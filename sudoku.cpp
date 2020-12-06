#include <cstdio>
#include <vector>
extern "C" {
#include <unistd.h>
}

#define SOLVER "./sat_opt"

using namespace std;

FILE *to_solver, *from_solver;

void spawn_solver() {
    int to_child[2], from_child[2]; 
    if (pipe(to_child) < 0)
        perror("pipe1");
    if (pipe(from_child) < 0)
        perror("pipe2");
    pid_t pid;
    if ((pid = vfork()) < 0)
        perror("vfork");
    if (pid == 0) { // in solver
        close(to_child[1]);
        close(from_child[0]);
        dup2(to_child[0], 0);
        dup2(from_child[1], 1);
        close(to_child[0]);
        close(from_child[1]);
        if (execl(SOLVER, SOLVER, NULL) < 0)
            perror("execl");
    }
    close(to_child[0]);
    close(from_child[1]);
    to_solver = fdopen(to_child[1], "w");
    from_solver = fdopen(from_child[0], "r");
}

int p(int i, int j, int n) { return (i*81 + j*9 + n) + 1; }

void solve() {
    int b[9][9];

    // read initial states
    for (int i = 0; i < 9; ++i) {
        for (int j = 0; j < 9; ++j) {
            char c;
            scanf(" %c", &c);
            b[i][j] = c - '0';
        }
    }

    // construct cnf
    vector<vector<int>> db;
    for (int i = 0; i < 9; ++i) {
        for (int j = 0; j < 9; ++j) {
            if (b[i][j] != 0)
                db.push_back({ p(i,j,b[i][j] - 1) });
        }
    }
    for (int i = 0; i < 9; ++i) {
        for (int j = 0; j < 9; ++j) {
            vector<int> c;
            for (int n = 0; n < 9; ++n)
                c.push_back(p(i,j,n));
            db.push_back(move(c));
        }
    }
    for (int i = 0; i < 9; ++i) {
        for (int j = 0; j < 9; ++j) {
            for (int x = 0; x < 8; ++x) {
                for (int y = x + 1; y < 9; ++y) {
                    vector<int> c;
                    c.push_back(-p(i,j,x));
                    c.push_back(-p(i,j,y));
                    db.push_back(move(c));
                }
            }
        }
    }
    for (int i = 0; i < 9; ++i) {
        for (int n = 0; n < 9; ++n) {
            vector<int> c;
            for (int j = 0; j < 9; ++j)
                c.push_back(p(i,j,n));
            db.push_back(move(c));
        }
    }
    for (int j = 0; j < 9; ++j) {
        for (int n = 0; n < 9; ++n) {
            vector<int> c;
            for (int i = 0; i < 9; ++i)
                c.push_back(p(i,j,n));
            db.push_back(move(c));
        }
    }
    for (int r = 0; r < 3; ++r) {
        for (int s = 0; s < 3; ++s) {
            for (int n = 0; n < 9; ++n) {
                vector<int> c;
                for (int i = 0; i < 3; ++i)
                    for (int j = 0; j < 3; ++j)
                        c.push_back(p(3*r+i,3*s+j,n));
                db.push_back(move(c));
            }
        }
    }

    // send cnf to solver
    fprintf(to_solver, "p cnf %d %lu\n", 9*9*9, db.size());
    for (auto & c : db) {
        for (auto lit : c) {
            fprintf(to_solver, "%d ", lit);
        }
        fprintf(to_solver, "0\n");
    }
    fflush(to_solver);

    // receive answer from solver
    fscanf(from_solver, "s SATISFIABLE v ");
    while (1) {
        int p;
        fscanf(from_solver, "%d", &p);
        if (p == 0)
            break;
        if (p < 0)
            continue;
        --p;
        int i = p / 81;
        int j = (p % 81) / 9;
        int n = p % 9;
        b[i][j] = n + 1;
    }

    for (int i = 0; i < 9; ++i) {
        for (int j = 0; j < 9; ++j) {
            printf("%d", b[i][j]);
        }
        printf("\n");
    }
}

int main() {
    spawn_solver();
    solve();
}
