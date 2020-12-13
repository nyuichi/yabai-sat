#include <algorithm>
#include <cassert>
#include <cstdio>
#include <vector>
extern "C" {
#include <unistd.h>
}

using namespace std;

bool opt_quiet = false;
FILE * opt_cert_file = NULL;

typedef unsigned uint;
typedef unsigned char uchar;

uint N; // number of variables
uint M; // number of initial clauses
vector<vector<int>> F; // problem

enum {
    MODEL_DEFINED = 1,
    MODEL_PHASE = 2,
};
vector<uchar> model;
vector<int> trail; // 0 for decision mark
uint decision_level;

bool defined(uint var) {
    return (model[var] & MODEL_DEFINED) != 0;
}
bool phase(uint var) {
    return (model[var] & MODEL_PHASE) != 0;
}
int ev(uint var) {
    return ! defined(var) ? 0 : phase(var) ? (int) var : -(int) var;
}

void push(int lit) {
    uint var = abs(lit);
    model[var] = lit > 0 ? MODEL_DEFINED | MODEL_PHASE : MODEL_DEFINED;
    trail.push_back(lit);
}
int pop() {
    int lit = trail.back();
    uint var = abs(lit);
    model[var] &= ~MODEL_DEFINED;
    trail.pop_back();
    return lit;
}

void backtrack() {
    int lit = 0;
    for (uint i = trail.size() - 1; trail[i] != 0; --i)
        lit = pop();
    trail.pop_back(); // remove the mark
    --decision_level;
    push(-lit); // flip the decision
}

bool find_conflict() {
    bool retry;
    do {
        retry = false;
        for (auto & c : F) {
            int num_undef = 0;
            int undef_lit;
            for (auto lit : c) {
                if (! defined(abs(lit))) {
                    ++num_undef;
                    undef_lit = lit;
                } else if (ev(abs(lit)) == lit) {
                    goto next;
                }
            }
            if (num_undef == 0)
                return true; // conflict found
            if (num_undef == 1) {
                push(undef_lit);
                retry = true;
            }
        next:;
        }
    } while (retry);
    return false; // no conflict found
}

int choose() {
    for (uint v = 1; v <= N; ++v) {
        if (! defined(v))
            return (int) v;
    }
    return 0;
}

int decide() {
    int lit;
    if ((lit = choose()) == 0)
        return false; // sat
    trail.push_back(0); // push mark
    ++decision_level;
    push(lit);
    return true;
}

bool solve() {
    model.resize(N + 1);
    trail.reserve(2 * N);
    decision_level = 0;

    while (1) {
        while (find_conflict()) {
            if (decision_level == 0)
                return false;
            backtrack();
        }
        if (! decide())
            return true;
    }
}

void check_model() {
    for (auto & lits : F) {
        bool found = false;
        for (int lit : lits) {
            if (ev(abs(lit)) == lit) {
                found = true;
                break;
            }
        }
        if (! found) {
            fputs("model broken!\n", stderr);
            exit(2);
        }
    }
}

void usage() {
    fputs("Usage: sat [options] [input-file] [output-file]\n", stderr);
    fputs("\n", stderr);
    fputs("Options:\n", stderr);
    fputs("\n", stderr);
    fputs("  -q                Do not print results to stdout\n", stderr);
    fputs("  -C <DRUP_FILE>    Output certificates for unsatisfiable formulas\n", stderr);
    fputs("  -h                Show this message\n", stderr);
    fputs("\n", stderr);
    exit(1);
}

int main(int argc, char * argv[]) {
    int c;
    while ((c = getopt(argc, argv, "qC:")) != -1) {
        switch (c) {
        case 'q':
            opt_quiet = true;
            break;
        case 'C':
            opt_cert_file = fopen(optarg, "w");
            if (! opt_cert_file)
                perror("could not open certificate file");
            break;
        default:
            usage();
        }
    }
    argc -= optind;
    argv += optind;
    if (argc > 2)
        usage();
    if (argc > 0) {
        if (freopen(argv[0], "r", stdin) == NULL) {
            perror("could not open input file");
            exit(1);
        }
    }
    if (argc > 1) {
        if (opt_quiet)
            usage();
        if (freopen(argv[1], "w", stdout) == NULL) {
            perror("could not open output file");
            exit(1);
        }
    }

    // read cnf
    while (getchar() == 'c') {
        while (getchar() != '\n')
            ;
    }
    scanf(" cnf %d %d", &N, &M);
    F.resize(M);
    for (auto & c : F) {
        int lit;
        while (scanf("%d", &lit), lit != 0) {
            c.push_back(lit);
        }
    }

    bool sat = solve();

    // follow sat competition's output format
    if (! sat) {
        if (opt_cert_file)
            fputs("0\n", opt_cert_file);
        if (! opt_quiet)
            puts("s UNSATISFIABLE");
        return 20;
    }
    check_model();
    if (! opt_quiet) {
        puts("s SATISFIABLE");
        printf("v ");
        for (uint v = 1; v <= N; ++v) {
            if (defined(v))
                printf("%d ", ev(v));
        }
        puts("0");
    }
    return 10;
}