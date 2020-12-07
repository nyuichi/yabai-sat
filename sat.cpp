#include <algorithm>
#include <cassert>
#include <cstdio>
#include <deque>
#include <optional>
#include <queue>
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
struct clause {
    uint num_lit;
    int lits[];
};
vector<uint> level;
vector<clause *> reason; // nullptr for decision
vector<bool> seen; // only used in `analyze`
queue<int> q; // literal pool for conflict analysis; only used in `analyze`
vector<int> learnt; // only used in `analyze`
deque<clause *> db; // all clauses

bool defined(uint var) {
    return (model[var] & MODEL_DEFINED) != 0;
}
bool phase(uint var) {
    return (model[var] & MODEL_PHASE) != 0;
}
int ev(uint var) {
    return ! defined(var) ? 0 : phase(var) ? (int) var : -(int) var;
}

void push(int lit, clause * c) {
    uint var = abs(lit);
    model[var] = lit > 0 ? MODEL_DEFINED | MODEL_PHASE : MODEL_DEFINED;
    level[var] = decision_level;
    reason[var] = c;
    trail.push_back(lit);
}
void pop() {
    int lit = trail.back();
    uint var = abs(lit);
    model[var] &= ~MODEL_DEFINED;
    seen[var] = false;
    trail.pop_back();
}

clause * make_clause(const vector<int> & lits) {
    clause * c = reinterpret_cast<clause *>(malloc(sizeof(clause) + sizeof(int) * lits.size()));
    c->num_lit = lits.size();
    for (uint i = 0; i < lits.size(); ++i)
        c->lits[i] = lits[i];
    return c;
}

void backjump(uint level) {
    while (decision_level != level) {
        for (uint i = trail.size() - 1; trail[i] != 0; --i)
            pop();
        trail.pop_back(); // remove the mark
        --decision_level;
    }
}

void analyze(clause * conflict) {
    for (uint i = 0; i < conflict->num_lit; ++i) {
        int lit = conflict->lits[i];
        if (level[abs(lit)] == decision_level) {
            q.push(lit);
        } else {
            learnt.push_back(lit);
        }
        seen[abs(lit)] = true;
    }
    int uip = 0;
    while (! q.empty()) {
        auto lit = q.front();
        q.pop();
        if (uip == 0 && q.empty()) {
            uip = lit;
            learnt.push_back(lit);
            break;
        }
        auto c = reason[abs(lit)];
        if (! c) {
            uip = lit;
            learnt.push_back(lit);
            seen[abs(lit)] = true;
            continue;
        }
        for (uint i = 0; i < c->num_lit; ++i) {
            int lit = c->lits[i];
            uint v = abs(lit);
            if (seen[v])
                continue;
            seen[v] = true;
            if (level[v] == decision_level) {
                q.push(lit);
            } else {
                learnt.push_back(lit);
            }
        }
    }
    for (auto lit : learnt)
        seen[abs(lit)] = false;
    uint max_lv = 0;
    for (auto lit : learnt) {
        if (level[abs(lit)] != decision_level)
            max_lv = max(level[abs(lit)], max_lv);
    }
    auto c = make_clause(learnt);
    db.push_back(c);
    backjump(max_lv);
    push(uip, c); // short-cut the next unit propagation
    learnt.clear();
}

optional<clause *> find_conflict() {
    bool retry;
    do {
        retry = false;
        for (auto c : db) {
            int num_undef = 0;
            int undef_lit;
            for (uint i = 0; i < c->num_lit; ++i) {
                int lit = c->lits[i];
                if (! defined(abs(lit))) {
                    ++num_undef;
                    undef_lit = lit;
                } else if (ev(abs(lit)) == lit) {
                    goto next;
                }
            }
            if (num_undef == 0)
                return c; // conflict found
            if (num_undef == 1) {
                push(undef_lit, c);
                retry = true;
            }
        next:;
        }
    } while (retry);
    return nullopt; // no conflict found
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
    push(lit, nullptr);
    return true;
}

bool solve() {
    model.resize(N + 1);
    trail.reserve(2 * N);
    decision_level = 0;
    level.resize(N + 1);
    reason.resize(N + 1);
    seen.resize(N + 1);
    learnt.reserve(N);

    for (auto & lits : F) {
        auto c = make_clause(lits);
        db.push_back(c);
    }

    while (1) {
        while (auto conflict = find_conflict()) {
            if (decision_level == 0)
                return false;
            analyze(*conflict);
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