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

#define SBR_BOUND 12

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
enum {
    CLAUSE_LOCK = 1,
};
struct clause {
    uint num_lit;
    double score;
    int flags;
    int lits[];
};
vector<uint> level;
vector<clause *> reason; // nullptr for decision
vector<bool> seen; // only used in `analyze`
vector<int> learnt; // only used in `analyze`
deque<clause *> db; // all clauses; first `db_num_persistent` clauses are persistent
uint db_num_persistent = 0;
uint db_limit = 0; // including persistent clauses
uint backoff_timer = 0;
uint backoff_limit = 0;

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
    if (c)
        c->flags |= CLAUSE_LOCK;
    trail.push_back(lit);
}
void pop() {
    int lit = trail.back();
    uint var = abs(lit);
    clause * c = reason[var];
    if (c)
        c->flags &= ~CLAUSE_LOCK;
    model[var] &= ~MODEL_DEFINED;
    trail.pop_back();
}

clause * make_clause(const vector<int> & lits, double score, int flags) {
    clause * c = reinterpret_cast<clause *>(malloc(sizeof(clause) + sizeof(int) * lits.size()));
    c->num_lit = lits.size();
    for (uint i = 0; i < lits.size(); ++i)
        c->lits[i] = lits[i];
    c->score = score;
    c->flags = flags;
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
    learnt.push_back(0); // reserve learnt[0] for UIP
    uint num_imp = 0;
    int lit = 0;
    uint i = trail.size() - 1;
    do {
        for (uint i = 0; i < conflict->num_lit; ++i) {
            int lit = conflict->lits[i];
            uint v = abs(lit);
            if (seen[v])
                continue;
            seen[v] = true;
            if (level[v] == decision_level) {
                ++num_imp;
            } else {
                learnt.push_back(lit);
            }
        }
        if (lit != 0)
            seen[abs(lit)] = false;
        do {
            lit = trail[i];
            --i;
        } while (! seen[abs(lit)]);
        --num_imp;
        conflict = reason[abs(lit)];
    } while (num_imp > 0);
    learnt[0] = -lit;
    for (auto lit : learnt)
        seen[abs(lit)] = false;
    uint max_lv = 0;
    for (uint i = 1; i < learnt.size(); ++i) {
        max_lv = max(level[abs(learnt[i])], max_lv);
    }
    uint num_lit = learnt.size();
    // learn new clause
    double score;
    if (num_lit < SBR_BOUND) {
        score = num_lit;
    } else {
        score = SBR_BOUND + rand() * (1 / ((double) RAND_MAX + 1));
    }
    auto c = make_clause(learnt, score, 0);
    if (num_lit == 2) {
        db.push_front(c);
        ++db_num_persistent;
    } else {
        db.push_back(c);
    }
    backjump(max_lv);
    push(-lit, c); // short-cut the next unit propagation
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

void reduce() {
    if (db.size() < db_limit)
        return;
    sort(db.begin() + db_num_persistent, db.end(), [](auto x, auto y) {
        return x->score < y->score;
    });
    uint new_size = db_num_persistent + (db.size() - db_num_persistent) / 2;
    for (uint i = new_size; i < db.size(); ++i) {
        if ((db[i]->flags & CLAUSE_LOCK) != 0) {
            db[new_size++] = db[i];
            continue;
        }
        free(db[i]);
    }
    db.resize(new_size);
}

bool solve() {
    srand(0);

    model.resize(N + 1);
    trail.reserve(2 * N);
    decision_level = 0;
    level.resize(N + 1);
    reason.resize(N + 1);
    seen.resize(N + 1);
    learnt.reserve(N);
    db_limit = F.size() * 1.5;
    backoff_limit = 100;

    for (auto & lits : F) {
        auto c = make_clause(lits, -1, 0);
        db.push_back(c);
        ++db_num_persistent;
    }

    while (1) {
        while (auto conflict = find_conflict()) {
            if (decision_level == 0)
                return false;
            analyze(*conflict);
            ++backoff_timer;
            if (backoff_timer >= backoff_limit) {
                backoff_timer = 0;
                backoff_limit *= 1.5;
                db_limit = db_num_persistent + (db_limit - db_num_persistent) * 1.1;
            }
        }
        if (! decide())
            return true;
        reduce();
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