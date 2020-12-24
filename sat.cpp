#include <algorithm>
#include <cassert>
#include <cstdio>
#include <optional>
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
enum {
    CLAUSE_LEARNT = 1,
};
struct clause {
    uint num_lit;
    int flags;
    int lits[]; // lits[0] and lits[1] are watched literals
};
vector<vector<clause *>> pos_list, neg_list; // watch lists
vector<uint> level;
vector<clause *> reason; // nullptr for decision
vector<bool> seen; // only used in `analyze`
vector<int> learnt; // only used in `analyze`

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
    trail.pop_back();
}

clause * make_clause(const vector<int> & lits, int flags) {
    clause * c = reinterpret_cast<clause *>(malloc(sizeof(clause) + sizeof(int) * lits.size()));
    c->num_lit = lits.size();
    for (uint i = 0; i < lits.size(); ++i)
        c->lits[i] = lits[i];
    c->flags = flags;
    return c;
}

auto & watch_list(int lit) {
    return lit > 0 ? pos_list[lit] : neg_list[-lit];
}
void watch_clause(clause * c) {
    for (auto i : { 0, 1 }) {
        watch_list(c->lits[i]).push_back(c);
    }
}
void unwatch_clause(clause * c) {
    for (auto i : { 0, 1 }) {
        auto & wlist = watch_list(c->lits[i]);
        for (auto & wc : wlist) {
            if (wc == c) {
                wc = wlist.back();
                wlist.pop_back();
                break;
            }
        }
    }
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
    uint count = 0;
    for (uint i = 0; i < conflict->num_lit; ++i) {
        int lit = conflict->lits[i];
        uint v = abs(lit);
        seen[v] = true;
        if (level[v] < decision_level) {
            learnt.push_back(lit);
        } else {
            ++count;
        }
    }
    int uip;
    for (uint i = trail.size() - 1; true; --i) {
        int lit = trail[i];
        uint v = abs(lit);
        if (! seen[v])
            continue;
        seen[v] = false;
        --count;
        if (count == 0) {
            uip = lit;
            break;
        }
        auto c = reason[v];
        for (uint i = 1; i < c->num_lit; ++i) {
            int lit = c->lits[i];
            uint v = abs(lit);
            if (seen[v])
                continue;
            seen[v] = true;
            if (level[v] < decision_level) {
                learnt.push_back(lit);
            } else {
                ++count;
            }
        }
    }
    learnt[0] = -uip;
    uint num_lit = learnt.size();
    for (uint i = 1; i < num_lit; ++i)
        seen[abs(learnt[i])] = false;
    uint max_lv = 0;
    for (uint i = 1; i < num_lit; ++i) {
        uint lv = level[abs(learnt[i])];
        if (lv > max_lv) {
            max_lv = lv;
            swap(learnt[1], learnt[i]);
        }
    }
    backjump(max_lv);
    if (num_lit == 1) {
        push(-uip, nullptr);
        learnt.clear();
        return;
    }
    auto c = make_clause(learnt, CLAUSE_LEARNT);
    push(-uip, c);
    learnt.clear();
    watch_clause(c);
}

optional<clause *> find_conflict() {
    for (uint prop = trail.size() - 1; prop < trail.size(); ++prop) {
        int lit = trail[prop];
        auto & wlist = watch_list(-lit);
        for (uint i = 0; i < wlist.size(); ++i) {
            auto c = wlist[i];
            if (c->lits[0] == -lit)
                swap(c->lits[0], c->lits[1]);
            int lit = c->lits[0];
            if (ev(abs(lit)) == lit) // satisfied
                continue;
            for (uint k = 2; k < c->num_lit; ++k) {
                int lit = c->lits[k];
                if (ev(abs(lit)) != -lit) { // update watch list
                    watch_list(lit).push_back(c);
                    swap(c->lits[1], c->lits[k]);
                    wlist[i] = wlist.back();
                    wlist.pop_back();
                    --i;
                    goto next;
                }
            }
            if (defined(abs(lit)))
                return c; // conflict found
            push(lit, c);
        next:;
        }
    }
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
    pos_list.resize(N + 1);
    neg_list.resize(N + 1);
    level.resize(N + 1);
    reason.resize(N + 1);
    seen.resize(N + 1);
    learnt.reserve(N);

    vector<int> unit;
    vector<int> new_lits;
    for (auto & lits : F) {
        size_t size = lits.size();
        if (size == 0)
            return false; // unsat
        if (size == 1) {
            unit.push_back(lits[0]);
            continue;
        }
        for (uint i = 0; i < lits.size(); ++i) {
            bool last = true;
            for (uint j = i + 1; j < lits.size(); ++j) {
                if (lits[i] == -lits[j]) // tautology found
                    goto next;
                if (lits[i] == lits[j]) {
                    last = false;
                    break;
                }
            }
            if (last)
                new_lits.push_back(lits[i]);
        }
        watch_clause(make_clause(new_lits, 0));
    next:
        new_lits.clear();
    }

    while (! unit.empty()) {
        int lit = unit.back();
        unit.pop_back();
        push(lit, nullptr);
        if (find_conflict())
            return false;
    }
    if (trail.empty()) {
        if (! decide())
            return true;
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
