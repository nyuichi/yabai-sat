#include <cstdio>
#include <cctype>
#include <string>
#include <vector>
#include <unordered_map>

using namespace std;

#define LEND (-1)
#define LVAR 0
#define LNEG 1
#define LAND 2
#define LOR 3
#define LIMP 4
#define LBIMP 5
#define LOPEN 6
#define LCLOSE 7

#define PREC(op) (10 - (op)) // ugly but sufficient

struct subf {
    int op;
    int arg[2];
};
vector<subf> subfs; // recursive descent parser automatically enumerates all subformulas

unordered_map<string, int> map;

[[noreturn]] void error(const char *str) {
    fputs(str, stderr);
    exit(1);
}

string name;
int next_token = LEND;

int get_token() {
    if (next_token != LEND) {
        int k = next_token;
        next_token = LEND;
        return k;
    }
    int c;
    do {
        c = getchar();
    } while (isspace(c));
    switch (c) {
    case EOF: return LEND;
    case '(': return LOPEN;
    case ')': return LCLOSE;
    case '~': return LNEG;
    case '&': return LAND;
    case '|': return LOR;
    case '-':
        if (getchar() != '>')
            error("unknown token");
        return LIMP;
    case '<':
        if (getchar() != '-')
            error("unknown token");
        if (getchar() != '>')
            error("unknown token");
        return LBIMP;
    default:
        if (isalpha(c) || c == '_') {
            name = "";
            do {
                name += c;
                c = getchar();
            } while (isalpha(c) || c == '_');
            ungetc(c, stdin);
            return LVAR;
        }
        error("unknown token");
    }
}

int peek_token() {
    if (next_token == LEND)
        next_token = get_token();
    return next_token;
}

int parse();

int parse_primary() {
    int k = get_token();
    if (k == LNEG) {
        k = parse_primary();
        subfs.push_back({ LNEG, k });
        return subfs.size() - 1;
    } else if (k == LVAR) {
        auto it = map.find(name);
        if (it != map.end()) {
            return it->second;
        }
        subfs.push_back({ LVAR });
        return map.insert({ move(name), subfs.size() - 1 }).first->second;
    } else if (k == LOPEN) {
        k = parse();
        if (get_token() != LCLOSE)
            error("unexpected ')'");
        return k;
    } else {
        error("syntax error");
    }
}

int parse_1(int lhs, int prec) {
    while (1) {
        int k = peek_token();
        if (! (k == LAND || (k == LOR && PREC(k) >= prec) || (k == LIMP && PREC(k) >= prec) || (k == LBIMP && PREC(k) > prec)))
            break;
        int op = k;
        get_token(); // consume
        int rhs = parse_primary();
        while (1) {
            k = peek_token();
            if (k == LBIMP && op == LBIMP)
                error("syntax error");
            if (! ((k == LAND && PREC(k) > PREC(op)) || (k == LOR && PREC(k) > PREC(op)) || (k == LIMP && PREC(k) == PREC(op))))
                break;
            rhs = parse_1(rhs, PREC(op));
        }
        subfs.push_back({ op, lhs, rhs });
        lhs = subfs.size() - 1;
    }
    return lhs;
}

int parse() {
    int k = parse_primary();
    return parse_1(k, 0);
}

// void print() {
//     for (int i = 1; i < subfs.size(); ++i) {
//         auto [op, arg] = subfs[i];
//         if (op == LVAR)
//             continue;
//         int p = arg[0], q = arg[1];
//         switch (op) {
//         case LNEG: fprintf(stderr, "%d <-> ~%d\n", i, p); break;
//         case LAND: fprintf(stderr, "%d <-> %d & %d\n", i, p, q); break;
//         case LOR: fprintf(stderr, "%d <-> %d | %d\n", i, p, q); break;
//         case LIMP: fprintf(stderr, "%d <-> %d -> %d\n", i, p, q); break;
//         case LBIMP: fprintf(stderr, "%d <-> (%d <-> %d)\n", i, p, q); break;
//         }
//     }
// }

int main() {
    subfs.push_back({}); // avoid 0
    int k = parse();

    // Tseitin transformation
    vector<vector<int>> db;
    for (int i = 1; i < subfs.size(); ++i) {
        auto [op, arg] = subfs[i];
        if (op == LVAR)
            continue;
        int r = i, p = arg[0], q = arg[1];
        switch (op) {
        case LNEG: // r<->~p = r->~p & ~p->r = ~r|~p & p|r
            db.push_back({ r, p });
            db.push_back({ -r, -p });
            break;
        case LIMP: // r<->p->q = r->~p|q
            p = -p;
            [[fallthrough]];
        case LOR: // r<->p|q = ~r<->~p&~q
            r = -r;
            p = -p;
            q = -q;
            [[fallthrough]];
        case LAND: // r<->p&q = r->p&q & p&q->r = ~r|p&q & ~p|~q|r = ~r|p & ~r|q & ~p|~q|r
            db.push_back({ -r, p });
            db.push_back({ -r, q });
            db.push_back({ r, -p, -q });
            break;
        case LBIMP: // r<->(p<->q) = r->(p<->q) & (p<->q)->r = ~r|((p|~q)&(~p|q)) & ~((p&q)|(~p&~q))|r
            db.push_back({ -r, p, -q });
            db.push_back({ -r, -p, q });
            db.push_back({ r, -p, -q });
            db.push_back({ r, p, q });
            break;
        }
    }
    db.push_back({ k });

    printf("p cnf %lu %lu\n", subfs.size() - 1, db.size());
    for (auto & clause : db) {
        for (auto lit : clause)
            printf("%d ", lit);
        printf("0\n");
    }
}