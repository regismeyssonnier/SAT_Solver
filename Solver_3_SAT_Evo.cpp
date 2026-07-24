#pragma comment(linker, "/LARGEADDRESSAWARE")
// ============================================================
// OPTIMISATIONS ABSOLUES
// ============================================================

// Pour GCC/MinGW
#if defined(__GNUC__) || defined(__MINGW32__) || defined(__MINGW64__)
#pragma GCC optimize("O3")
#pragma GCC optimize("Ofast")
#pragma GCC optimize("unroll-loops")
#pragma GCC optimize("inline-functions")
#pragma GCC optimize("omit-frame-pointer")
#pragma GCC optimize("tree-vectorize")
#pragma GCC optimize("fast-math")
#pragma GCC optimize("no-stack-protector")
#pragma GCC optimize("fuse-linker-optimizations")
#pragma GCC optimize("funroll-loops")
#pragma GCC optimize("no-signed-zeros")
#pragma GCC optimize("no-trapping-math")
#pragma GCC target("native")
#pragma GCC diagnostic ignored "-Wunknown-pragmas"
#endif

// Pour MSVC
#if defined(_MSC_VER)
#pragma optimize("gt", on)
#pragma optimize("s", on)
#pragma optimize("y", on)
#pragma inline_recursion(on)
#pragma inline_depth(255)
#pragma runtime_checks("", off)
#endif

// Précharge les données en cache
#ifdef __linux__
#pragma GCC push_options
#pragma GCC optimize("prefetch-loop-arrays")
#pragma GCC pop_options
#endif

#include <iostream>
#include <vector>
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <ctime>
#include <fstream>
#include <string>
#include <set>
#include <queue>
#include <cstdint>
#include <chrono>

using namespace std;

// ============================================================
// DEBUG
// ============================================================

#define DEBUG 0  // Mettre à 1 pour activer les logs

#if DEBUG
#define LOG(x) cout << x << endl
#define LOGVAR(x) cout << #x << "=" << x << endl
#else
#define LOG(x)
#define LOGVAR(x)
#endif

// ============================================================
// CLAUSE
// ============================================================

class Clause {
public:
    vector<int> lits;
    bool learnt;
    double activity;
    bool deleted;

    Clause() : learnt(false), activity(0.0), deleted(false) {}
    Clause(const vector<int>& l, bool lr = false) : lits(l), learnt(lr), activity(0.0), deleted(false) {}

    int size() const { return (int)lits.size(); }

    void print() const {
        cout << "(";
        for (int i = 0; i < (int)lits.size(); i++) {
            int lit = lits[i];
            if (lit > 0) cout << "x" << lit;
            else cout << "nx" << -lit;
            if (i < (int)lits.size() - 1) cout << " v ";
        }
        cout << ")";
        if (learnt) cout << " [apprise]";
        cout << endl;
    }

    bool isSatisfied(const vector<int8_t>& assign) const {
        for (int lit : lits) {
            int var = abs(lit);
            if (var < 1 || var >= (int)assign.size()) continue;
            bool sign = (lit > 0);
            if (assign[var] != -1 && (assign[var] == 1) == sign) {
                return true;
            }
        }
        return false;
    }

    bool isFalse(const vector<int8_t>& assign) const {
        for (int lit : lits) {
            int var = abs(lit);
            if (var < 1 || var >= (int)assign.size()) return false;
            bool sign = (lit > 0);
            if (assign[var] == -1) return false;
            if ((assign[var] == 1) == sign) return false;
        }
        return true;
    }

    bool getUnit(int& unitVar, bool& unitSign, const vector<int8_t>& assign) const {
        int undefCount = 0;
        int lastVar = -1;
        bool lastSign = false;

        for (int lit : lits) {
            int v = abs(lit);
            if (v < 1 || v >= (int)assign.size()) continue;
            bool s = (lit > 0);
            if (assign[v] == -1) {
                undefCount++;
                lastVar = v;
                lastSign = s;
            }
            else if ((assign[v] == 1) == s) {
                return false;
            }
        }

        if (undefCount == 1) {
            unitVar = lastVar;
            unitSign = lastSign;
            return true;
        }
        return false;
    }
};

// ============================================================
// WATCHER
// ============================================================
struct Watcher {
    int clause;
    int blocker;

    Watcher() : clause(-1), blocker(-1) {}
    Watcher(int c, int b) : clause(c), blocker(b) {}

    // ✅ Ajouter l'opérateur de comparaison
    bool operator==(const Watcher& other) const {
        return clause == other.clause && blocker == other.blocker;
    }
};

// ============================================================
// SOLVEUR CDCL
// ============================================================

class SolverCDCL {
private:
    // Clauses
    vector<Clause> clauses;
    vector<Clause> learntClauses;

    // Assignations
    vector<int8_t> assignment;
    vector<int> level;
    vector<int> reason;
    vector<uint8_t> seen;

    // Trail
    vector<int> trail;
    vector<int> trail_lim;
    int qhead;

    // Watch lists
    vector<vector<Watcher>> watches;

    // VSIDS
    vector<double> activity;
    priority_queue<pair<double, int>> order_heap;

    // Statistiques
    int nextVar;
    int decisionLevel;
    int decisions;
    int propagations;
    int conflicts;
    int restartLimit;
    int conflictCount;
    double var_decay;
    double var_inc;
    double restartFactor;
    bool satisfiable;
    int propagationCount;

    vector<uint8_t> clauseSat;  // ← Ajouter ce cache

public:
    SolverCDCL() : nextVar(1), decisionLevel(0), decisions(0),
        propagations(0), conflicts(0), satisfiable(false),
        qhead(0), var_decay(0.95), var_inc(1.0),
        restartLimit(50), conflictCount(0), restartFactor(1.2), propagationCount(0){
        assignment.resize(1, -1);
        level.resize(1, -1);
        reason.resize(1, -1);
        seen.resize(1, 0);
        activity.resize(1, 0.0);
        watches.resize(1);

        clauseSat.resize(1, 0);  // ← Initialiser

        clauses.reserve(100000000);      // 100M clauses
        learntClauses.reserve(10000);    // 10k clauses apprises
        watches.reserve(130000);         // 130k variables
    }

    // ============================================================
    // GESTION DES VARIABLES
    // ============================================================

    int getMaxVar() { return nextVar - 1; }

    int getNextVar() {
        int var = nextVar++;
        int size = var + 1;
        if ((int)assignment.size() <= size) {
            assignment.resize(size, -1);
            level.resize(size, -1);
            reason.resize(size, -1);
            seen.resize(size, 0);
            activity.resize(size, 0.0);
            watches.resize(size);
        }
        LOG("new var x" << var);
        return var;
    }

    void ensureVar(int var) {
        int size = var + 1;
        if ((int)assignment.size() <= size) {
            assignment.resize(size, -1);
            level.resize(size, -1);
            reason.resize(size, -1);
            seen.resize(size, 0);
            activity.resize(size, 0.0);
            watches.resize(size);
        }
        if (var >= nextVar) nextVar = var + 1;
    }

    vector<Clause> getClauses() { return this->clauses; }

    // ============================================================
    // AJOUT DE CLAUSES
    // ============================================================

    void addClause(vector<int> lits) {
        LOG("addClause: ");
#if DEBUG
        for (int l : lits) cout << l << " ";
        cout << endl;
#endif

        for (int lit : lits) {
            int var = abs(lit);
            ensureVar(var);
        }

        Clause c(std::move(lits), false);
        int idx = clauses.size();
        clauses.push_back(c);
        clauseSat.push_back(0);  // ← Ajouter pour la nouvelle clause

        if (lits.size() == 1) {
            // Clause unitaire : assigner immédiatement
            int lit = lits[0];
            int var = abs(lit);
            bool sign = (lit > 0);
            if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                assignment[var] = sign ? 1 : 0;
                level[var] = 0;
                reason[var] = idx;
                trail.push_back(var);
            }
            return;
        }

        // Chercher deux variables distinctes pour les watchers
        int v1 = -1, v2 = -1;
        for (int lit : lits) {
            int v = abs(lit);
            if (v1 == -1) v1 = v;
            else if (v != v1 && v2 == -1) v2 = v;
        }

        if (v2 == -1) {
            // Tous les littéraux sont sur la même variable (clause unitaire déguisée)
            // Assigner immédiatement
            int lit = lits[0];
            int var = abs(lit);
            bool sign = (lit > 0);
            if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                assignment[var] = sign ? 1 : 0;
                level[var] = 0;
                reason[var] = idx;
                trail.push_back(var);
            }
            return;
        }

        if (v1 >= 1 && v1 < (int)watches.size()) {
            watches[v1].push_back(Watcher(idx, v2));
        }
        if (v2 >= 1 && v2 < (int)watches.size()) {
            watches[v2].push_back(Watcher(idx, v1));
        }
        LOG("  watch x" << v1 << " <-> x" << v2);
    }

    void addClause(int a, int b, int c) {
        vector<int> lits = { a, b, c };
        addClause(lits);
    }

    void addClause(int a, int b) {
        vector<int> lits = { a, b };
        addClause(lits);
    }

    void addClause(int a) {
        vector<int> lits = { a };
        addClause(lits);
    }

    // ============================================================
    // Add1Sat à AddAddBin
    // ============================================================

    void addBinaryClause(int a, int b, int signA, int signB) {
        // sign=1 signifie que le littéral est positif (x), sign=0 signifie négatif (¬x)
        // La clause est (littéralA v littéralB)
        // Si signA=1, littéralA = a, sinon littéralA = -a
        addClause({ signA == 1 ? a : -a, signB == 1 ? b : -b });
    }

    void o2o2oAdd1Sat(int idxa, int sidxa) {
        vector<int> l;
        if (sidxa == 1) l = { idxa , idxa, idxa };
        else l = { -idxa , -idxa, -idxa };

        addClause(l);
    }

    void Add1Sat(int idxa, int sidxa) {
        if (sidxa == 1) {
            addClause({ idxa });      // ← (x) au lieu de (x v x v x)
        }
        else {
            addClause({ -idxa });     // ← (¬x) au lieu de (¬x v ¬x v ¬x)
        }
    }

    void oooAdd1Sat(int idxa, int sidxa) {
        int z1 = getNextVar();
        int z2 = getNextVar();

        if (sidxa == 1) {
            // Forcer idxa = VRAI
            // (idxa v z1 v z2) ∧ (idxa v ¬z1 v z2) ∧ (idxa v z1 v ¬z2) ∧ (idxa v ¬z1 v ¬z2)
            addClause({ idxa,  z1,  z2 });
            addClause({ idxa, -z1,  z2 });
            addClause({ idxa,  z1, -z2 });
            addClause({ idxa, -z1, -z2 });
        }
        else {
            // Forcer idxa = FAUX
            // (¬idxa v z1 v z2) ∧ (¬idxa v ¬z1 v z2) ∧ (¬idxa v z1 v ¬z2) ∧ (¬idxa v ¬z1 v ¬z2)
            addClause({ -idxa,  z1,  z2 });
            addClause({ -idxa, -z1,  z2 });
            addClause({ -idxa,  z1, -z2 });
            addClause({ -idxa, -z1, -z2 });
        }
    }

    void oooAdd2Sat(int idxa, int idxb, int sidxa, int sidxb) {
        int z = getNextVar();
        vector<int> l1 = { (sidxa == 1) ? idxa : -idxa, (sidxb == 1) ? idxb : -idxb, z };
        vector<int> l2 = { (sidxa == 1) ? idxa : -idxa, (sidxb == 1) ? idxb : -idxb, -z };
        addClause(l1);
        addClause(l2);
    }

    void Add2Sat(int idxa, int idxb, int sidxa, int sidxb) {
        // (littéralA v littéralB)
        addClause({
            (sidxa == 1) ? idxa : -idxa,
            (sidxb == 1) ? idxb : -idxb
            });
    }

    void Add3Sat(int idxa, int idxb, int idxc, int sidxa, int sidxb, int sidxc) {
        vector<int> lits = {
            (sidxa == 1) ? idxa : -idxa,
            (sidxb == 1) ? idxb : -idxb,
            (sidxc == 1) ? idxc : -idxc
        };
        addClause(lits);
    }

    void Add4Sat(int idxa, int idxb, int idxc, int idxd,
        int sidxa, int sidxb, int sidxc, int sidxd) {
        int z = getNextVar();
        vector<int> l1 = {
            (sidxa == 1) ? idxa : -idxa,
            (sidxb == 1) ? idxb : -idxb,
            z
        };
        vector<int> l2 = { -z, (sidxc == 1) ? idxc : -idxc, (sidxd == 1) ? idxd : -idxd };
        addClause(l1);
        addClause(l2);
    }

    void oooAddKSat(int* vars, int* signs, int k) {
        if (k == 1) { Add1Sat(vars[0], signs[0]); return; }
        if (k == 2) { Add2Sat(vars[0], vars[1], signs[0], signs[1]); return; }
        if (k == 3) { Add3Sat(vars[0], vars[1], vars[2], signs[0], signs[1], signs[2]); return; }

        int z_prev = -1;
        int z1 = getNextVar();
        vector<int> l1 = {
            (signs[0] == 1) ? vars[0] : -vars[0],
            (signs[1] == 1) ? vars[1] : -vars[1],
            z1
        };
        addClause(l1);
        z_prev = z1;

        for (int i = 2; i < k - 2; i += 1) {
            int z_next = getNextVar();
            vector<int> l = { -z_prev, (signs[i] == 1) ? vars[i] : -vars[i], z_next };
            addClause(l);
            z_prev = z_next;
        }

        vector<int> last = {
            -z_prev,
            (signs[k - 2] == 1) ? vars[k - 2] : -vars[k - 2],
            (signs[k - 1] == 1) ? vars[k - 1] : -vars[k - 1]
        };
        addClause(last);
    }

    //chat gpt
    void AddKSat(int* vars, int* signs, int k) {
        if (k == 1) {
            Add1Sat(vars[0], signs[0]);
            return;
        }

        if (k == 2) {
            Add2Sat(vars[0], vars[1], signs[0], signs[1]);
            return;
        }

        if (k == 3) {
            Add3Sat(vars[0], vars[1], vars[2],
                signs[0], signs[1], signs[2]);
            return;
        }

        if (k == 4) {
            Add4Sat(vars[0], vars[1], vars[2], vars[3],
                signs[0], signs[1], signs[2], signs[3]);
            return;
        }

        int z_prev = getNextVar();

        // (x0 ∨ x1 ∨ z1)
        addClause({
            (signs[0] == 1) ? vars[0] : -vars[0],
            (signs[1] == 1) ? vars[1] : -vars[1],
            z_prev
            });

        for (int i = 2; i < k - 2; i++) {
            int z_next = getNextVar();

            // (¬z_prev ∨ xi ∨ z_next)
            addClause({
                -z_prev,
                (signs[i] == 1) ? vars[i] : -vars[i],
                z_next
                });

            z_prev = z_next;
        }

        // (¬z_prev ∨ x[k-2] ∨ x[k-1])
        addClause({
            -z_prev,
            (signs[k - 2] == 1) ? vars[k - 2] : -vars[k - 2],
            (signs[k - 1] == 1) ? vars[k - 1] : -vars[k - 1]
            });
    }

    void AddKSatGOOD(int* vars, int* signs, int k) {
        if (k == 1) {
            Add1Sat(vars[0], signs[0]);
            return;
        }
        if (k == 2) {
            Add2Sat(vars[0], vars[1], signs[0], signs[1]);
            return;
        }
        if (k == 3) {
            Add3Sat(vars[0], vars[1], vars[2], signs[0], signs[1], signs[2]);
            return;
        }

        if (k == 4) { Add4Sat(vars[0], vars[1], vars[2], vars[3], signs[0], signs[1], signs[2], signs[3]); return; }


        // Pour k > 3, utiliser un schéma séquentiel
        int z_prev = -1;
        int z1 = getNextVar();
        vector<int> l1 = {
            (signs[0] == 1) ? vars[0] : -vars[0],
            (signs[1] == 1) ? vars[1] : -vars[1],
            z1
        };
        addClause(l1);
        z_prev = z1;

        for (int i = 2; i < k - 2; i += 1) {
            int z_next = getNextVar();
            vector<int> l = { -z_prev, (signs[i] == 1) ? vars[i] : -vars[i], z_next };
            addClause(l);
            z_prev = z_next;
        }

        // Dernière clause
        vector<int> last = {
            -z_prev,
            (signs[k - 2] == 1) ? vars[k - 2] : -vars[k - 2],
            (signs[k - 1] == 1) ? vars[k - 1] : -vars[k - 1]
        };
        addClause(last);
    }

    void AddKSatREC(int* vars, int* signs, int k) {
        if (k == 1) { Add1Sat(vars[0], signs[0]); return; }
        if (k == 2) { Add2Sat(vars[0], vars[1], signs[0], signs[1]); return; }
        if (k == 3) { Add3Sat(vars[0], vars[1], vars[2], signs[0], signs[1], signs[2]); return; }
        if (k == 4) { Add4Sat(vars[0], vars[1], vars[2], vars[3],  signs[0], signs[1], signs[2], signs[3]); return; }
        // ✅ Utiliser une approche récursive pour k >= 4
        // (vars[0] v vars[1] v ... v vars[k-1]) 
        // = (vars[0] v vars[1] v z) ∧ (¬z v vars[2] v ... v vars[k-1])
        int z = getNextVar();

        // vars[0] v vars[1] v z
        addClause({ (signs[0] ? vars[0] : -vars[0]),
                    (signs[1] ? vars[1] : -vars[1]),
                    z });

        // ¬z v vars[2] v ... v vars[k-1]
        int* remaining = new int[k - 1];
        int* remainingSigns = new int[k - 1];
        remaining[0] = z;
        remainingSigns[0] = 0;  // ¬z
        for (int i = 2; i < k; i++) {
            remaining[i - 1] = vars[i];
            remainingSigns[i - 1] = signs[i];
        }
        AddKSat(remaining, remainingSigns, k - 1);

        delete[] remaining;
        delete[] remainingSigns;
    }

    void addAtLeastOne4(int a, int b, int c, int d) {
        // (a v b v c v d)
        int s1 = getNextVar();
        int s2 = getNextVar();
        int s3 = getNextVar();

        // s1 = a
        addClause({ -s1, a });
        addClause({ -a, s1 });

        // s2 = s1 OR b
        addClause({ -s2, s1, b });
        addClause({ -s1, s2 });
        addClause({ -b, s2 });

        // s3 = s2 OR c
        addClause({ -s3, s2, c });
        addClause({ -s2, s3 });
        addClause({ -c, s3 });

        // s3 OR d  (au moins un de s3 ou d)
        addClause({ -s3, d });
    }
    
    void addAtLeastOne(int* vars, int* signs, int k) {
        if (k == 0) return;
        if (k == 1) { Add1Sat(vars[0], signs[0]); return; }
        if (k == 2) { Add2Sat(vars[0], vars[1], signs[0], signs[1]); return; }
        if (k == 3) { Add3Sat(vars[0], vars[1], vars[2], signs[0], signs[1], signs[2]); return; }

        // ✅ Pour k >= 4, utiliser l'approche récursive (plus fiable)
        // (a v b v c v d) = (a v b v z) ∧ (¬z v c v d)
        if (k == 4) {
            int z = getNextVar();
            // a v b v z
            addClause({ (signs[0] ? vars[0] : -vars[0]),
                        (signs[1] ? vars[1] : -vars[1]),
                        z });
            // ¬z v c v d
            addClause({ -z,
                        (signs[2] ? vars[2] : -vars[2]),
                        (signs[3] ? vars[3] : -vars[3]) });
            return;
        }

        // Pour k > 4, utiliser l'encodage séquentiel
        int* s = new int[k - 1];
        for (int i = 0; i < k - 1; i++) {
            s[i] = getNextVar();
        }

        // s[0] = vars[0]
        addClause({ -s[0], (signs[0] ? vars[0] : -vars[0]) });
        addClause({ -(signs[0] ? vars[0] : -vars[0]), s[0] });

        for (int i = 1; i < k - 1; i++) {
            addClause({ -s[i], s[i - 1], (signs[i] ? vars[i] : -vars[i]) });
            addClause({ -s[i - 1], s[i] });
            addClause({ -(signs[i] ? vars[i] : -vars[i]), s[i] });
        }

        Add1Sat(s[k - 2], 1);
        delete[] s;
    }

    void addAtLeastOne22(int* vars, int* signs, int k) {
        if (k == 0) return;
        if (k == 1) { Add1Sat(vars[0], signs[0]); return; }
        if (k == 2) { Add2Sat(vars[0], vars[1], signs[0], signs[1]); return; }
        if (k == 3) { Add3Sat(vars[0], vars[1], vars[2], signs[0], signs[1], signs[2]); return; }

        // ✅ Pour k >= 4, utiliser l'encodage séquentiel
        int* s = new int[k - 1];
        for (int i = 0; i < k - 1; i++) {
            s[i] = getNextVar();
        }

        // s[0] = vars[0]
        addClause({ -s[0], (signs[0] ? vars[0] : -vars[0]) });
        addClause({ -(signs[0] ? vars[0] : -vars[0]), s[0] });

        // s[i] = s[i-1] OR vars[i]
        for (int i = 1; i < k - 1; i++) {
            addClause({ -s[i], s[i - 1], (signs[i] ? vars[i] : -vars[i]) });
            addClause({ -s[i - 1], s[i] });
            addClause({ -(signs[i] ? vars[i] : -vars[i]), s[i] });
        }

        // Au moins un : s[k-2] = vrai
        Add1Sat(s[k - 2], 1);

        delete[] s;
    }

    void addExactlyOne(int a, int b, int c, int d) {
        // Au moins un : (a v b v c v d)
        // On utilise 2 variables auxiliaires
        int z1 = getNextVar();
        int z2 = getNextVar();

        addClause({ a, b, z1 });
        addClause({ -z1, c, z2 });
        addClause({ -z2, d });

        // Au plus un : clauses binaires
        addClause({ -a, -b });
        addClause({ -a, -c });
        addClause({ -a, -d });
        addClause({ -b, -c });
        addClause({ -b, -d });
        addClause({ -c, -d });
    }

    void oooAddXor(int a, int b, int c) {
        Add3Sat(a, b, c, 1, 1, 0);
        Add3Sat(a, b, c, 1, 0, 1);
        Add3Sat(a, b, c, 0, 1, 1);
        Add3Sat(a, b, c, 0, 0, 0);
    }

    void AddXor(int a, int b, int c) {
        // c = a XOR b
        // (a v b v ¬c) ∧ (a v ¬b v c) ∧ (¬a v b v c) ∧ (¬a v ¬b v ¬c)
        addClause({ a, b, -c });
        addClause({ a, -b, c });
        addClause({ -a, b, c });
        addClause({ -a, -b, -c });  // ← c=0 quand a=0,b=0
    }

    void oooAddAnd(int a, int b, int c) {
        Add3Sat(a, b, c, 1, 1, 0);
        Add3Sat(a, b, c, 1, 0, 0);
        Add3Sat(a, b, c, 0, 1, 0);
        Add3Sat(a, b, c, 0, 0, 1);
    }

    void AddAnd(int a, int b, int c) {
        // c = a AND b
        // (¬a v ¬b v c) ∧ (a v ¬c) ∧ (b v ¬c)
        addClause({ -a, -b, c });
        addClause({ a, -c });
        addClause({ b, -c });
    }


    void oooAddOr(int a, int b, int c) {
        Add3Sat(a, b, c, 1, 1, 0);
        Add3Sat(a, b, c, 1, 0, 1);
        Add3Sat(a, b, c, 0, 1, 1);
        Add3Sat(a, b, c, 0, 0, 1);
    }

    void AddOr(int a, int b, int c) {
        // c = a OR b
        // (a v b v ¬c) ∧ (¬a v c) ∧ (¬b v c)
        addClause({ a, b, -c });
        addClause({ -a, c });
        addClause({ -b, c });
    }


    void AddAddBin(int a, int b, int res, int ret, int retenue) {
        int s = getNextVar();
        int r = getNextVar();
        int t = getNextVar();

        AddXor(a, b, s);
        AddAnd(a, b, r);
        AddXor(s, ret, res);
        AddAnd(s, ret, t);
        AddOr(r, t, retenue);
    }

    // ============================================================
    // INITIALISATION
    // ============================================================

    void init() {
        LOG("=== INIT ===");
        int vars = getMaxVar() + 1;

        assignment.assign(vars, -1);
        level.assign(vars, -1);
        reason.assign(vars, -1);
        seen.assign(vars, 0);
        activity.assign(vars, 0.0);

        trail.clear();
        trail_lim.clear();
        qhead = 0;
        decisionLevel = 0;
        decisions = 0;
        propagations = 0;
        conflicts = 0;
        satisfiable = false;
        learntClauses.clear();
        conflictCount = 0;
        order_heap = priority_queue<pair<double, int>>();

        LOG("vars=" << vars);
    }

    // ============================================================
    // VSIDS
    // ============================================================

    void bumpActivity(int var) {
        activity[var] += var_inc;
        order_heap.push(make_pair(activity[var], var));
    }

    void decayActivities() {
        for (int i = 1; i <= getMaxVar(); i++) {
            activity[i] *= var_decay;
        }
        var_inc *= (1.0 / var_decay);
    }

    // ============================================================
    // CHOIX DE VARIABLE
    // ============================================================

    int chooseVarGOOD() {
        // Essayer la heap d'abord
        while (!order_heap.empty()) {
            auto p = order_heap.top();
            order_heap.pop();
            int var = p.second;
            if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                // Remettre dans la heap pour plus tard (car on ne l'a pas choisie ? Non, on la choisit)
                return var;
            }
        }

        // Fallback : chercher n'importe quelle variable non assignée
        for (int i = 1; i <= getMaxVar(); i++) {
            if (i < (int)assignment.size() && assignment[i] == -1) {
                return i;
            }
        }
        return -1;
    }

    int chooseVarNOCACHEGOOD() {
        // Essayer la heap
        while (!order_heap.empty()) {
            auto p = order_heap.top();
            order_heap.pop();
            int var = p.second;
            if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                return var;
            }
        }

        // ✅ Fallback optimisé avec cache
        static int lastVar = 1;
        int maxVar = getMaxVar();
        for (int i = lastVar; i <= maxVar; i++) {
            if (i < (int)assignment.size() && assignment[i] == -1) {
                lastVar = i + 1;
                if (lastVar > maxVar) lastVar = 1;
                return i;
            }
        }

        // Réinitialiser et réessayer
        lastVar = 1;
        for (int i = lastVar; i <= maxVar; i++) {
            if (i < (int)assignment.size() && assignment[i] == -1) {
                lastVar = i + 1;
                return i;
            }
        }
        return -1;
    }

    int chooseVar() {
        // ✅ Version optimisée avec cache
        static int lastVar = 1;
        int maxVar = getMaxVar();

        // D'abord la heap
        while (!order_heap.empty()) {
            auto p = order_heap.top();
            order_heap.pop();
            int var = p.second;
            if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                return var;
            }
        }

        // Fallback rapide avec cache
        for (int i = lastVar; i <= maxVar; i++) {
            if (i < (int)assignment.size() && assignment[i] == -1) {
                lastVar = i + 1;
                if (lastVar > maxVar) lastVar = 1;
                return i;
            }
        }

        lastVar = 1;
        return -1;
    }

    // ============================================================
    // ASSIGNATION
    // ============================================================

    void assign(int var, int value, int reasonIdx) {
        LOG("assign: x" << var << "=" << value << " (level=" << decisionLevel << ", reason=" << reasonIdx << ")");
        assignment[var] = value;
        level[var] = decisionLevel;
        reason[var] = reasonIdx;
        trail.push_back(var);
        bumpActivity(var);
    }

    // ============================================================
    // PROPAGATION
    // ============================================================
    void cleanWatches000() {
        for (int v = 1; v < (int)watches.size(); v++) {
            int j = 0;
            for (int i = 0; i < (int)watches[v].size(); i++) {
                if (watches[v][i].clause != -1) {
                    watches[v][j++] = watches[v][i];
                }
            }
            watches[v].resize(j);
        }
    }

    void cleanWatches() {
        for (int v = 1; v < (int)watches.size(); v++) {
            int j = 0;
            for (int i = 0; i < (int)watches[v].size(); i++) {
                int clauseIdx = watches[v][i].clause;
                if (clauseIdx >= 0 && clauseIdx < (int)clauses.size()
                    && !clauses[clauseIdx].deleted
                    && !clauseSat[clauseIdx]) {  // ← Vérifier le cache
                    watches[v][j++] = watches[v][i];
                }
            }
            watches[v].resize(j);
        }
    }

    bool propagate1() {
        propagationCount++;
        if (propagationCount % 10000 == 0) {
            // Nettoyer tous les watchers invalides
            for (int v = 1; v < (int)watches.size(); v++) {
                int j = 0;
                for (int k = 0; k < (int)watches[v].size(); k++) {
                    if (watches[v][k].clause >= 0 && watches[v][k].clause < (int)clauses.size()
                        && !clauses[watches[v][k].clause].deleted) {
                        watches[v][j++] = watches[v][k];
                    }
                }
                watches[v].resize(j);
            }
        }

        LOG("propagate: qhead=" << qhead << ", trail.size=" << trail.size());

        while (qhead < (int)trail.size()) {
            int var = trail[qhead++];
            LOG("  propagate var x" << var << " (val=" << (int)assignment[var] << ")");

            if (var < 1 || var >= (int)watches.size()) {
                LOG("  WARNING: var=" << var << " hors limites");
                continue;
            }

            int nbWatchers = (int)watches[var].size();
            for (int i = 0; i < nbWatchers; i++) {
                if (i >= (int)watches[var].size()) break;

                Watcher& w = watches[var][i];
                int clauseIdx = w.clause;

                if (clauseIdx < 0 || clauseIdx >= (int)clauses.size()) {
                    // Supprimer le watcher invalide
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    nbWatchers--;
                    continue;
                }

                Clause& c = clauses[clauseIdx];
                if (c.deleted) {
                    // Supprimer le watcher
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    nbWatchers--;
                    continue;
                }

                // Vérifier si la clause est déjà satisfaite
                bool isSat = false;
                for (int lit2 : c.lits) {
                    int v2 = abs(lit2);
                    if (v2 < 1 || v2 >= (int)assignment.size()) continue;
                    bool s = (lit2 > 0);
                    if (assignment[v2] != -1 && (assignment[v2] == 1) == s) {
                        isSat = true;
                        break;
                    }
                }

                if (isSat) {
                    // Clause satisfaite, supprimer le watcher
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    nbWatchers--;
                    continue;
                }

                // Chercher un nouveau watcher (littéral vrai)
                /*bool found = false;
                for (int j = 0; j < c.size(); j++) {
                    int lit = c.lits[j];
                    int v = abs(lit);
                    if (v < 1 || v >= (int)assignment.size()) continue;
                    bool sign = (lit > 0);

                    if (v == var) continue;

                    if (assignment[v] != -1 && ((assignment[v] == 1) == sign)) {
                        if (v >= 1 && v < (int)watches.size()) {
                            watches[v].push_back(Watcher(clauseIdx, v));
                            // Supprimer l'ancien watcher
                            watches[var][i] = watches[var].back();
                            watches[var].pop_back();
                            i--;
                            nbWatchers--;
                            found = true;
                            LOG("    watcher deplace vers x" << v);
                            break;
                        }
                    }
                }

                if (found) continue;*/

                // Chercher un nouveau watcher : n'importe quel littéral non-faux (vrai OU non-assigné), autre que 'var'
                bool found = false;
                for (int j = 0; j < c.size(); j++) {
                    int lit = c.lits[j];
                    int v = abs(lit);
                    if (v == var) continue;
                    bool sign = (lit > 0);
                    // non-faux = non-assigné OU vrai
                    if (assignment[v] != -1 && ((assignment[v] == 1) == sign)) {
                        watches[v].push_back(Watcher(clauseIdx, v));
                        watches[var][i] = watches[var].back();
                        watches[var].pop_back();
                        i--; nbWatchers--;
                        found = true;
                        break;
                    }
                }
                if (found) continue;

                // La clause est unitaire ou en conflit
                int undefCount = 0;
                int unitVar = -1;
                bool unitSign = false;
                bool allFalse = true;

                for (int lit2 : c.lits) {
                    int v2 = abs(lit2);
                    if (v2 < 1 || v2 >= (int)assignment.size()) continue;
                    bool s = (lit2 > 0);
                    if (assignment[v2] == -1) {
                        undefCount++;
                        unitVar = v2;
                        unitSign = s;
                    }
                    else if ((assignment[v2] == 1) == s) {
                        allFalse = false;
                        break;
                    }
                }

                if (allFalse && undefCount == 0) {
                    LOG("  CONFLIT sur la clause " << clauseIdx);
                    return analyzeConflict(c, clauseIdx);
                }

                if (undefCount == 1 && unitVar >= 1 && unitVar < (int)assignment.size() && assignment[unitVar] == -1) {
                    assign(unitVar, unitSign ? 1 : 0, clauseIdx);
                    propagations++;
                    LOG("    propagation: x" << unitVar << "=" << (unitSign ? 1 : 0) << " (clause " << clauseIdx << ")");
                }
            }
        }

        LOG("propagate: fin");
        return true;
    }

    bool propagateGOOD() {
        propagationCount++;
        if (propagationCount % 10000 == 0) {
            cleanWatches();
        }

        LOG("propagate: qhead=" << qhead << ", trail.size=" << trail.size());

        while (qhead < (int)trail.size()) {
            int var = trail[qhead++];
            LOG("  propagate var x" << var << " (val=" << (int)assignment[var] << ")");

            if (var < 1 || var >= (int)watches.size()) {
                LOG("  WARNING: var=" << var << " hors limites");
                continue;
            }

            // ✅ Faire une copie des watchers pour éviter les problèmes d'itération
            vector<Watcher> currentWatches = watches[var];

            for (int i = 0; i < (int)currentWatches.size(); i++) {
                Watcher& w = currentWatches[i];
                int clauseIdx = w.clause;

                if (clauseIdx < 0 || clauseIdx >= (int)clauses.size()) {
                    continue;
                }

                Clause& c = clauses[clauseIdx];
                if (c.deleted) {
                    continue;
                }

                // Vérifier si la clause est déjà satisfaite
                bool isSat = false;
                for (int lit2 : c.lits) {
                    int v2 = abs(lit2);
                    if (v2 < 1 || v2 >= (int)assignment.size()) continue;
                    bool s = (lit2 > 0);
                    if (assignment[v2] != -1 && (assignment[v2] == 1) == s) {
                        isSat = true;
                        break;
                    }
                }

                if (isSat) {
                    // Supprimer le watcher
                    auto it = find(watches[var].begin(), watches[var].end(), w);
                    if (it != watches[var].end()) {
                        watches[var].erase(it);
                    }
                    continue;
                }

                // ✅ Vérifier d'abord si la clause est unitaire (un seul littéral non-assigné)
                int undefCount = 0;
                int unitVar = -1;
                bool unitSign = false;
                bool allFalse = true;

                for (int lit2 : c.lits) {
                    int v2 = abs(lit2);
                    if (v2 < 1 || v2 >= (int)assignment.size()) continue;
                    bool s = (lit2 > 0);
                    if (assignment[v2] == -1) {
                        undefCount++;
                        unitVar = v2;
                        unitSign = s;
                    }
                    else if ((assignment[v2] == 1) == s) {
                        allFalse = false;
                        break;
                    }
                }

                if (allFalse && undefCount == 0) {
                    LOG("  CONFLIT sur la clause " << clauseIdx);
                    return analyzeConflict(c, clauseIdx);
                }

                if (undefCount == 1 && unitVar >= 1 && unitVar < (int)assignment.size() && assignment[unitVar] == -1) {
                    // ✅ Propager immédiatement sans déplacer le watcher
                    assign(unitVar, unitSign ? 1 : 0, clauseIdx);
                    propagations++;
                    LOG("    propagation: x" << unitVar << "=" << (unitSign ? 1 : 0) << " (clause " << clauseIdx << ")");
                    continue;  // ← Ne pas déplacer le watcher
                }

                // Chercher un nouveau watcher (littéral vrai d'abord)
                bool found = false;
                for (int j = 0; j < c.size(); j++) {
                    int lit = c.lits[j];
                    int v = abs(lit);
                    if (v < 1 || v >= (int)assignment.size()) continue;
                    bool sign = (lit > 0);

                    if (v == var) continue;

                    if (assignment[v] != -1 && (assignment[v] == 1) == sign) {
                        if (v >= 1 && v < (int)watches.size()) {
                            // ✅ Vérifier que la clause n'est pas déjà watchée par v
                            bool alreadyWatched = false;
                            for (Watcher& w2 : watches[v]) {
                                if (w2.clause == clauseIdx) {
                                    alreadyWatched = true;
                                    break;
                                }
                            }
                            if (!alreadyWatched) {
                                watches[v].push_back(Watcher(clauseIdx, v));
                                auto it = find(watches[var].begin(), watches[var].end(), w);
                                if (it != watches[var].end()) {
                                    watches[var].erase(it);
                                }
                                found = true;
                                LOG("    watcher deplace vers x" << v);
                                break;
                            }
                        }
                    }
                }

                if (found) continue;

                // Fallback : littéral non-assigné
                for (int j = 0; j < c.size(); j++) {
                    int lit = c.lits[j];
                    int v = abs(lit);
                    if (v == var) continue;
                    bool sign = (lit > 0);

                    if (v >= 1 && v < (int)assignment.size() && assignment[v] == -1) {
                        if (v >= 1 && v < (int)watches.size()) {
                            // ✅ Vérifier que la clause n'est pas déjà watchée par v
                            bool alreadyWatched = false;
                            for (Watcher& w2 : watches[v]) {
                                if (w2.clause == clauseIdx) {
                                    alreadyWatched = true;
                                    break;
                                }
                            }
                            if (!alreadyWatched) {
                                watches[v].push_back(Watcher(clauseIdx, v));
                                auto it = find(watches[var].begin(), watches[var].end(), w);
                                if (it != watches[var].end()) {
                                    watches[var].erase(it);
                                }
                                found = true;
                                break;
                            }
                        }
                    }
                }

                if (found) continue;

                // Si on arrive ici, la clause est en conflit ou unitaire
                // (déjà traité plus haut)
            }
        }

        LOG("propagate: fin");
        return true;
    }

    bool propagateNOCACHE() {
        propagationCount++;
        if (propagationCount % 10000 == 0) {
            cleanWatches();
        }

        LOG("propagate: qhead=" << qhead << ", trail.size=" << trail.size());

        while (qhead < (int)trail.size()) {
            int var = trail[qhead++];
            LOG("  propagate var x" << var << " (val=" << (int)assignment[var] << ")");

            if (var < 1 || var >= (int)watches.size()) {
                LOG("  WARNING: var=" << var << " hors limites");
                continue;
            }

            // ✅ Parcourir avec un index pour éviter les copies
            for (int i = 0; i < (int)watches[var].size(); i++) {
                Watcher& w = watches[var][i];
                int clauseIdx = w.clause;

                if (clauseIdx < 0 || clauseIdx >= (int)clauses.size()) {
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                Clause& c = clauses[clauseIdx];
                if (c.deleted) {
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                // ✅ Vérifier d'abord si la clause est déjà satisfaite (avec cache)
                bool isSat = false;
                for (int lit2 : c.lits) {
                    int v2 = abs(lit2);
                    if (v2 < 1 || v2 >= (int)assignment.size()) continue;
                    bool s = (lit2 > 0);
                    if (assignment[v2] != -1 && (assignment[v2] == 1) == s) {
                        isSat = true;
                        break;
                    }
                }

                if (isSat) {
                    // Clause satisfaite, supprimer le watcher
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                // ✅ Compter les littéraux non-assignés (pour détecter unitaire/conflit)
                int undefCount = 0;
                int unitVar = -1;
                bool unitSign = false;
                bool allFalse = true;

                for (int lit2 : c.lits) {
                    int v2 = abs(lit2);
                    if (v2 < 1 || v2 >= (int)assignment.size()) continue;
                    bool s = (lit2 > 0);
                    if (assignment[v2] == -1) {
                        undefCount++;
                        unitVar = v2;
                        unitSign = s;
                        if (undefCount > 1) break; // ✅ Optimisation : pas besoin de compter plus
                    }
                    else if ((assignment[v2] == 1) == s) {
                        allFalse = false;
                        break;
                    }
                }

                // ✅ Conflit : tous les littéraux sont faux
                if (allFalse && undefCount == 0) {
                    LOG("  CONFLIT sur la clause " << clauseIdx);
                    return analyzeConflict(c, clauseIdx);
                }

                // ✅ Clause unitaire : un seul littéral non-assigné
                if (undefCount == 1 && unitVar >= 1 && unitVar < (int)assignment.size() && assignment[unitVar] == -1) {
                    assign(unitVar, unitSign ? 1 : 0, clauseIdx);
                    propagations++;
                    LOG("    propagation: x" << unitVar << "=" << (unitSign ? 1 : 0) << " (clause " << clauseIdx << ")");
                    // ✅ Supprimer le watcher de la clause unitaire (elle est maintenant satisfaite)
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                // ✅ Chercher un nouveau watcher (littéral vrai d'abord)
                bool found = false;
                for (int j = 0; j < c.size(); j++) {
                    int lit = c.lits[j];
                    int v = abs(lit);
                    if (v < 1 || v >= (int)assignment.size()) continue;
                    bool sign = (lit > 0);

                    if (v == var) continue;

                    // ✅ Priorité : littéral VRAI
                    if (assignment[v] != -1 && (assignment[v] == 1) == sign) {
                        if (v >= 1 && v < (int)watches.size()) {
                            // ✅ Vérifier que la clause n'est pas déjà watchée par v
                            bool alreadyWatched = false;
                            for (const Watcher& w2 : watches[v]) {
                                if (w2.clause == clauseIdx) {
                                    alreadyWatched = true;
                                    break;
                                }
                            }
                            if (!alreadyWatched) {
                                watches[v].push_back(Watcher(clauseIdx, v));
                                watches[var][i] = watches[var].back();
                                watches[var].pop_back();
                                i--;
                                found = true;
                                LOG("    watcher deplace vers x" << v);
                                break;
                            }
                        }
                    }
                }

                if (found) continue;

                // ✅ Fallback : littéral non-assigné
                for (int j = 0; j < c.size(); j++) {
                    int lit = c.lits[j];
                    int v = abs(lit);
                    if (v == var) continue;
                    bool sign = (lit > 0);

                    if (v >= 1 && v < (int)assignment.size() && assignment[v] == -1) {
                        if (v >= 1 && v < (int)watches.size()) {
                            // ✅ Vérifier que la clause n'est pas déjà watchée par v
                            bool alreadyWatched = false;
                            for (const Watcher& w2 : watches[v]) {
                                if (w2.clause == clauseIdx) {
                                    alreadyWatched = true;
                                    break;
                                }
                            }
                            if (!alreadyWatched) {
                                watches[v].push_back(Watcher(clauseIdx, v));
                                watches[var][i] = watches[var].back();
                                watches[var].pop_back();
                                i--;
                                found = true;
                                break;
                            }
                        }
                    }
                }

                if (found) continue;

                // ✅ Si on arrive ici, la clause est en conflit (déjà traité plus haut)
                // ou le watcher n'a pas pu être déplacé → conserver le watcher actuel
            }
        }

        LOG("propagate: fin");
        return true;
    }

    bool propagate() {
        propagationCount++;
        if (propagationCount % 10000 == 0) {
            cleanWatches();
        }

        LOG("propagate: qhead=" << qhead << ", trail.size=" << trail.size());

        while (qhead < (int)trail.size()) {
            int var = trail[qhead++];
            LOG("  propagate var x" << var << " (val=" << (int)assignment[var] << ")");

            if (var < 1 || var >= (int)watches.size()) {
                LOG("  WARNING: var=" << var << " hors limites");
                continue;
            }

            // ✅ Parcourir avec un index pour éviter les copies
            for (int i = 0; i < (int)watches[var].size(); i++) {
                Watcher& w = watches[var][i];
                int clauseIdx = w.clause;

                if (clauseIdx < 0 || clauseIdx >= (int)clauses.size()) {
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                Clause& c = clauses[clauseIdx];
                if (c.deleted) {
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                // ✅ Vérifier d'abord si la clause est déjà satisfaite (avec cache)
                bool isSat = false;

                // ✅ Si la clause est marquée comme satisfaite dans le cache
                if (clauseSat[clauseIdx]) {
                    isSat = true;
                }
                else {
                    // Vérifier la clause
                    for (int lit2 : c.lits) {
                        int v2 = abs(lit2);
                        if (v2 < 1 || v2 >= (int)assignment.size()) continue;
                        bool s = (lit2 > 0);
                        if (assignment[v2] != -1 && (assignment[v2] == 1) == s) {
                            isSat = true;
                            clauseSat[clauseIdx] = 1;  // ← Mettre en cache
                            break;
                        }
                    }
                }

                if (isSat) {
                    // Clause satisfaite, supprimer le watcher
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                // ✅ Compter les littéraux non-assignés (pour détecter unitaire/conflit)
                int undefCount = 0;
                int unitVar = -1;
                bool unitSign = false;
                bool allFalse = true;

                for (int lit2 : c.lits) {
                    int v2 = abs(lit2);
                    if (v2 < 1 || v2 >= (int)assignment.size()) continue;
                    bool s = (lit2 > 0);
                    if (assignment[v2] == -1) {
                        undefCount++;
                        unitVar = v2;
                        unitSign = s;
                        if (undefCount > 1) break; // ✅ Optimisation
                    }
                    else if ((assignment[v2] == 1) == s) {
                        allFalse = false;
                        break;
                    }
                }

                // ✅ Conflit : tous les littéraux sont faux
                if (allFalse && undefCount == 0) {
                    LOG("  CONFLIT sur la clause " << clauseIdx);
                    return analyzeConflict(c, clauseIdx);
                }

                // ✅ Clause unitaire : un seul littéral non-assigné
                if (undefCount == 1 && unitVar >= 1 && unitVar < (int)assignment.size() && assignment[unitVar] == -1) {
                    assign(unitVar, unitSign ? 1 : 0, clauseIdx);
                    propagations++;
                    LOG("    propagation: x" << unitVar << "=" << (unitSign ? 1 : 0) << " (clause " << clauseIdx << ")");

                    // ✅ La clause est maintenant satisfaite, on peut la marquer dans le cache
                    // Mais seulement si tous les littéraux sont assignés
                    bool allAssigned = true;
                    for (int lit2 : c.lits) {
                        int v2 = abs(lit2);
                        if (v2 >= 1 && v2 < (int)assignment.size() && assignment[v2] == -1) {
                            allAssigned = false;
                            break;
                        }
                    }
                    if (allAssigned) {
                        clauseSat[clauseIdx] = 1;
                    }

                    // Supprimer le watcher
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                // ✅ Chercher un nouveau watcher (littéral vrai d'abord)
                bool found = false;
                for (int j = 0; j < c.size(); j++) {
                    int lit = c.lits[j];
                    int v = abs(lit);
                    if (v < 1 || v >= (int)assignment.size()) continue;
                    bool sign = (lit > 0);

                    if (v == var) continue;

                    // ✅ Priorité : littéral VRAI
                    if (assignment[v] != -1 && (assignment[v] == 1) == sign) {
                        if (v >= 1 && v < (int)watches.size()) {
                            // ✅ Vérifier que la clause n'est pas déjà watchée par v
                            bool alreadyWatched = false;
                            for (const Watcher& w2 : watches[v]) {
                                if (w2.clause == clauseIdx) {
                                    alreadyWatched = true;
                                    break;
                                }
                            }
                            if (!alreadyWatched) {
                                watches[v].push_back(Watcher(clauseIdx, v));
                                watches[var][i] = watches[var].back();
                                watches[var].pop_back();
                                i--;
                                found = true;
                                LOG("    watcher deplace vers x" << v);
                                break;
                            }
                        }
                    }
                }

                if (found) continue;

                // ✅ Fallback : littéral non-assigné
                for (int j = 0; j < c.size(); j++) {
                    int lit = c.lits[j];
                    int v = abs(lit);
                    if (v == var) continue;
                    bool sign = (lit > 0);

                    if (v >= 1 && v < (int)assignment.size() && assignment[v] == -1) {
                        if (v >= 1 && v < (int)watches.size()) {
                            // ✅ Vérifier que la clause n'est pas déjà watchée par v
                            bool alreadyWatched = false;
                            for (const Watcher& w2 : watches[v]) {
                                if (w2.clause == clauseIdx) {
                                    alreadyWatched = true;
                                    break;
                                }
                            }
                            if (!alreadyWatched) {
                                watches[v].push_back(Watcher(clauseIdx, v));
                                watches[var][i] = watches[var].back();
                                watches[var].pop_back();
                                i--;
                                found = true;
                                break;
                            }
                        }
                    }
                }

                if (found) continue;

                // ✅ Si on arrive ici, la clause est en conflit (déjà traité plus haut)
            }
        }

        LOG("propagate: fin");
        return true;
    }

    

    bool propagateSIMPLE() {
        while (qhead < (int)trail.size()) {
            int var = trail[qhead++];

            for (int i = 0; i < (int)watches[var].size(); i++) {
                Watcher& w = watches[var][i];
                int clauseIdx = w.clause;
                Clause& c = clauses[clauseIdx];

                // ✅ Vérifier d'abord si la clause est satisfaite
                bool isSat = false;
                int undefCount = 0;
                int unitVar = -1;
                bool unitSign = false;

                for (int lit2 : c.lits) {
                    int v2 = abs(lit2);
                    if (v2 < 1 || v2 >= (int)assignment.size()) continue;
                    bool s = (lit2 > 0);
                    if (assignment[v2] == -1) {
                        undefCount++;
                        unitVar = v2;
                        unitSign = s;
                    }
                    else if ((assignment[v2] == 1) == s) {
                        isSat = true;
                        break;
                    }
                }

                // Clause satisfaite
                if (isSat) {
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                // Clause unitaire : propager
                if (undefCount == 1 && unitVar >= 1 && unitVar < (int)assignment.size() && assignment[unitVar] == -1) {
                    assign(unitVar, unitSign ? 1 : 0, clauseIdx);
                    propagations++;
                    // ✅ NE PAS déplacer le watcher, supprimer la clause de la liste des watchers
                    watches[var][i] = watches[var].back();
                    watches[var].pop_back();
                    i--;
                    continue;
                }

                // ✅ Si clause non-satisfaite et non-unitaire, déplacer le watcher
                // Chercher un nouveau watcher (littéral vrai ou non-assigné)
                bool found = false;
                for (int j = 0; j < c.size(); j++) {
                    int lit = c.lits[j];
                    int v = abs(lit);
                    if (v == var) continue;
                    if (v < 1 || v >= (int)assignment.size()) continue;
                    bool sign = (lit > 0);

                    // Accepter littéral vrai ou non-assigné
                    if (assignment[v] == -1 || (assignment[v] == 1) == sign) {
                        if (v >= 1 && v < (int)watches.size()) {
                            watches[v].push_back(Watcher(clauseIdx, v));
                            watches[var][i] = watches[var].back();
                            watches[var].pop_back();
                            i--;
                            found = true;
                            break;
                        }
                    }
                }

                // Si on ne peut pas déplacer le watcher, le garder
                if (!found) {
                    // Conserver le watcher sur var
                }
            }
        }
        return true;
    }
    // ============================================================
    // ANALYSE DE CONFLIT
    // ============================================================

    bool oooanalyzeConflict(Clause& conflictClause, int conflictIdx) {
        conflicts++;
        conflictCount++;

        LOG("analyzeConflict: conflit #" << conflicts << " (level=" << decisionLevel << ")");
        LOG("  clause de conflit: ");
#if DEBUG
        conflictClause.print();
#endif

        if (decisionLevel == 0) {
            LOG("  UNSAT (decisionLevel=0)");
            return false;
        }

        vector<int> learntLits;
        int counter = 0;

        for (int lit : conflictClause.lits) {
            int var = abs(lit);
            if (var >= 1 && var < (int)level.size() && level[var] > 0) {
                seen[var] = 1;
                // Ici, -lit inverse le signe. Pour la clause de conflit (nx1),
                // lit=-1, -lit=1, donc on ajoute 1 (x1=VRAI) à la clause apprise.
                // Mais on veut apprendre nx1, donc on doit ajouter lit, pas -lit.
                learntLits.push_back(lit);   // Correction : lit au lieu de -lit
                counter++;
                LOG("  initial: x" << var << " lit=" << lit << " -> -lit=" << -lit);
            }
        }

        int idx = trail.size() - 1;
        LOG("  resolution 1-UIP, counter=" << counter);

        while (counter > 1 && idx >= 0) {
            int var = trail[idx];
            idx--;

            if (var < 1 || var >= (int)reason.size()) continue;
            if (reason[var] == -1 || level[var] == 0) continue;

            if (seen[var]) {
                seen[var] = 0;
                counter--;
                LOG("    seen x" << var << " -> counter=" << counter);
            }

            if (reason[var] < 0 || reason[var] >= (int)clauses.size()) continue;

            Clause* reasonClause = &clauses[reason[var]];
            LOG("    raison x" << var << " = clause " << reason[var]);

            for (int lit : reasonClause->lits) {
                int v = abs(lit);
                if (v == var) continue;
                if (v >= 1 && v < (int)level.size() && level[v] > 0 && !seen[v]) {
                    seen[v] = 1;
                    learntLits.push_back(lit);   // Correction : lit au lieu de -lit
                    counter++;
                    LOG("      ajout: lit=" << lit << " (x" << v << ")");
                }
            }
        }

        // Supprimer les littéraux résolus (ceux dont seen == 0 après la résolution)
        vector<int> filtered;
        for (int lit : learntLits) {
            int var = abs(lit);
            if (var >= 1 && var < (int)seen.size() && seen[var] == 1) {
                filtered.push_back(lit);
                seen[var] = 0;
            }
        }
        learntLits = filtered;

        sort(learntLits.begin(), learntLits.end());
        learntLits.erase(unique(learntLits.begin(), learntLits.end()), learntLits.end());

        LOG("  clause apprise: ");
#if DEBUG
        for (int l : learntLits) cout << l << " ";
        cout << endl;
#endif

        if (!learntLits.empty()) {
            Clause newClause(learntLits, true);
            int idxLearn = clauses.size();
            learntClauses.push_back(newClause);
            clauses.push_back(newClause);

            if (learntLits.size() >= 2) {
                int v1 = abs(learntLits[0]);
                int v2 = abs(learntLits[1]);
                if (v1 >= 1 && v1 < (int)watches.size()) {
                    watches[v1].push_back(Watcher(idxLearn, v2));
                }
                if (v2 >= 1 && v2 < (int)watches.size()) {
                    watches[v2].push_back(Watcher(idxLearn, v1));
                }
            }

            // Calculer le backjump level (deuxième niveau le plus haut)
            int maxLevel = 0;
            int secondMaxLevel = 0;
            for (int lit : learntLits) {
                int var = abs(lit);
                if (var >= 1 && var < (int)level.size() && level[var] > 0) {
                    if (level[var] > maxLevel) {
                        secondMaxLevel = maxLevel;
                        maxLevel = level[var];
                    }
                    else if (level[var] > secondMaxLevel && level[var] < maxLevel) {
                        secondMaxLevel = level[var];
                    }
                }
            }
            int btLevel = secondMaxLevel;

            LOG("  levels: ");
            for (int lit : learntLits) {
                int var = abs(lit);
                LOG("    x" << var << " level=" << level[var]);
            }

            LOG("  backjump level=" << btLevel);
            backjump(btLevel);

            // Vérifier si la clause apprise est unitaire après le backjump
            int unassigned = 0;
            int unitLit = 0;
            for (int lit : learntLits) {
                int var = abs(lit);
                if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                    unassigned++;
                    unitLit = lit;
                }
                else if (var >= 1 && var < (int)assignment.size() && assignment[var] == (lit > 0 ? 1 : 0)) {
                    // Littéral vrai, clause satisfaite
                    unassigned = -1;
                    break;
                }
            }
            if (unassigned == 1) {
                int var = abs(unitLit);
                bool sign = (unitLit > 0);
                assign(var, sign ? 1 : 0, idxLearn);
                propagations++;
                LOG("  propagation clause apprise: x" << var << "=" << (sign ? 1 : 0));
            }

            return true;
        }

        return false;
    }

    bool analyzeConflict(Clause& conflictClause, int conflictIdx) {
        conflicts++;
        conflictCount++;

        LOG("analyzeConflict: conflit #" << conflicts << " (level=" << decisionLevel << ")");
        LOG("  clause de conflit: ");
#if DEBUG
        conflictClause.print();
#endif

        if (decisionLevel == 0) {
            LOG("  UNSAT (decisionLevel=0)");
            return false;
        }

        vector<int> learntLits;
        int counter = 0;

        for (int lit : conflictClause.lits) {
            int var = abs(lit);
            if (var >= 1 && var < (int)level.size() && level[var] > 0) {
                seen[var] = 1;
                learntLits.push_back(lit);
                counter++;
                LOG("  initial: x" << var << " lit=" << lit);
            }
        }

        int idx = trail.size() - 1;
        LOG("  resolution 1-UIP, counter=" << counter);

        while (counter > 1 && idx >= 0) {
            int var = trail[idx];
            idx--;

            if (var < 1 || var >= (int)reason.size()) continue;
            if (reason[var] == -1 || level[var] == 0) continue;

            if (seen[var]) {
                seen[var] = 0;
                counter--;
                LOG("    seen x" << var << " -> counter=" << counter);
            }

            if (reason[var] < 0 || reason[var] >= (int)clauses.size()) continue;

            Clause* reasonClause = &clauses[reason[var]];
            LOG("    raison x" << var << " = clause " << reason[var]);

            for (int lit : reasonClause->lits) {
                int v = abs(lit);
                if (v == var) continue;
                if (v >= 1 && v < (int)level.size() && level[v] > 0 && !seen[v]) {
                    seen[v] = 1;
                    learntLits.push_back(lit);
                    counter++;
                    LOG("      ajout: lit=" << lit << " (x" << v << ")");
                }
            }
        }

        // Supprimer les littéraux résolus (ceux dont seen == 0 après la résolution)
        vector<int> filtered;
        for (int lit : learntLits) {
            int var = abs(lit);
            if (var >= 1 && var < (int)seen.size() && seen[var] == 1) {
                filtered.push_back(lit);
                seen[var] = 0;
            }
        }
        learntLits = filtered;

        sort(learntLits.begin(), learntLits.end());
        learntLits.erase(unique(learntLits.begin(), learntLits.end()), learntLits.end());

        LOG("  clause apprise: ");
#if DEBUG
        for (int l : learntLits) cout << l << " ";
        cout << endl;
#endif

        if (!learntLits.empty()) {
            Clause newClause(learntLits, true);
            int idxLearn = clauses.size();
            learntClauses.push_back(newClause);
            clauses.push_back(newClause);
            clauseSat.push_back(0);  // ← Ajouter l'entrée pour la clause apprise

            // ============================================================
            // ✅ CORRECTION : Watcher les littéraux de plus haut niveau
            // ============================================================
            if (learntLits.size() >= 2) {
                // Trouver les 2 littéraux de plus haut niveau de décision
                int idx1 = -1, idx2 = -1;
                int lvl1 = -1, lvl2 = -1;

                for (int i = 0; i < (int)learntLits.size(); i++) {
                    int var = abs(learntLits[i]);
                    int lv = level[var];
                    if (lv > lvl1) {
                        lvl2 = lvl1;
                        idx2 = idx1;
                        lvl1 = lv;
                        idx1 = i;
                    }
                    else if (lv > lvl2) {
                        lvl2 = lv;
                        idx2 = i;
                    }
                }

                // Si idx2 n'a pas été trouvé (cas improbable), utiliser le premier comme fallback
                if (idx2 == -1) {
                    idx2 = (idx1 + 1) % learntLits.size();
                }

                int v1 = abs(learntLits[idx1]);
                int v2 = abs(learntLits[idx2]);

                if (v1 >= 1 && v1 < (int)watches.size()) {
                    watches[v1].push_back(Watcher(idxLearn, v2));
                }
                if (v2 >= 1 && v2 < (int)watches.size()) {
                    watches[v2].push_back(Watcher(idxLearn, v1));
                }

                LOG("  watchers: x" << v1 << " (level=" << lvl1 << ") et x" << v2 << " (level=" << lvl2 << ")");
            }
            else if (learntLits.size() == 1) {
                // Clause unitaire
                int v = abs(learntLits[0]);
                if (v >= 1 && v < (int)watches.size()) {
                    watches[v].push_back(Watcher(idxLearn, v));
                }
            }

            // Calculer le backjump level (deuxième niveau le plus haut)
            int maxLevel = 0;
            int secondMaxLevel = 0;
            for (int lit : learntLits) {
                int var = abs(lit);
                if (var >= 1 && var < (int)level.size() && level[var] > 0) {
                    if (level[var] > maxLevel) {
                        secondMaxLevel = maxLevel;
                        maxLevel = level[var];
                    }
                    else if (level[var] > secondMaxLevel && level[var] < maxLevel) {
                        secondMaxLevel = level[var];
                    }
                }
            }
            int btLevel = secondMaxLevel;

            LOG("  levels: ");
            for (int lit : learntLits) {
                int var = abs(lit);
                LOG("    x" << var << " level=" << level[var]);
            }

            LOG("  backjump level=" << btLevel);
            backjump(btLevel);

            // Vérifier si la clause apprise est unitaire après le backjump
            int unassigned = 0;
            int unitLit = 0;
            for (int lit : learntLits) {
                int var = abs(lit);
                if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                    unassigned++;
                    unitLit = lit;
                }
                else if (var >= 1 && var < (int)assignment.size() && assignment[var] == (lit > 0 ? 1 : 0)) {
                    unassigned = -1;
                    break;
                }
            }
            if (unassigned == 1) {
                int var = abs(unitLit);
                bool sign = (unitLit > 0);
                assign(var, sign ? 1 : 0, idxLearn);
                propagations++;
                LOG("  propagation clause apprise: x" << var << "=" << (sign ? 1 : 0));
            }

            return true;
        }

        return false;
    }

    void clearCache() {
        fill(clauseSat.begin(), clauseSat.end(), 0);
    }

    // ============================================================
    // BACKJUMP
    // ============================================================

    void backjump(int targetLevel) {
        if (targetLevel < 0) targetLevel = 0;
        if (targetLevel > decisionLevel) targetLevel = decisionLevel;

        while (!trail.empty()) {
            int var = trail.back();
            if (var < 1 || var >= (int)level.size()) {
                trail.pop_back();
                continue;
            }
            if (level[var] <= targetLevel) break;

            assignment[var] = -1;
            level[var] = -1;
            reason[var] = -1;
            trail.pop_back();
        }

        while (!trail_lim.empty() && trail_lim.back() > targetLevel) {
            trail_lim.pop_back();
        }

        if (qhead > (int)trail.size()) {
            qhead = trail.size();
        }

     
        decisionLevel = targetLevel;

        // ✅ Vider la heap des variables assignées
        while (!order_heap.empty()) {
            int var = order_heap.top().second;
            if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                break;
            }
            order_heap.pop();
        }
    }


    // ============================================================
    // RESTART
    // ============================================================

    bool oooshouldRestart() {
        if (conflicts > restartLimit) {
            restartLimit = (int)(restartLimit * restartFactor);
            LOG("RESTART: conflicts=" << conflicts << " > limit=" << restartLimit);
            return true;
        }
        return false;
    }

    bool shouldRestartv2() {
        if (conflicts > restartLimit) {
            restartLimit = (int)(restartLimit * 1.5);
            // Supprimer les clauses apprises
            for (Clause& c : learntClauses) {
                c.deleted = true;
            }
            learntClauses.clear();
            LOG("RESTART: conflicts=" << conflicts << " > limit=" << restartLimit);
            return true;
        }
        return false;
    }

    bool shouldRestart() {
        if (conflicts > restartLimit) {
            restartLimit = (int)(restartLimit * 1.5);
            // Ne PAS supprimer les clauses apprises !
            // for (Clause& c : learntClauses) { c.deleted = true; }
            // learntClauses.clear();
            LOG("RESTART: conflicts=" << conflicts << " > limit=" << restartLimit);
            return true;
        }
        return false;
    }

    void restart() {
        LOG("=== RESTART ===");
        backjump(0);
        qhead = 0;
        decayActivities();
    }

    // ============================================================
    // SOLVE
    // ============================================================

    bool solveBONNEBASE() {
        LOG("=== SOLVE START ===");
        init();

        /* Assigner les clauses unitaires déguisées (x v x v x)
        for (int i = 0; i < (int)clauses.size(); i++) {
            Clause& c = clauses[i];
            if (c.deleted || c.size() != 3) continue;
            if (c.lits[0] == c.lits[1] && c.lits[1] == c.lits[2]) {
                int lit = c.lits[0];
                int var = abs(lit);
                bool sign = (lit > 0);
                if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                    assignment[var] = sign ? 1 : 0;
                    level[var] = 0;
                    reason[var] = i;
                    trail.push_back(var);
                }
            }
        }*/

        // ✅ Ajouter toutes les clauses unitaires au trail
        for (int i = 0; i < (int)clauses.size(); i++) {
            Clause& c = clauses[i];
            if (c.deleted) continue;
            if (c.size() == 1) {
                int lit = c.lits[0];
                int var = abs(lit);
                bool sign = (lit > 0);
                if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                    assignment[var] = sign ? 1 : 0;
                    level[var] = 0;
                    reason[var] = i;
                    trail.push_back(var);
                    LOG("  unitaire: x" << var << "=" << (sign ? 1 : 0));
                }
            }
        }

        order_heap = priority_queue<pair<double, int>>();
        int heapCount = 0;
        for (int i = 1; i <= getMaxVar(); i++) {
            if (i < (int)assignment.size() && assignment[i] == -1) {
                activity[i] = getMaxVar() - i + 1;
                order_heap.push(make_pair(activity[i], i));
                heapCount++;
            }
        }
        LOG("  heap initialisee avec " << heapCount << " variables");

        if (!propagate()) {
            LOG("UNSAT (init)");
            satisfiable = false;
            return false;
        }

        while (true) {
            bool allSat = true;
            for (Clause& c : clauses) {
                if (!c.deleted && !c.isSatisfied(assignment)) {
                    allSat = false;
                    break;
                }
            }
            if (allSat) {
                LOG("SAT");
                satisfiable = true;
                return true;
            }

            if (shouldRestart()) {
                restart();
                continue;
            }

            int var = chooseVar();
            if (var == -1) {
                // Vérifier s'il reste vraiment des variables non assignées
                bool hasUnassigned = false;
                for (int i = 1; i <= getMaxVar(); i++) {
                    if (i < (int)assignment.size() && assignment[i] == -1) {
                        hasUnassigned = true;
                        // Remettre dans la heap
                        activity[i] = 1.0;
                        order_heap.push(make_pair(1.0, i));
                    }
                }

                if (hasUnassigned) {
                    // Il reste des variables, reconstruire la heap et continuer
                    continue;
                }

                // Vraiment plus de variables, vérifier SAT/UNSAT
                if (!propagate()) {
                    if (decisionLevel == 0) {
                        LOG("UNSAT (propagation finale)");
                        satisfiable = false;
                        return false;
                    }
                    continue;
                }

                bool allSat = true;
                for (Clause& c : clauses) {
                    if (!c.deleted && !c.isSatisfied(assignment)) {
                        allSat = false;
                        break;
                    }
                }

                if (allSat) {
                    LOG("SAT (plus de variables)");
                    satisfiable = true;
                    return true;
                }
                else {
                    LOG("UNSAT (clauses non satisfaites)");
                    satisfiable = false;
                    return false;
                }
            }

            decisions++;
            decisionLevel++;
            trail_lim.push_back(trail.size());
            assign(var, 1, -1);
            LOG("  decision: x" << var << "=1 (level=" << decisionLevel << ")");

            if (!propagate()) {
                if (decisionLevel == 0) {
                    LOG("UNSAT (level=0)");
                    satisfiable = false;
                    return false;
                }
            }
        }
    }

    bool solve() {
        LOG("=== SOLVE START ===");
        init();

        // Ajouter toutes les clauses unitaires au trail
        /*for (int i = 0; i < (int)clauses.size(); i++) {
            Clause& c = clauses[i];
            if (c.deleted) continue;
            if (c.size() == 1) {
                int lit = c.lits[0];
                int var = abs(lit);
                bool sign = (lit > 0);
                if (var >= 1 && var < (int)assignment.size() && assignment[var] == -1) {
                    assignment[var] = sign ? 1 : 0;
                    level[var] = 0;
                    reason[var] = i;
                    trail.push_back(var);
                }
            }
        }*/


        // ✅ Ajouter toutes les clauses unitaires au trail avec vérification de conflit
        for (int i = 0; i < (int)clauses.size(); i++) {
            Clause& c = clauses[i];
            if (c.deleted) continue;
            if (c.size() == 1) {
                int lit = c.lits[0];
                int var = abs(lit);
                bool sign = (lit > 0);
                if (var >= 1 && var < (int)assignment.size()) {
                    if (assignment[var] == -1) {
                        assignment[var] = sign ? 1 : 0;
                        level[var] = 0;
                        reason[var] = i;
                        trail.push_back(var);
                    }
                    else if ((assignment[var] == 1) != sign) {
                        // ✅ Conflit : variable déjà assignée à la valeur opposée
                        LOG("UNSAT: conflit unitaire sur x" << var);
                        satisfiable = false;
                        return false;
                    }
                }
            }
        }

    

        if (!propagate()) {
            LOG("UNSAT (init)");
            satisfiable = false;
            return false;
        }

        while (true) {
            // ✅ SUPPRIME CE SCAN
            // bool allSat = true;
            // for (Clause& c : clauses) { ... }  ← À SUPPRIMER

            if (shouldRestart()) {
                restart();
                continue;
            }

            int var = chooseVar();
            if (var == -1) {
                // ✅ Plus de variables non-assignées → SAT
                if (isSolutionValid()) {
                    LOG("SAT");
                    satisfiable = true;
                    return true;
                }
                else {
                    LOG("UNSAT: solution invalide");
                    satisfiable = false;
                    return false;
                }
            }

            decisions++;
            decisionLevel++;
            trail_lim.push_back(trail.size());
            assign(var, 1, -1);
            LOG("  decision: x" << var << "=1 (level=" << decisionLevel << ")");

            if (!propagate()) {
                if (decisionLevel == 0) {
                    LOG("UNSAT (level=0)");
                    satisfiable = false;
                    return false;
                }
            }
        }
    }

    // ✅ Ajouter cette méthode
    bool isSolutionValid() {
        // Vérifier que toutes les clauses sont satisfaites
        for (Clause& c : clauses) {
            if (!c.deleted && !c.isSatisfied(assignment)) {
                return false;
            }
        }
        return true;
    }

    void exporterDimacs(const string& filename) {
        ofstream fichier(filename);

        int nbVars = getMaxVar();
        int nbClauses = 0;
        for (int i = 0; i < (int)clauses.size(); i++) {
            if (!clauses[i].deleted) nbClauses++;
        }

        fichier << "p cnf " << nbVars << " " << nbClauses << endl;

        for (int i = 0; i < (int)clauses.size(); i++) {
            if (clauses[i].deleted) continue;
            for (int lit : clauses[i].lits) {
                fichier << lit << " ";
            }
            fichier << "0" << endl;
        }

        fichier.close();
        cout << "Exporte dans " << filename << " : " << nbVars << " variables, " << nbClauses << " clauses" << endl;
    }

    // ============================================================
    // AFFICHAGE
    // ============================================================

    void printStats() {
        cout << "=== STATISTIQUES ===" << endl;
        cout << "Variables : " << getMaxVar() << endl;
        cout << "Clauses : " << clauses.size() << endl;
        cout << "Clauses apprises : " << learntClauses.size() << endl;
        cout << "Decisions : " << decisions << endl;
        cout << "Propagations : " << propagations << endl;
        cout << "Conflits : " << conflicts << endl;
    }

    bool isSatisfiable() const { return satisfiable; }
    const vector<int8_t>& getAssignment() const { return assignment; }
};


// ============================================================
// CLASSE ADDITIONNEUR POUR SolverCDCL
// ============================================================

class Additionneur {
private:
    SolverCDCL* solver;
    int* a;
    int* b;
    int* res;
    int* ret;
    int nb_bits;

public:
    // ============================================================
    // CONSTRUCTEURS
    // ============================================================

    // Constructeur : crée toutes les variables
    Additionneur(SolverCDCL* s, int bits) {
        this->solver = s;
        this->nb_bits = bits;

        this->a = new int[bits];
        this->b = new int[bits];
        this->res = new int[bits];
        this->ret = new int[bits + 1];

        for (int i = 0; i < bits; i += 1) {
            this->a[i] = this->solver->getNextVar();
            this->b[i] = this->solver->getNextVar();
            this->res[i] = this->solver->getNextVar();
            this->ret[i] = this->solver->getNextVar();
        }
        this->ret[bits] = this->solver->getNextVar();

        // Retenue initiale = 0
        this->solver->Add1Sat(this->ret[0], 0);


    }

    // Constructeur : A est déjà défini
    Additionneur(SolverCDCL* s, int* pa, int bits) {
        this->solver = s;
        this->nb_bits = bits;

        this->a = new int[bits];
        this->b = new int[bits];
        this->res = new int[bits];
        this->ret = new int[bits + 1];

        for (int i = 0; i < bits; i += 1) {
            this->a[i] = pa[i];
            this->b[i] = this->solver->getNextVar();
            this->res[i] = this->solver->getNextVar();
            this->ret[i] = this->solver->getNextVar();
        }
        this->ret[bits] = this->solver->getNextVar();

        this->solver->Add1Sat(this->ret[0], 0);
        
    }

    // Constructeur : A et B sont déjà définis
    Additionneur(SolverCDCL* s, int* pa, int* pb, int bits) {
        this->solver = s;
        this->nb_bits = bits;

        this->a = new int[bits];
        this->b = new int[bits];
        this->res = new int[bits];
        this->ret = new int[bits + 1];

        for (int i = 0; i < bits; i += 1) {
            this->a[i] = pa[i];
            this->b[i] = pb[i];
            this->res[i] = this->solver->getNextVar();
            this->ret[i] = this->solver->getNextVar();
        }
        this->ret[bits] = this->solver->getNextVar();

        this->solver->Add1Sat(this->ret[0], 0);
        
    }

    // ============================================================
    // DESTRUCTEUR
    // ============================================================

    ~Additionneur() {
        delete[] this->a;
        delete[] this->b;
        delete[] this->res;
        delete[] this->ret;
    }

    // ============================================================
    // MÉTHODES
    // ============================================================

    void build() {
        for (int i = 0; i < this->nb_bits; i += 1) {
            this->solver->AddAddBin(
                this->a[i],
                this->b[i],
                this->res[i],
                this->ret[i],
                this->ret[i + 1]
            );
        }
    }

    void ooosetA(int value) {
        for (int i = 0; i < this->nb_bits; i += 1) {
            int bit = (value >> i) & 1;
            this->solver->Add1Sat(this->a[i], bit);
        }
    }

    void setA(int value) {
        cout << "setA(" << value << ")" << endl;
        for (int i = 0; i < this->nb_bits; i += 1) {
            int bit = (value >> i) & 1;
            cout << "  a[" << i << "] = " << bit << " (var " << this->a[i] << ")" << endl;
            this->solver->Add1Sat(this->a[i], bit);
        }
    }

    void setB(int value) {
        for (int i = 0; i < this->nb_bits; i += 1) {
            int bit = (value >> i) & 1;
            this->solver->Add1Sat(this->b[i], bit);
        }
    }

    void setAFrom(int* source) {
        for (int i = 0; i < this->nb_bits; i += 1) {
            if (source[i] >= 0) {
                // a = source
                this->solver->Add2Sat(this->a[i], source[i], 0, 1);
                this->solver->Add2Sat(this->a[i], source[i], 1, 0);
            }
            else {
                // a = 0
                this->solver->Add1Sat(this->a[i], 0);
            }
        }
    }

    void setBFrom(int* source) {
        for (int i = 0; i < this->nb_bits; i += 1) {
            if (source[i] >= 0) {
                // b = source
                this->solver->Add2Sat(this->b[i], source[i], 0, 1);
                this->solver->Add2Sat(this->b[i], source[i], 1, 0);
            }
            else {
                // b = 0
                this->solver->Add1Sat(this->b[i], 0);
            }
        }
    }

    void setAReset() {
        for (int i = 0; i < this->nb_bits; i += 1) {
            this->solver->Add1Sat(this->a[i], 0);
        }
    }

    void setBReset() {
        for (int i = 0; i < this->nb_bits; i += 1) {
            this->solver->Add1Sat(this->b[i], 0);
        }
    }

    // ============================================================
    // GETTERS
    // ============================================================

    int getNBits() const { return this->nb_bits; }
    int* getA() const { return this->a; }
    int* getB() const { return this->b; }
    int* getRes() const { return this->res; }
    int* getRet() const { return this->ret; }

    // ============================================================
    // AFFICHAGE
    // ============================================================

    void printResult(SolverCDCL* solver) {
        int* ans = new int[this->nb_bits];
        const vector<int8_t>& assign = solver->getAssignment();

        for (int i = 0; i < this->nb_bits; i += 1) {
            ans[i] = assign[this->res[i]];
        }

        for (int i = this->nb_bits - 1; i >= 0; i -= 1) {
            cout << ans[i];
        }
        cout << endl;

        delete[] ans;
    }

    int getResult(SolverCDCL* solver) {
        int* ans = new int[this->nb_bits];
        const vector<int8_t>& assign = solver->getAssignment();

        for (int i = 0; i < this->nb_bits; i += 1) {
            if (this->res[i] >= 0 && this->res[i] < (int)assign.size()) {
                ans[i] = assign[this->res[i]];
            }
            else {
                ans[i] = 0;
            }
        }

        int result = 0;
        for (int i = this->nb_bits - 1; i >= 0; i -= 1) {
            if (ans[i] == 1) {
                result += (1 << i);
            }
        }

        delete[] ans;
        return result;
    }
};

// ============================================================
// TSP N VILLES AVEC SolverCDCL
// ============================================================

// ============================================================
// calculerDistanceMultiple adapté pour SolverCDCL
// ============================================================
void calculerDistanceMultiple(
    SolverCDCL* solver,
    int add_count,
    int nb_bits,
    int** dist_pos,
    int* result
) {
    if (add_count == 0) {
        for (int bit = 0; bit < nb_bits; bit += 1) {
            //result[bit] = solver->getNextVar();
            solver->Add1Sat(result[bit], 0);
        }
        return;
    }

    if (add_count == 1) {
        for (int bit = 0; bit < nb_bits; bit += 1) {
            //result[bit] = solver->getNextVar();
            // Copie : result = dist_pos[0]
            solver->Add2Sat(result[bit], dist_pos[0][bit], 0, 1);
            solver->Add2Sat(result[bit], dist_pos[0][bit], 1, 0);
        }
        return;
    }

    // Créer zéro
    int* zero = new int[nb_bits];
    for (int bit = 0; bit < nb_bits; bit += 1) {
        zero[bit] = solver->getNextVar();
        solver->Add1Sat(zero[bit], 0);
    }

    // Premier additionneur : 0 + dist_pos[0]
    Additionneur add0(solver, zero, dist_pos[0], nb_bits);
    add0.build();
    int* current_res = add0.getRes();

    // Pas de delete pour Additionneur car getRes() retourne un pointeur membre
    // On garde une copie des résultats
    int* saved_res = new int[nb_bits];
    for (int bit = 0; bit < nb_bits; bit += 1) {
        saved_res[bit] = current_res[bit];
    }

    // Additions suivantes
    for (int i = 1; i < add_count; i += 1) {
        int* old_res = saved_res;

        Additionneur add(solver, old_res, dist_pos[i], nb_bits);
        add.build();
        current_res = add.getRes();

        saved_res = new int[nb_bits];
        for (int bit = 0; bit < nb_bits; bit += 1) {
            saved_res[bit] = current_res[bit];
        }
    }

    // Copie du résultat final
    for (int bit = 0; bit < nb_bits; bit += 1) {
        //result[bit] = solver->getNextVar();
        solver->Add2Sat(result[bit], saved_res[bit], 0, 1);
        solver->Add2Sat(result[bit], saved_res[bit], 1, 0);
    }

    //delete[] zero;
    // Note : saved_res fuit, mais c'est un exemple
}

void calculerDistanceMultipleooo(
    SolverCDCL* solver,
    int add_count,
    int nb_bits,
    int** dist_pos,
    int* result
) {
    // Créer les variables de résultat
    for (int bit = 0; bit < nb_bits; bit += 1) {
        result[bit] = solver->getNextVar();
    }

    // Initialiser result = 0
    int* current = new int[nb_bits];
    for (int bit = 0; bit < nb_bits; bit += 1) {
        current[bit] = solver->getNextVar();
        solver->Add1Sat(current[bit], 0);
    }

    // Additionner les distances
    for (int p = 0; p < add_count; p += 1) {
        int* next = new int[nb_bits];
        for (int bit = 0; bit < nb_bits; bit += 1) {
            next[bit] = solver->getNextVar();
        }

        // Additionner current + dist_pos[p] -> next
        int carry = solver->getNextVar();
        solver->Add1Sat(carry, 0);  // retenue initiale = 0

        for (int bit = 0; bit < nb_bits; bit += 1) {
            int carry_out = solver->getNextVar();
            solver->AddAddBin(current[bit], dist_pos[p][bit], next[bit], carry, carry_out);
            carry = carry_out;
        }

        delete[] current;
        current = next;
    }

    // Copier current -> result
    for (int bit = 0; bit < nb_bits; bit += 1) {
        solver->Add2Sat(result[bit], current[bit], 0, 1);
        solver->Add2Sat(result[bit], current[bit], 1, 0);
    }

    delete[] current;
}


void TSP2N() {
    cout << " === TSP N VILLES AVEC SolverCDCL ===" << endl;

    const int NB_CITY = 40;
    const int NB_BITS = 7;
    const int MAX_DIST = 50;  // Distance maximale

    // ============================================================
    // 1. CRÉER LE SOLVEUR
    // ============================================================
    SolverCDCL solver;

    // ============================================================
    // 2. VARIABLES
    // ============================================================
    int x[NB_CITY][NB_CITY];
    for (int ville = 0; ville < NB_CITY; ville += 1) {
        for (int pos = 0; pos < NB_CITY; pos += 1) {
            x[ville][pos] = solver.getNextVar();
        }
    }

    int t[NB_CITY][NB_CITY][NB_CITY];
    for (int i = 0; i < NB_CITY; i += 1) {
        for (int j = 0; j < NB_CITY; j += 1) {
            for (int p = 0; p < NB_CITY; p += 1) {
                t[i][j][p] = -1;
            }
        }
    }
    for (int i = 0; i < NB_CITY; i += 1) {
        for (int j = 0; j < NB_CITY; j += 1) {
            if (i == j) continue;
            for (int p = 0; p < NB_CITY; p += 1) {
                t[i][j][p] = solver.getNextVar();
            }
        }
    }

    // ============================================================
    // 3. SIGNE POUR AddKSat
    // ============================================================
    int signs[NB_CITY];
    for (int j = 0; j < NB_CITY; ++j) {
        signs[j] = 1;
    }

    // ============================================================
    // 4. CONTRAINTES : Chaque ville à exactement 1 position
    // ============================================================
    for (int ville = 0; ville < NB_CITY; ville += 1) {
        //solver.AddKSat(x[ville], signs, NB_CITY);
        solver.AddKSat(x[ville], signs, NB_CITY);
        for (int i = 0; i < NB_CITY; ++i) {
            for (int j = 0; j < NB_CITY; ++j) {
                if (i == j) continue;
                //solver.Add2Sat(x[ville][i], x[ville][j], 0, 0);
                // Au lieu de solver.Add2Sat(x[ville][i], x[ville][j], 0, 0);
                solver.addBinaryClause(x[ville][i], x[ville][j], 0, 0);
            }
        }
    }

    // ============================================================
    // 5. CONTRAINTES : Chaque position a exactement 1 ville
    // ============================================================
    for (int pos = 0; pos < NB_CITY; pos += 1) {
        int cities[NB_CITY];
        for (int j = 0; j < NB_CITY; ++j) {
            cities[j] = x[j][pos];
        }
        //solver.AddKSat(cities, signs, NB_CITY);
        solver.AddKSat(cities, signs, NB_CITY);
        for (int i = 0; i < NB_CITY ; ++i) {
            for (int j =0; j < NB_CITY; ++j) {
                if (i == j) continue;
                //solver.Add2Sat(x[i][pos], x[j][pos], 0, 0);
                solver.addBinaryClause(x[i][pos], x[j][pos], 0, 0);
            }
        }
    }

  

    // ============================================================
    // 6. DÉPART FORCÉ : A en position 0
    // ============================================================
    //solver.Add1Sat(x[0][0], 0);
    //solver.Add1Sat(x[1][1], 0);
    //solver.Add1Sat(x[2][2], 0);
    //solver.Add1Sat(x[3][3], 0);

    // ============================================================
    // 7. TRANSITIONS
    // ============================================================
    for (int i = 0; i < NB_CITY; i += 1) {
        for (int j = 0; j < NB_CITY; j += 1) {
            if (i == j) continue;
            for (int p = 0; p < NB_CITY; p += 1) {
                int next_p = (p + 1) % NB_CITY;
                int trans = t[i][j][p];
                /*solver.Add2Sat(trans, x[i][p], 0, 1);
                solver.Add2Sat(trans, x[j][next_p], 0, 1);
                //solver.addBinaryClause(trans, x[i][p], 0, 1);
                //solver.addBinaryClause(trans, x[j][next_p], 0, 1);*/
                solver.Add3Sat(x[i][p], x[j][next_p], trans, 0, 0, 1);
                
                // trans → x[i][p]  (¬trans v x[i][p])
                solver.addBinaryClause(trans, x[i][p], 0, 1);
                // trans → x[j][next_p]  (¬trans v x[j][next_p])
                solver.addBinaryClause(trans, x[j][next_p], 0, 1);
                // x[i][p] ∧ x[j][next_p] → trans  (¬x[i][p] v ¬x[j][next_p] v trans)
                //solver.Add3Sat(x[i][p], x[j][next_p], trans, 0, 0, 1);
            }
        }
    }

    // ============================================================
    // 8. UNE TRANSITION PAR POSITION
    // ============================================================
    const int NB_TRANS = NB_CITY * (NB_CITY - 1);
    int trans_signs[NB_TRANS];
    for (int i = 0; i < NB_TRANS; ++i) trans_signs[i] = 1;

    for (int p = 0; p < NB_CITY; p += 1) {
        int tr[NB_TRANS];
        int nb = 0;
        for (int i = 0; i < NB_CITY; i += 1) {
            for (int j = 0; j < NB_CITY; j += 1) {
                if (i == j) continue;
                tr[nb++] = t[i][j][p];
            }
        }
  
        solver.AddKSat(tr, trans_signs, NB_TRANS);
        for (int a = 0; a < NB_TRANS; a += 1) {
            for (int b = 0; b < NB_TRANS; b += 1) {
                if (a == b)continue;
                solver.addBinaryClause(tr[a], tr[b], 0, 0);
                //solver.addBinaryClause(tr[a], tr[b], 0, 0);
            }
        }
    }


    // ============================================================
    // 9. MATRICE DES DISTANCES
    // ============================================================
    int d[4][4] = {
        {0, 10, 8, 12},
        {10, 0, 14, 9},
        {8, 14, 0, 13},
        {12, 9, 13, 0}
    };

    /*int d[NB_CITY][NB_CITY];

    for (int i = 0; i < NB_CITY; i += 1) {
        for (int j = i; j < NB_CITY; j += 1) {
            if (i == j) {
                d[i][j] = 0;
            }
            else {
                int nd = rand() % 15;
                d[i][j] = nd;
                d[j][i] = nd;
            }
        }

    }*/

    
    // ============================================================
    // 10. DISTANCE DE CHAQUE TRANSITION
    // ============================================================
    /*int dist_pos[NB_CITY][NB_BITS];
    for (int p = 0; p < NB_CITY; p += 1) {
        for (int bit = 0; bit < NB_BITS; bit += 1) {
            dist_pos[p][bit] = solver.getNextVar();
        }
    }

    for (int p = 0; p < NB_CITY; p += 1) {
        for (int i = 0; i < NB_CITY; i += 1) {
            for (int j = 0; j < NB_CITY; j += 1) {
                if (i == j) continue;
                int trans = t[i][j][p];
                int value = d[i][j];
                for (int bit = 0; bit < NB_BITS; bit += 1) {
                    int val_bit = (value >> bit) & 1;
                    solver.addBinaryClause(trans, dist_pos[p][bit], 0, val_bit);
                }
            }
        }
    }
    
    // ============================================================
    // 11. DISTANCE FINALE
    // ============================================================
    int dist_final[NB_BITS];
    for (int bit = 0; bit < NB_BITS; bit += 1) {
        dist_final[bit] = solver.getNextVar();
    }

    // Convertir dist_pos pour la fonction
    int* dist_pos_ptr[NB_CITY];
    for (int p = 0; p < NB_CITY; p += 1) {
        dist_pos_ptr[p] = dist_pos[p];
        //cout << "d=" << dist_pos_ptr[p] << ", " << dist_pos[p] << endl;
    }

    calculerDistanceMultiple(&solver, NB_CITY, NB_BITS, dist_pos_ptr, dist_final);

    // ============================================================
    // 12. CONTRAINTE DISTANCE < MAX_DIST
    // ============================================================
    for (int val = MAX_DIST; val < 128; val += 1) {

        int clause_vars[NB_BITS];
        int clause_signs[NB_BITS];
        for (int bit = 0; bit < NB_BITS; bit += 1) {
            int bit_val = (val >> bit) & 1;
            clause_vars[bit] = dist_final[bit];
            clause_signs[bit] = (bit_val == 1) ? 0 : 1;
  
        }
        solver.AddKSat(clause_vars, clause_signs, NB_BITS);
    }
    */
    
    // ============================================================
    // 13. RÉSOUDRE
    // ============================================================
    cout << "Solver start" << endl;
    auto start = chrono::high_resolution_clock::now();
    bool result = solver.solve();
    auto end = chrono::high_resolution_clock::now();
    cout << "vars=" << solver.getMaxVar() << endl;

    for (int p = 0; p < NB_CITY; p++) {
        int count = 0;

        for (int ville = 0; ville < NB_CITY; ville++) {
            int v = solver.getAssignment()[x[ville][p]];

            if (v == 1) {
                cout << "p=" << p << " ville=" << ville << endl;
                count++;
            }
        }

        cout << "Position " << p << " : " << count << " villes" << endl;
    }

    for (int p = 0; p < NB_CITY; p++) {
        int count = 0;

        for (int i = 0; i < NB_CITY; i++) {
            for (int j = 0; j < NB_CITY; j++) {
                if (i == j) continue;

                if (solver.getAssignment()[t[i][j][p]] == 1) {
                    cout << "Transition pos " << p
                        << " : " << i << " -> " << j << endl;
                    count++;
                }
            }
        }

        cout << "Transitions pos " << p
            << " = " << count << endl;
    }

    // ============================================================
    // 14. AFFICHER LA SOLUTION
    // ============================================================
    if (result) {
        cout << "Solution trouvee !" << endl;
        for (int p = 0; p < NB_CITY; p += 1) {
            for (int ville = 0; ville < NB_CITY; ville += 1) {
                int val = solver.getAssignment()[x[ville][p]];
                if (val == 1) {
                    char villes[12] = { 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L' };
                    cout << "Pos " << p << " : " << villes[ville] << endl;
                }
            }
        }
        int dist_val = 0;
        for (int i = 0; i < NB_BITS; i += 1) {
            int val = 0;// solver.getAssignment()[dist_final[i]];
            cout << val;
            if (val < 1) val = 0;
            dist_val += val * (1 << i);
        }
        cout << endl;
        cout << "Distance : " << dist_val << endl;
    }
    else {
        cout << "Aucune solution." << endl;
    }
    solver.printStats();

    auto duration = chrono::duration_cast<chrono::milliseconds>(end - start);

    cout << "Temps d'exécution : " << duration.count() << " ms" << endl;
    // ou en secondes
    cout << "Temps d'exécution : " << duration.count() / 1000.0 << " s" << endl;

    //solver.exporterDimacs("tsp_444evovilles.cnf");

}

void TSP_sans_distance() {
    cout << " === TSP 4 VILLES SANS DISTANCE ===" << endl;

    const int NB_CITY = 4;
    SolverCDCL solver;

    // Variables de position : x[ville][pos]
    int x[NB_CITY][NB_CITY];
    for (int ville = 0; ville < NB_CITY; ville += 1) {
        for (int pos = 0; pos < NB_CITY; pos += 1) {
            x[ville][pos] = solver.getNextVar();
        }
    }

    // ============================================================
    // CONTRAINTES DE POSITION
    // ============================================================

    int signs4[4] = { 1, 1, 1, 1 };

    // Chaque ville a exactement 1 position
    for (int ville = 0; ville < NB_CITY; ville += 1) {
        // Au moins une position
        int vars[4] = { x[ville][0], x[ville][1], x[ville][2], x[ville][3] };
        solver.AddKSat(vars, signs4, 4);
        // Remplacer AddKSat(vars, signs4, 4) par :
        //solver.Add3Sat(vars[0], vars[1], vars[2], 1, 1, 1);
        //solver.Add2Sat(vars[2], vars[3], 1, 1);
        // Au plus une position (paires)
        for (int i = 0; i < NB_CITY; i += 1) {
            for (int j = i + 1; j < NB_CITY; j += 1) {
                solver.Add2Sat(x[ville][i], x[ville][j], 0, 0);
            }
        }
    }

    // Chaque position a exactement 1 ville
    for (int pos = 0; pos < NB_CITY; pos += 1) {
        // Au moins une ville
        int vars[4] = { x[0][pos], x[1][pos], x[2][pos], x[3][pos] };
        solver.AddKSat(vars, signs4, 4);
        // Remplacer AddKSat(vars, signs4, 4) par :
        //solver.Add3Sat(vars[0], vars[1], vars[2], 1, 1, 1);
       // solver.Add2Sat(vars[2], vars[3], 1, 1);
        // Au plus une ville (paires)
        for (int i = 0; i < NB_CITY; i += 1) {
            for (int j = i + 1; j < NB_CITY; j += 1) {
                solver.Add2Sat(x[i][pos], x[j][pos], 0, 0);
            }
        }
    }

    // Départ : ville A en position 0
    solver.Add1Sat(x[0][0], 1);

    // ============================================================
    // RÉSOUDRE
    // ============================================================
    cout << "Solver start" << endl;
    cout << "vars=" << solver.getMaxVar() << endl;
    bool result = solver.solve();
    

    if (result) {
        cout << "Solution trouvee !" << endl;
        cout << "Tour : ";
        for (int p = 0; p < NB_CITY; p += 1) {
            for (int ville = 0; ville < NB_CITY; ville += 1) {
                if (solver.getAssignment()[x[ville][p]] == 1) {
                    cout << (char)('A' + ville);
                    if (p < NB_CITY - 1) cout << " -> ";
                }
            }
        }
        cout << endl;
    }
    else {
        cout << "Aucune solution." << endl;
    }
    solver.printStats();
}

//ADD
void ADD2NOMBRES() {
    SolverCDCL solver;

    // Créer un additionneur 32 bits
    Additionneur add(&solver, 32);
    add.build();

    // Forcer les valeurs
    int _a = 213456789;
    int _b = 123456789;

    add.setA(_a);
    add.setB(_b);

    cout << "Clauses :" << endl;
    vector<Clause> clauses = solver.getClauses();
    for (auto& c : solver.getClauses()) {
        c.print();
    }


    cout << "A = " << _a << endl;
    cout << "B = " << _b << endl;

    // Résoudre
    bool result = solver.solve();

    if (result) {
        cout << "Resultat binaire : ";
        add.printResult(&solver);

        int resultat = add.getResult(&solver);
        cout << "Resultat decimal : " << resultat << endl;
        cout << "Verification : " << _a << " + " << _b << " = " << _a + _b << endl;
    }
    else {
        cout << "Aucune solution." << endl;
    }

    solver.printStats();

}

void testSimple() {
    SolverCDCL solver;

    // x = 1
    int x = solver.getNextVar();
    solver.Add1Sat(x, 1);

    // x = 0 (conflit)
    solver.Add1Sat(x, 0);

    cout << "Clauses :" << endl;
    vector<Clause> clauses = solver.getClauses();
    for (auto& c : solver.getClauses()) {
        c.print();
    }

    bool result = solver.solve();

    cout << "Résultat : " << (result ? "SAT" : "UNSAT") << endl;
    solver.printStats();
}

void test_TSP_Add2Sat() {
    SolverCDCL solver;

    int x0 = solver.getNextVar();
    int x1 = solver.getNextVar();

    // x0 et x1 ne peuvent pas être vrais ensemble
    solver.Add2Sat(x0, x1, 0, 0);
    solver.Add1Sat(x0, 1);

    bool result = solver.solve();
    cout << "Resultat: " << (result ? "SAT" : "UNSAT") << endl;
    if (result) {
        cout << "x0=" << (int)solver.getAssignment()[x0] << endl;
        cout << "x1=" << (int)solver.getAssignment()[x1] << endl;
    }
}

void test_AddKSat_4() {
    SolverCDCL solver;

    int v[4];
    for (int i = 0; i < 4; i++) v[i] = solver.getNextVar();

    int signs[4] = { 1, 1, 1, 1 };
    solver.AddKSat(v, signs, 4);

    // Forcer v[0] = 1 pour que ce soit SAT
    solver.Add1Sat(v[0], 1);

    bool result = solver.solve();
    cout << "Resultat: " << (result ? "SAT" : "UNSAT") << endl;
}

void testAdditionneurSimple() {
    SolverCDCL solver;

    // Tester XOR
    int a = solver.getNextVar();
    int b = solver.getNextVar();
    int c = solver.getNextVar();

    solver.Add1Sat(a, 1);  // a = 1
    solver.Add1Sat(b, 0);  // b = 0
    solver.AddXor(a, b, c); // c = a XOR b

    bool result = solver.solve();
    if (result) {
        cout << "1 XOR 0 = " << (int)solver.getAssignment()[c] << endl;
        cout << "Résultat: SAT" << endl;
    }
    else {
        cout << "Résultat: UNSAT" << endl;
    }
}

void testAdditionneur4Bits() {
    cout << "=== TEST ADDITIONNEUR 4 BITS ===" << endl;
    SolverCDCL solver;

    Additionneur add(&solver, 4);
    add.build();

    // 5 + 3 = 8
    add.setA(5);
    add.setB(3);

    cout << "A = 5 (0101)" << endl;
    cout << "B = 3 (0011)" << endl;

    bool result = solver.solve();

    if (result) {
        int res = add.getResult(&solver);
        cout << "Résultat = " << res << " (binaire: ";
        for (int i = 3; i >= 0; i--) {
            cout << (int)solver.getAssignment()[add.getRes()[i]];
        }
        cout << ")" << endl;
        cout << "Vérification: 5 + 3 = " << 5 + 3 << endl;
    }
    else {
        cout << "UNSAT" << endl;
    }
    solver.printStats();
}

// ============================================================
// FONCTION MAIN DE TEST
// ============================================================

int main() {
    srand(time(nullptr));
    TSP2N();
    //test_AddKSat_4();
    //TSP_sans_distance();
    //testAdditionneur4Bits();
    //ADD2NOMBRES();
    //testSimple();
    //test_TSP_Add2Sat();

    return 0;
}