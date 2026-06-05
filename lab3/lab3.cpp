/*
  C++17, один файл для двух классических задач ИИ (очищенная версия, комментарии на русском):
  1) «Волк – Коза – Капуста» (BFS, DFS, IDS) с поддержкой множественных волков/коз/капуст.
  2) «Уголки» (Corners) — A*, DFS/IDS, эвристика через Венгерский алгоритм.

  Сборка:
    g++ -std=gnu++17 -O2 -pipe -static -s -o puzzles puzzles.cpp

  Запуск:
    # Задача 1 (ВКК)
    ./puzzles wgc --wolves 1 --goats 1 --cabbages 1 --algo bfs
    ./puzzles wgc --wolves 2 --goats 1 --cabbages 1 --algo ids
    ./puzzles wgc --wolves 1 --goats 1 --cabbages 1 --algo dfs --limit 64

    # Задача 2 (Уголки)
    ./puzzles corners --rows 8 --cols 8 --rectR 3 --rectC 4 --algo astar
    ./puzzles corners --rows 6 --cols 6 --rectR 2 --rectC 3 --algo ids
*/

#include <algorithm>
#include <cmath>
#include <functional>
#include <iostream>
#include <queue>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>


using namespace std;

/******************** Общий контейнер узла поиска ********************/

template<class State>
struct Node {
    State s;                 // состояние
    int g = 0;               // цена пути / глубина
    int h = 0;               // эвристика (для A*)
    int f() const { return g + h; }
    int parent = -1;         // индекс родителя в векторе nodes
    string action;           // человеко-читаемое описание действия
};

/******************** Задача 1: Волк – Коза – Капуста ********************/

// Состояние хранит сторону фермера и количества объектов на ЛЕВОМ берегу
struct WGCState {
    int farmer = 0;      // 0 — левый (старт), 1 — правый (цель)
    int wL = 1, gL = 1, cL = 1; // волки, козы, капуста на ЛЕВОМ берегу

    WGCState(int w, int g, int c) { wL = w; gL = g; cL = c; farmer = 0; }
    WGCState() {}

    bool operator==(const WGCState& o) const {
        return farmer == o.farmer && wL == o.wL && gL == o.gL && cL == o.cL;
    }
};

// Хешер для использования в unordered_*
struct WGCStateHasher {
    size_t operator()(WGCState const& s) const noexcept {
        return ((s.farmer * 131 + s.wL) * 131 + s.gL) * 131 + s.cL;
    }
};

// Проверка безопасности на одном берегу
static inline bool safe_bank(int wolves, int goats, int cabbages, bool farmer_on_bank) {
    // Если фермера нет и есть несовместимые пары — опасно
    if (!farmer_on_bank) {
        if (wolves > 0 && goats > 0) return false;    // волки съедят коз
        if (goats > 0 && cabbages > 0) return false;  // козы съедят капусту
    }
    return true;
}

// Глобальная проверка безопасности для состояния
static inline bool safe(const WGCState& s, int Wtot, int Gtot, int Ctot) {
    int wR = Wtot - s.wL;
    int gR = Gtot - s.gL;
    int cR = Ctot - s.cL;
    bool farmerLeft = (s.farmer == 0);
    bool farmerRight = !farmerLeft;
    return safe_bank(s.wL, s.gL, s.cL, farmerLeft) && safe_bank(wR, gR, cR, farmerRight);
}

// Постановка задачи ВКК: генерация соседей и цель
struct WGCProblem {
    int Wtot, Gtot, Ctot;     // суммарные количества
    WGCState start, goal;     // старт/цель

    WGCProblem(int W, int G, int C) : Wtot(W), Gtot(G), Ctot(C) {
        start = WGCState(W, G, C);
        goal = WGCState(0, 0, 0); 
        goal.farmer = 1; // всё на правом берегу, фермер справа
    }

    // Порождаем допустимые переходы (лодка перевозит либо никого, либо ровно один объект)
    vector<pair<WGCState, string>> neighbors(const WGCState& s) const {
        vector<pair<WGCState, string>> res;
        int dir = (s.farmer == 0) ? +1 : -1; // +1 — в право (уменьшаем левый берег), -1 — в лево
        auto try_add = [&](WGCState t, string act) { 
            if (safe(t, Wtot, Gtot, Ctot)) 
                res.emplace_back(t, act); 
            };
        // Фермер один
        {
            WGCState t = s; 
            t.farmer ^= 1;
            try_add(t, "Farmer alone");
        }
        // С фермером один объект, если он есть на соответствующем берегу
        if (dir == +1 && s.wL > 0) { 
            WGCState t = s;
            t.wL--;
            t.farmer ^= 1;
            try_add(t, "Farmer + Wolf"); 
        }
        if (dir == -1 && (Wtot - s.wL) > 0) {
            WGCState t = s;
            t.wL++;
            t.farmer ^= 1;
            try_add(t, "Farmer + Wolf");
        }
        if (dir == +1 && s.gL > 0) { 
            WGCState t = s;
            t.gL--; 
            t.farmer ^= 1;
            try_add(t, "Farmer + Goat");
        }
        if (dir == -1 && (Gtot - s.gL) > 0) {
            WGCState t = s;
            t.gL++;
            t.farmer ^= 1;
            try_add(t, "Farmer + Goat");
        }
        if (dir == +1 && s.cL > 0) { 
            WGCState t = s; 
            t.cL--; 
            t.farmer ^= 1; 
            try_add(t, "Farmer + Cabbage"); 
        }
        if (dir == -1 && (Ctot - s.cL) > 0) {
            WGCState t = s; 
            t.cL++; 
            t.farmer ^= 1; 
            try_add(t, "Farmer + Cabbage");
        }
        return res;
    }

    bool is_goal(const WGCState& s) const { return s.farmer == 1 && s.wL == 0 && s.gL == 0 && s.cL == 0; }
};

// ---- BFS для ВКК ----
struct WGC_BFS_Result {
    bool found = false; 
    int goal_index = -1;
    vector<Node<WGCState>> nodes;
    unordered_map<WGCState, int, WGCStateHasher> index_of;
};

static WGC_BFS_Result WGC_BFS(const WGCProblem& P) {
    WGC_BFS_Result R; 
    R.nodes.push_back({ P.start,0,0,-1,"START" });
    R.index_of[P.start] = 0; 
    queue<int> q; 
    q.push(0);
    while (!q.empty()) {
        int i = q.front(); q.pop();
        if (P.is_goal(R.nodes[i].s)) { 
            R.found = true; 
            R.goal_index = i;
            return R; 
        }
        for (auto [ns, act] : P.neighbors(R.nodes[i].s))
            if (!R.index_of.count(ns)) {
                int j = (int)R.nodes.size(); 
                R.index_of[ns] = j;
                R.nodes.push_back({ ns,R.nodes[i].g + 1,0,i,act });
                q.push(j);
            }
    }
    return R; // решения нет в пределах просмотренного пространства
}

// ---- DFS (с ограничением глубины) для ВКК ----
struct WGC_DFS_Result { 
    bool found = false; 
    int goal_index = -1;
    vector<Node<WGCState>> nodes; 
};

static bool WGC_DFS_rec(const WGCProblem& P, const WGCState& s, int depth, int limit,
    unordered_set<WGCState, WGCStateHasher>& onstack,
    WGC_DFS_Result& R, int parent, const string& action) {
    int idx = (int)R.nodes.size();
    R.nodes.push_back({ s,depth,0,parent,action });
    if (P.is_goal(s)) { 
        R.found = true; 
        R.goal_index = idx; 
        return true; 
    }
    if (depth == limit) return false;
    onstack.insert(s);
    for (auto [ns, act] : P.neighbors(s)) 
        if (!onstack.count(ns)) {
            if (WGC_DFS_rec(P, ns, depth + 1, limit, onstack, R, idx, act))
                return true;
    }
    onstack.erase(s);
    return false;
}

static WGC_DFS_Result WGC_DFS(const WGCProblem& P, int depth_limit) {
    WGC_DFS_Result R; 
    unordered_set<WGCState, WGCStateHasher> onstack;
    WGC_DFS_rec(P, P.start, 0, depth_limit, onstack, R, -1, "START");
    return R;
}

// ---- IDS (итеративное углубление) для ВКК ----
static WGC_DFS_Result WGC_IDS(const WGCProblem& P, int max_depth = 64) {
    for (int d = 0; d <= max_depth; ++d) {
        auto R = WGC_DFS(P, d);
        if (R.found) 
            return R; 
    }
    return {}; // не найдено до max_depth
}

// Восстановление пути для ВКК
static vector<int> reconstruct_path(const vector<Node<WGCState>>& nodes, int goal_index) {
    vector<int> path; 
    for (int i = goal_index; i != -1; i = nodes[i].parent) 
        path.push_back(i); 
    reverse(path.begin(), path.end()); 
    return path;
}

/******************** Задача 2: «Уголки» (Corners) ********************/

struct BoardPos { int r, c; };

// Состояние-доска, как строка (R*C символов): '0' — пусто, '1' — белая, '2' — чёрная
struct CornersState { 
    int R = 8, C = 8; 
    string cells; 
    bool operator==(const CornersState& o) const { return cells == o.cells; } 
};
struct CornersHasher { 
    size_t operator()(const CornersState& s) const noexcept { return hash<string>{}(s.cells); }
};
static inline int idx(int r, int c, int C) { return r * C + c; }

// Формируем старт/цель и генерируем соседние состояния (шаг/одинарный прыжок по ортогонали)
struct CornersProblem {
    int R, C, rectR, rectC; CornersState start, goal;
    CornersProblem(int R_, int C_, int rectR_, int rectC_) :R(R_), C(C_), rectR(rectR_), rectC(rectC_) {
        start.R = R; 
        start.C = C; 
        goal.R = R; 
        goal.C = C; 
        start.cells.assign(R * C, '0');
        goal.cells.assign(R * C, '0');
        // Белые — прямоугольник слева-сверху; чёрные — симметрично справа-снизу
        for (int r = 0; r < rectR; r++) 
            for (int c = 0; c < rectC; c++) {
                start.cells[idx(r, c, C)] = '1'; 
                goal.cells[idx(r, c, C)] = '2'; 
            }
        for (int r = R - rectR; r < R; r++) 
            for (int c = C - rectC; c < C; c++) { 
                start.cells[idx(r, c, C)] = '2'; 
                goal.cells[idx(r, c, C)] = '1'; 
            }
    }
    vector<pair<CornersState, string>> neighbors(const CornersState& s) const {
        static const int dr[4] = { -1,1,0,0 };
        static const int dc[4] = { 0,0,-1,1 };
        vector<pair<CornersState, string>> res;
        for (int r = 0; r < R; r++) 
            for (int c = 0; c < C; c++) {
            char piece = s.cells[idx(r, c, C)];
            if (piece == '0') continue;
                for (int k = 0; k < 4; k++) {
                    int r1 = r + dr[k], c1 = c + dc[k];
                    if (r1 < 0 || r1 >= R || c1 < 0 || c1 >= C) continue; 
                    int i1 = idx(r1, c1, C);
                    if (s.cells[i1] == '0') {
                        // Шаг на 1 клетку в пустую
                        CornersState t = s; 
                        swap(t.cells[idx(r, c, C)], t.cells[i1]);
                        string act = string("Step ") + (piece == '1' ? "W" : "B") + " (" + to_string(r) + "," + to_string(c) + ") -> (" + to_string(r1) + "," + to_string(c1) + ")";
                        res.emplace_back(move(t), move(act));
                    }
                    else {
                        // Перепрыгнуть через соседнюю занятую клетку, приземлиться сразу за ней
                        int r2 = r1 + dr[k], c2 = c1 + dc[k]; 
                        if (r2 < 0 || r2 >= R || c2 < 0 || c2 >= C) continue; 
                        int i2 = idx(r2, c2, C);
                        if (s.cells[i2] == '0') {
                            CornersState t = s;
                            t.cells[i2] = piece;
                            t.cells[idx(r, c, C)] = '0';
                            string act = string("Jump ") + (piece == '1' ? "W" : "B") + " (" + to_string(r) + "," + to_string(c) + ") -> (" + to_string(r2) + "," + to_string(c2) + ")";
                            res.emplace_back(move(t), move(act));
                        }
                    }
                }
            }
        return res;
    }
    bool is_goal(const CornersState& s) const { return s.cells == goal.cells; }
};

/******** Венгерский алгоритм (минимальное назначение, O(n^3)) ********/
// Возвращает минимальную сумму стоимостей назначения n работников к n задачам.
// Реализация через потенциалы u (строки) и v (столбцы) и «нулевые» редуцированные стоимости.
static int hungarian_min_cost(const vector<vector<int>>& a) {
    int n = a.size();
    const int INF = 1e9;
    vector<int> u(n + 1), v(n + 1), p(n + 1), way(n + 1);
    for (int i = 1; i <= n; i++) {
        p[0] = i; 
        int j0 = 0;
        vector<int> minv(n + 1, INF);
        vector<char> used(n + 1, false);
        do {
            used[j0] = true;
            int i0 = p[j0], delta = INF, j1 = 0;
            for (int j = 1; j <= n; j++)
                if (!used[j]) {
                    // редуцированная стоимость cur = a[i0-1][j-1] - u[i0] - v[j]
                    int cur = a[i0 - 1][j - 1] - u[i0] - v[j];
                    if (cur < minv[j]) minv[j] = cur, way[j] = j0;
                    if (minv[j] < delta) delta = minv[j], j1 = j;
                }
            // сдвиг потенциалов: у посещённых уменьшаем v, у соответствующих строк увеличиваем u;
            // у непосещённых уменьшаем запас minv (slack)
            for (int j = 0; j <= n; j++) {
                if (used[j]) 
                    u[p[j]] += delta, v[j] -= delta; 
                else minv[j] -= delta;
            }
            j0 = j1; // расширяем дерево по новому нулевому ребру
        } while (p[j0] != 0);
        // восстановление увеличивающего пути и переворот паросочетания
        do { int j1 = way[j0]; p[j0] = p[j1]; j0 = j1; } while (j0);
    }
    return -v[0]; // минимальная стоимость
}

// Вспомогательное: список позиций фигур
static vector<BoardPos> list_positions(const string& cells, int R, int C, char who) {
    vector<BoardPos> v; 
    for (int r = 0; r < R; r++) 
        for (int c = 0; c < C; c++) 
            if (cells[idx(r, c, C)] == who) 
                v.push_back({ r,c }); 
    return v;
}
static inline int manhattan(BoardPos a, BoardPos b) { return abs(a.r - b.r) + abs(a.c - b.c); }

// Эвристика для A*: сумма двух минимальных назначений по Манхэттену — для белых и для чёрных
static int corners_heuristic(const CornersProblem& P, const CornersState& s) {
    auto curW = list_positions(s.cells, P.R, P.C, '1');
    auto curB = list_positions(s.cells, P.R, P.C, '2');
    auto goalW = list_positions(P.goal.cells, P.R, P.C, '1');
    auto goalB = list_positions(P.goal.cells, P.R, P.C, '2');
    int cost = 0; int nW = (int)curW.size(), nB = (int)curB.size();
    if (nW) { 
        vector<vector<int>> a(nW, vector<int>(nW)); 
        for (int i = 0; i < nW; i++) 
            for (int j = 0; j < nW; j++) 
                a[i][j] = manhattan(curW[i], goalW[j]); 
        cost += hungarian_min_cost(a); 
    }
    if (nB) {
        vector<vector<int>> a(nB, vector<int>(nB));
        for (int i = 0; i < nB; i++)
            for (int j = 0; j < nB; j++)
                a[i][j] = manhattan(curB[i], goalB[j]);
        cost += hungarian_min_cost(a); 
    }
    return cost; // допустимая и согласованная для данной модели ходов
}

/******************** A* для «Уголков» (единственная реализация) ********************/

// Возвращает последовательность действий (строки). Предел расширений регулирует время работы.
static vector<string> Corners_Astar_Solve(const CornersProblem& P, int max_expansions = 500000) {
    struct QNode {
        CornersState s;
        int g, h; 
        string key;
    };
    struct Cmp {
        bool operator()(const QNode& a, const QNode& b) const { return a.g + a.h > b.g + b.h; }
    };
    auto keyOf = [&](const CornersState& s) { return s.cells; };
    priority_queue<QNode, vector<QNode>, Cmp> pq;
    unordered_map<string, int> bestg;
    unordered_map<string, pair<string, string>> parent; // child -> (parent_key, action)

    CornersState S = P.start;
    pq.push({ S,0,corners_heuristic(P,S), keyOf(S) });
    bestg[keyOf(S)] = 0;
    parent[keyOf(S)] = { "","START" };

    int expansions = 0;
    while (!pq.empty()) {
        auto cur = pq.top(); pq.pop(); 
        if (expansions++ > max_expansions) break;
        if (P.is_goal(cur.s)) {
            // восстановление пути по словарю parent
            vector<string> moves; 
            string k = cur.key;
            while (true) { 
                auto it = parent.find(k); 
                if (it == parent.end()) break; 
                auto [pk, act] = it->second; 
                if (act != "START") 
                    moves.push_back(act);
                if (pk.empty())
                    break;
                k = pk; 
            }
            reverse(moves.begin(), moves.end());
            return moves;
        }
        for (auto [ns, act] : P.neighbors(cur.s)) {
            int ng = cur.g + 1; 
            string nk = keyOf(ns); 
            auto it = bestg.find(nk);
            if (it == bestg.end() || ng < it->second) {
                bestg[nk] = ng;
                parent[nk] = { cur.key, act };
                pq.push({ ns,ng,corners_heuristic(P,ns), nk });
            }
        }
    }
    return {}; // не найдено в пределах лимита
}

/******************** DFS/IDS для «Уголков» ********************/

struct CornersSearchResult { 
    bool found = false;
    int goal_index = -1; 
    vector<Node<CornersState>> nodes;
    unordered_map<string, int> index_of; 
};

static vector<int> reconstruct_path(const vector<Node<CornersState>>& nodes, int goal_index) { 
    vector<int> path; 
    for (int i = goal_index; i != -1; i = nodes[i].parent) 
        path.push_back(i);
    reverse(path.begin(), path.end());
    return path;
}

static CornersSearchResult Corners_DFS(const CornersProblem& P, int limit) {
    CornersSearchResult R; 
    unordered_set<string> onstack;
    function<bool(const CornersState&, int, int, int, string)> rec;
        rec = [&](const CornersState& s, int depth, int lim, int parent, string action) {
        int idx = (int)R.nodes.size(); 
        R.nodes.push_back({ s,depth,0,parent,action }); 
        R.index_of[s.cells] = idx; 
        if (P.is_goal(s)) { 
            R.found = true;
            R.goal_index = idx; 
            return true;
        }
        if (depth == lim) return false; 
        onstack.insert(s.cells);
        for (auto [ns, act] : P.neighbors(s)) 
            if (!onstack.count(ns.cells))
                if (rec(ns, depth + 1, lim, idx, act))
                    return true; onstack.erase(s.cells);
        return false; 
        };
    rec(P.start, 0, limit, -1, "START"); return R;
}

static CornersSearchResult Corners_IDS(const CornersProblem& P, int max_depth) {
    for (int d = 0; d <= max_depth; ++d) {
        auto R = Corners_DFS(P, d);
        if (R.found) return R; 
    } 
    return {};
}

/******************** Вывод и CLI ********************/

static void print_wgc_path(const vector<Node<WGCState>>& nodes, int goal_index) {
    auto path = reconstruct_path(nodes, goal_index);
    cout << "Moves: " << ((int)path.size() - 1) << "\n"; 
        for (size_t i = 1; i < path.size(); ++i) {
            auto& n = nodes[path[i]]; 
            cout << i << ". " << n.action << " | State: farmer=" << (n.s.farmer ? "R" : "L") << ", wL=" << n.s.wL << ", gL=" << n.s.gL << ", cL=" << n.s.cL << "\n"; 
        }
}

    static void usage() {
        cerr << "Usage:" << "  wgc     --wolves W --goats G --cabbages C --algo bfs|dfs|ids [--limit D]" << "  corners --rows R --cols C --rectR r --rectC c --algo dfs|ids|";
    }

int main(int argc, char** argv) {
    ios::sync_with_stdio(false); cin.tie(nullptr);
    if (argc < 2) { usage(); return 0; }
    string mode = argv[1];

    if (mode == "wgc") {
        int W = 1, G = 1, C = 1; string algo = "bfs"; int limit = 64;
        for (int i = 2; i < argc; i++) {
            string a = argv[i]; auto need = [&](const string& flag) { return i + 1 < argc && a == flag; };
            if (need("--wolves")) W = stoi(argv[++i]);
            else if (need("--goats")) G = stoi(argv[++i]);
            else if (need("--cabbages")) C = stoi(argv[++i]);
            else if (need("--algo")) algo = argv[++i];
            else if (need("--limit")) limit = stoi(argv[++i]);
        }
        WGCProblem P(W, G, C);
        if (algo == "bfs") {
            auto R = WGC_BFS(P); if (R.found) {
                cout << "Solution found by BFS.";
                print_wgc_path(R.nodes, R.goal_index); } else cout<<"No solution(within explored space).";
        }
        else if (algo == "dfs") {
            auto R = WGC_DFS(P, limit); 
            if (R.found) {
                cout << "Solution found by DFS (depth-limited)."; 
                print_wgc_path(R.nodes, R.goal_index);
            }
            else cout<<"Not found within limit.";
        }
        else if (algo == "ids") {
                auto R = WGC_IDS(P, limit);
                if (R.found) {
                    cout << "Solution found by IDS."; 
                    print_wgc_path(R.nodes, R.goal_index);
                }
                else cout<<"No solution up to given depth.";
        }
        else usage();
    }
    else if (mode == "corners") {
             int R = 8, C = 8, r = 3, c = 4; string algo = "astar";
             for (int i = 2; i < argc; i++) {
                 string a = argv[i]; auto need = [&](const string& flag) { return i + 1 < argc && a == flag; };
                 if (need("--rows")) R = stoi(argv[++i]);
                 else if (need("--cols")) C = stoi(argv[++i]);
                 else if (need("--rectR")) r = stoi(argv[++i]);
                 else if (need("--rectC")) c = stoi(argv[++i]);
                 else if (need("--algo")) algo = argv[++i];
             }
             CornersProblem P(R, C, r, c);
             if (algo == "dfs") {
                 auto Rz = Corners_DFS(P, 200); 
                 if (Rz.found) {
                     cout << "Solution found by DFS (depth-limited)."; 
                     auto path=reconstruct_path(Rz.nodes,Rz.goal_index); 
                     cout<<"Moves: "<<path.size()-1<<"\n"; 
                     for(size_t i=1;i<path.size();++i) 
                         cout<<i<<". "<<Rz.nodes[path[i]].action<<"\n"; 
                 } 
                 else cout<<"Not found within limit.";
             }
             else if (algo == "ids") {
                     auto Rz = Corners_IDS(P, 512); 
                     if (Rz.found) {
                         cout << "Solution found by IDS.";
                         auto path=reconstruct_path(Rz.nodes,Rz.goal_index); 
                         cout<<"Moves: "<<path.size()-1<<"\n";
                         for(size_t i=1;i<path.size();++i) 
                             cout<<i<<". "<<Rz.nodes[path[i]].action<<"\n"; 
                     }
                     else cout<<"No solution up to max depth.";
             }
             else if (algo == "astar") {
                 auto moves = Corners_Astar_Solve(P, 1000000); 
                 if (!moves.empty()) {
                     cout << "Solution found by A*. Moves: " << moves.size() << "\n";
                     for(size_t i=0;i<moves.size();++i) 
                         cout<<(i+1)<<". "<<moves[i]<<"\n"; 
                 } else cout<<"A * did not find a solution within limits.Try smaller board or rectangles.";
             }
             else usage();
    }
    else usage();
    return 0;
}