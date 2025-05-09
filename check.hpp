#include <string>
#include <vector>
#include <fstream>
#include <utility>
#include <map>
#include <set>
#include <deque>
#include <cassert>
#include <numeric>
#include <spdlog/spdlog.h>
#include <fmt/core.h>

using std::string;
using std::vector;
using std::set;
using std::map;
using std::pair;
using std::tuple;
using std::deque;
using std::min;
using std::max;
using std::swap;

const int INF = 10000;

bool isForbiddenCut(int cutsize, int component_size) {
    if (cutsize <= 4) {
        return component_size > 0;
    } else if (cutsize == 5) {
        return component_size > 1;
    } else if (cutsize == 6) {
        return component_size > 3;
    } else if (cutsize == 7) {
        return component_size > 4;
    }
    return false;
}

// pq-contractibly connected パス := 
//     リングの頂点 p, q (p != q) を configuration の外側で繋ぐパス P であって、
//     p < q のとき E = P + p{p+1} + ... {q-1}q
//     p > q のとき E = P + p{p+1} + ... + {r-1}0 + ... +{q-1}q
//     が configuration と disjoint な disk を囲うようなもの。
struct Configuration {
  private:
    // 縮約辺
    vector<pair<int, int>> contract_; 
    // contract_ を縮約した結果 conf の中にできる 2,3-cut reduction によって削除される頂点集合
    vector<bool> is_reductable_inside_;
    // 6サイクルの中に conf があり、 contract_ を縮約した結果 conf の外にできる 2,3-cut reduction によって削除される頂点集合
    vector<bool> is_reductable_outside6_;
    // 7サイクルの中に conf があり、 contract_ を縮約した結果 conf の外にできる 2,3-cut reduction によって削除される頂点集合
    vector<bool> is_reductable_outside7_;
    // dist_contracted_[u][v] := contract_ を縮約した後の uv の間の最短距離
    vector<vector<int>> dist_contracted_;
    // 縮約後の代表元 (同一視された頂点のうちインデックスが最小のもの) の計算
    vector<int> representative_;
    // length6_[p][q] := 6サイクルの中に conf があり、
    // ring の頂点 p, q について pq-contractiblely connected パスがサイクルの一部であるときの最小の長さ。
    vector<vector<int>> length6_;
    // length_onedge6_[p][q] := 6サイクルの中に conf があり、
    // ring の頂点 p, q について pq-contractiblely connected パスが 1 辺を除いてサイクルの一部であるときの最小の長さ。
    vector<vector<int>> length_oneedge6_;
    // length7_[p][q] := 7サイクルの中に conf があり、
    // ring の頂点 p, q について pq-contractiblely connected パスがサイクルの一部であるときの最小の長さ。
    vector<vector<int>> length7_;
    // length_onedge7_[p][q] := 7サイクルの中に conf があり、
    // ring の頂点 p, q について pq-contractiblely connected パスが 1 辺を除いてサイクルの一部であるときの最小の長さ。
    vector<vector<int>> length_oneedge7_;
    // all_paths_[p][q] := リングの頂点 p,q の間の長さ 7 以下の全てのパス
    vector<vector<vector<vector<int>>>> all_paths_;
  public:
    // 頂点数
    int n_; 
    // リングサイズ
    int r_;
    // the free completion with its ring の隣接リスト
    vector<set<int>> VtoV_;
    // dist_[u][v] := uv の間の最短距離
    vector<vector<int>> dist_;

    Configuration(int n, int r, const vector<set<int>> &VtoV): 
        contract_({}), 
        is_reductable_inside_(vector<bool>(n, false)),
        is_reductable_outside6_(vector<bool>(n, false)),
        is_reductable_outside7_(vector<bool>(n, false)),
        n_(n), r_(r), VtoV_(VtoV) {
        dist_ = WF();
        dist_contracted_ = dist_;
        representative_ = calcRepresentative();
        all_paths_.assign(r_, vector<vector<vector<int>>>(r_));
        for (int p = 0;p < r_; p++) {
            for (int q = 0;q < r_; q++) {
                if (p == q) continue;
                all_paths_[p][q] = calculatePaths(p, q);
            }
        }
        length6_ = calcLowerBoundLengthOuterPath(6);
        length7_ = calcLowerBoundLengthOuterPath(7);
        length_oneedge6_ = calcLowerBoundLengthOuterPathOneEdge(6);
        length_oneedge7_ = calcLowerBoundLengthOuterPathOneEdge(7);
    }

    static Configuration readConfFile(const string &filename) {
        std::ifstream ifs(filename);
        if (!ifs) {
            spdlog::critical("Failed to open {} ", filename);
            throw std::runtime_error("Failed to open" + filename);
        }
        string dummy;
        getline(ifs, dummy);
        int n, r;
        ifs >> n >> r;
        vector<set<int>> VtoV(n);
        for (int i = 0;i < r; i++) {
            VtoV[i].insert((i + 1) % r);
            VtoV[(i + 1) % r].insert(i);
        }
        for (int i = r;i < n; i++) {
            int v, d;
            ifs >> v >> d;
            --v;
            assert(v == i);
            for (int j = 0;j < d; j++) {
                int u;
                ifs >> u;
                --u;
                VtoV[v].insert(u);
                if (u < r) {
                    VtoV[u].insert(v);
                }
            }
        }
        return Configuration(n, r, VtoV);
    }

    // 縮約辺 contract_ を設定して、それに伴う更新をする。
    void setContract(const vector<pair<int, int>> &contract) {
        contract_ = contract;
        dist_contracted_ = WF(true);
        is_reductable_inside_ = calcCutReduction();
        is_reductable_outside6_ = calcReductableVertices(6);
        is_reductable_outside7_ = calcReductableVertices(7);
        representative_ = calcRepresentative();
        for (int v = 0;v < n_; v++) {
            if (is_reductable_inside_[v] || is_reductable_outside6_[v]) {
                spdlog::info("vertex {} is erased by 6", v);
            }
            if (is_reductable_inside_[v] || is_reductable_outside7_[v]) {
                spdlog::info("vertex {} is erased by 7", v);
            }
        }
        return;
    }

    vector<int> calcRepresentative(void) {
        // 縮約後の代表元の計算 (代表元はインデックスが最小のものを選ぶようにしている)
        vector<int> representative(n_, -1);
        for (int v = 0;v < n_; v++) {
            for (int u = 0;u < n_; u++) {
                if (equivalent(v, u)) {
                    representative[v] = u;
                    break;
                }
            }
        }
        return representative;
    }

    // contract_ の辺を縮約した後に同じ頂点になっているかどうかを計算する。
    bool equivalent(int u, int v) const {
        return dist_contracted_[v][u] == 0;
    }

    // APSP Warshall-Floyd
    // after_contract = true なら contract_ に含まれる辺を縮約した場合の距離を返す。
    vector<vector<int>> WF(bool after_contract=false) const {
        vector<vector<int>> dist(n_, vector<int>(n_, INF));
        for (int v = 0;v < n_; v++) {
            dist[v][v] = 0;
            for (int u : VtoV_[v]) {
                dist[v][u] = 1;
            }
        }
        if (after_contract) {
            for (const auto &e : contract_) {
                assert(dist[e.first][e.second] == 1);
                dist[e.first][e.second] = 0;
                dist[e.second][e.first] = 0;
            }
        }
        for (int k = 0;k < n_; k++) {
            for (int i = 0;i < n_; i++) {
                for (int j = 0;j < n_; j++) {
                    dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]);
                }
            }
        }
        return dist;
    }

    // s-t shortestPaths の列挙
    // after_contract = true ならば contract に含まれる辺を縮約した場合の最短路を考える。
    vector<vector<int>> shortestPaths(int s, int t, bool after_contract=false) const {
        set<pair<int, int>> contract_set;
        if (after_contract) {
            for (const auto &e : contract_) {
                contract_set.insert(e);
                contract_set.insert({e.second, e.first});
            }
        }
        vector<int> dist(n_, INF);
        dist[s] = 0;
        deque<int> que;
        que.push_back(s);
        while (!que.empty()) {
            int v = que.front();
            que.pop_front();
            for (int u : VtoV_[v]) {
                if (contract_set.count({u, v})) {
                    if (dist[v] < dist[u]) {
                        dist[u] = dist[v];
                        que.push_front(u);
                    }
                } else {
                    if (dist[v] + 1 < dist[u]) {
                        dist[u] = dist[v] + 1;
                        que.push_back(u);
                    }
                }
            }
        }

        vector<vector<vector<int>>> paths(n_); // paths[i] := { s-i shortest path の集合 }
        paths[s].push_back({s});
        que.push_back(s);
        while (!que.empty()) {
            int v = que.front();
            que.pop_front();
            for (int u : VtoV_[v]) {
                if (dist[u] == dist[v] + 1 || (dist[u] == dist[v] && contract_set.count({u, v}))) {
                    bool update = false;
                    for (auto &path : paths[v]) { // path は変更してはいけない
                        path.push_back(u);
                        // + path が既に paths[u] に入っている
                        // + path は既に u を含んでいる (次に u を通ると path ではなくなる)
                        // 場合は update する必要がない。
                        if ((std::find(paths[u].begin(), paths[u].end(), path) != paths[u].end()) ||
                            (std::find(path.begin(), path.end(), u) != --path.end())) {
                            path.pop_back();
                            continue;
                        }
                        path.pop_back();

                        vector<int> upath = path;
                        upath.push_back(u);
                        paths[u].push_back(upath);
                        update = true;
                    }
                    if (update) {
                        if (dist[u] == dist[v] + 1) {
                            que.push_back(u);
                        } else {
                            que.push_front(u);
                        }
                    }
                }
            }
        }


        vector<vector<int>> unique_paths;
        for (const vector<int> &path : paths[t]) {
            bool unique = true;
            for (const vector<int> &unique_path : unique_paths) {
                if (path == unique_path) {
                    unique = false;
                    break;
                }
            }
            if (unique) {
                unique_paths.push_back(path);
            }
        }

        return unique_paths;
    }

    // p, q 間の長さ 7 以下のパスを列挙する。
    vector<vector<int>> calculatePaths(int p, int q) const {
        vector<vector<int>> paths;
        auto dfs = [&](auto &&dfs, int v, vector<int> &path) -> void {
            path.push_back(v);
            if (path.back() == q) {
                paths.push_back(path);
                path.pop_back();
                return;
            }
            if (path.size() == 8) {
                path.pop_back();
                return;
            }
            for (int u : VtoV_[v]) {
                if (std::find(path.begin(), path.end(), u) == path.end()) {
                    dfs(dfs, u, path);
                }
            }
            path.pop_back();
            return;
        };
        vector<int> path;
        dfs(dfs, p, path);
        return paths;
    }

    // contract_ の辺を縮約した後に
    // cut に含まれる頂点集合によって分けられるどの連結成分に属しているかを表す id を返す。
    vector<int> componentIdEquivalence(const vector<int> &cut) const {
        // cut 頂点集合の計算
        set<int> cutset;
        for (int v : cut) {
            cutset.insert(v);
            for (int u = 0;u < n_; u++) {
                if (equivalent(v, u)) {
                    cutset.insert(u);
                }
            }
        }

        vector<int> component_id(n_, -1);
        auto dfs = [&](auto &&dfs, int v, int c) -> void {
            component_id[v] = c;
            for (int u : VtoV_[v]) {
                if (cutset.count(u)) {
                    continue;
                }
                if (component_id[u] != -1) {
                    continue;
                }
                dfs(dfs, u, c);
            }
            return;
        };
        // リングに接続している頂点は外側のグラフで繋がっている
        for (int v = 0;v < r_; v++) {
            if (!cutset.count(v)) {
                dfs(dfs, v, 0);
            }
        }
        int num_component = 1;
        for (int v = r_;v < n_; v++) {
            if (!cutset.count(v) && component_id[v] == -1) {
                dfs(dfs, v, num_component);
                num_component++;
            }
        }

        return component_id;
    }

    void updateIsReductable(vector<bool> &is_reductable, const vector<int> &component_id, const vector<bool> &is_ring) const {
        vector<bool> is_reducing_component(n_, true);
        for (int v = 0;v < n_; v++) {
            if (component_id[v] != -1 && is_ring[v]) {
                is_reducing_component[component_id[v]] = false;
            }
        }
        for (int v = 0;v < n_; v++) {
            if (component_id[v] != -1 && is_reducing_component[component_id[v]]) {
                is_reductable[v] = true;
            }
        }
        return;
    }

    // contract_ を縮約した後にできる conf の中の 2,3-cut 
    // によって消える可能性のある頂点かどうかを表すフラグを計算する。
    vector<bool> calcCutReduction(void) const {
        vector<bool> is_reductable(n_, false);
        vector<bool> is_ring(n_, false); // ring の頂点か、ring の頂点と同一視される頂点か
        for (int v = 0;v < r_; v++) {
            for (int u = 0;u < n_; u++) {
                if (equivalent(v, u)) {
                    is_ring[u] = true;
                }
            }
        }
        for (int v0 = 0;v0 < n_; v0++) {
            vector<int> component_id = componentIdEquivalence({v0});
            updateIsReductable(is_reductable, component_id, is_ring);
            for (int v1 = 0;v1 < v0; v1++) {
                vector<int> component_id = componentIdEquivalence({v0, v1});
                updateIsReductable(is_reductable, component_id, is_ring);
                for (int v2 = 0;v2 < v1; v2++) {
                    vector<int> component_id = componentIdEquivalence({v0, v1, v2});
                    updateIsReductable(is_reductable, component_id, is_ring);
                }
            }
        }
        return is_reductable;
    }

    // リング上の頂点 p, q が端点であるようなパス pqpath があるとき、
    // pqpath によって分けられる頂点集合のうち、
    // + p < q ならば p+1, p+2, ... , q-1 が
    // + p > q ならば (p+1)%r, (p+2)%r, ... , (q+r-1)%r が 
    // 含まれる方の頂点集合を返す。
    vector<int> getComponent(const vector<int> &pqpath) const {
        int p = pqpath[0], q = pqpath.back();
        assert(p != q && p < r_ && q < r_);

        set<int> cutset;
        for (int v : pqpath) {
            cutset.insert(v);
        }

        vector<int> component_id(n_, -1);
        vector<int> component;
        auto dfs = [&](auto &&dfs, int v, int c) -> void {
            if (cutset.count(v) || component_id[v] != -1) {
                return;
            }
            component_id[v] = c;
            component.push_back(v);
            for (int u : VtoV_[v]) {
                dfs(dfs, u, c);
            }
            return;
        };
        for (int v = (p + 1) % r_;v != q;v = (v + 1) % r_) {
            dfs(dfs, v, 0);
        }

        return component;
    }

    // リング上で p1, q1, p2, q2 の順に並んでいる頂点について、
    // q1 と p2 を結ぶパスを q1p2_path, q2 と p1 を結ぶパスを q2p1_path としたとき、
    // その 2 つのパスに囲まれる configuration の連結成分の頂点集合を得る。(2つのパスが交わっているときは厳密には異なる。)
    vector<int> getComponent(const vector<int> &q1p2_path, const vector<int> &q2p1_path) const {
        set<int> component2;
        for (int v : getComponent(q1p2_path)) {
            component2.insert(v);
        }
        vector<int> p1q2_path = q2p1_path;
        std::reverse(p1q2_path.begin(), p1q2_path.end());
        vector<int> component;
        for (int v : getComponent(p1q2_path)) {
            if (!component2.count(v)) {
                component.push_back(v);
            }
        }
        return component;
    }

    // リング上で p1, q1, p2, q2 の順に並んでいる頂点について、
    // q1 と p2 を結ぶパスを q1p2_path, q2 と p1 を結ぶパスを q2p1_path としたとき、
    // その 2 つのパスに囲まれる configuration の連結成分と 2 つのパスの頂点 "以外" の頂点集合を得る。(2つのパスが交わっているときは厳密には異なる。)
    vector<int> getComponent2(const vector<int> &q1p2_path, const vector<int> &q2p1_path) const {
        set<int> component2;
        for (int v : getComponent(q1p2_path)) {
            component2.insert(v);
        }
        vector<int> component;
        for (int v : getComponent(q2p1_path)) {
            if (component2.count(v) > 0) {
                component2.erase(v);
                continue;
            }
            component.push_back(v);
        }
        for (int v : component2) {
            component.push_back(v);
        }
        return component;
    }

    // リング上の頂点 p, q が端点であるようなパス pqpath があるとき、
    // pqpath によって分けられる頂点集合のうち、
    // + p < q ならば p+1, p+2, ... , q-1 が
    // + p > q ならば (p+1)%r, (p+2)%r, ... , (q+r-1)%r が 
    // 含まれる方の頂点集合サイズを計算する。
    pair<int, int> sizeOfVertices(const vector<int> &pqpath) const {
        vector<int> component = getComponent(pqpath);

        int s = 0; // ring
        int t = 0; // inside ring
        for (int v : component) {
            if (v < r_) {
                s++;
            } else if (v >= r_) {
                t++;
            }
        }

        return std::make_pair(s, t);
    }

    // リング上で p1, q1, p2, q2 の順に並んでいる頂点について、
    // q1 と p2 を結ぶパスを q1p2_path, q2 と p1 を結ぶパスを q2p1_path としたとき、
    // その 2 つのパスに囲まれる configuration の連結成分の頂点集合サイズを計算する。
    pair<int, int> sizeOfVertices(const vector<int> &q1p2_path, const vector<int> &q2p1_path) const {
        vector<int> component = getComponent(q1p2_path, q2p1_path);

        int s = 0; // ring
        int t = 0; // inside ring
        for (int v : component) {
            if (v < r_) {
                s++;
            } else if (v >= r_) {
                t++;
            }
        }

        return std::make_pair(s, t);
    }

    // リング上で p1, q1, p2, q2 の順に並んでいる頂点について、
    // q1 と p2 を結ぶパスを q1p2_path, q2 と p1 を結ぶパスを q2p1_path としたとき、
    // その 2 つのパスに囲まれる configuration の連結成分と 2 つのパスの頂点 "以外" の頂点集合のサイズを計算する。
    pair<int, int> sizeOfVertices2(const vector<int> &q1p2_path, const vector<int> &q2p1_path) const {
        vector<int> component = getComponent2(q1p2_path, q2p1_path);

        int s = 0; // ring
        int t = 0; // inside ring
        for (int v : component) {
            if (v < r_) {
                s++;
            } else if (v >= r_) {
                t++;
            }
        }

        return std::make_pair(s, t);
    }

    // (conf + ring) の中にある path P と (conf + ring) の外で P の端点を結ぶ長さが k のパス
    // でできるサイクル C' が以下の条件を満たすかをチェックする。
    // + path の辺が全て ring の辺である。
    // + path が 2 or 3 辺を除いて ring の辺であるようなパスであり、 C' の長さが 7 であり、6 サイクルの中にある。
    // この条件で C' が C (やそれに近いサイクル)になりうるかを調べている。
    bool canBeAlmostMinimal(const vector<int> &path, int k, int cutSize) const {
        assert(path[0] < r_ && path.back() < r_);
        int number_in_ring = 0;
        for (size_t i = 0;i < path.size() - 1; i++) {
            if (path[i] < r_ && path[i + 1] < r_) number_in_ring ++;
        }
        int pathlen = (int)path.size() - 1;
        assert(pathlen >= 1);
        if ((number_in_ring == pathlen && pathlen + k >= 6) ||
            ((pathlen <= 3 || number_in_ring >= pathlen - 3) &&
              pathlen + k == 7 && cutSize == 6)) {
            return true;
        }
        return false;
    }

    // (conf + ring) の中にある path1, path2 と (conf + ring) の外で path1, path2 の端点を結ぶ長さが k1, k2 のパス
    // でできるサイクル C' が以下の条件を満たすかをチェックする。
    // + path1, path2 の辺が全て ring の辺である。
    // + path1, path2 が 2 or 3 辺を除いて ring の辺であるようなパスで C' の長さが 7 であり、6 サイクルの中にある。
    // この条件で C' が C (やそれに近いサイクル)になりうるかを調べている。
    bool canBeAlmostMinimal(const vector<int> &path1, const vector<int> &path2, int k1, int k2, int cutSize) const {
        assert(path1[0] < r_ && path1.back() < r_);
        int number_in_ring1 = 0;
        for (size_t i = 0;i < path1.size() - 1; i++) {
            if (path1[i] < r_ && path1[i + 1] < r_) number_in_ring1++;
        }
        assert(path2[0] < r_ && path2.back() < r_);
        int number_in_ring2 = 0;
        for (size_t i = 0;i < path2.size() - 1; i++) {
            if (path2[i] < r_ && path2[i + 1] < r_) number_in_ring2++;
        }
        int pathlen1 = (int)path1.size() - 1;
        int pathlen2 = (int)path2.size() - 1;

        int number_in_ring = number_in_ring1 + number_in_ring2;
        int pathlen = pathlen1 + pathlen2;
        int k = k1 + k2;
        if ((number_in_ring == pathlen && pathlen + k >= 6) ||
            ((pathlen <= 3 || number_in_ring >= pathlen - 3) &&
              pathlen + k == 7 && cutSize == 6)) {
            return true;
        }
        return false;
    }

    bool canBeAlmostMinimal2(const vector<int> &path1, const vector<int> &path2, int k1, int k2, int cutSize) const {
        assert(path1[0] < r_ && path1.back() < r_);
        int number_in_ring1 = 0;
        for (size_t i = 0;i < path1.size() - 1; i++) {
            if (path1[i] < r_ && path1[i + 1] < r_) number_in_ring1++;
        }
        assert(path2[0] < r_ && path2.back() < r_);
        int number_in_ring2 = 0;
        for (size_t i = 0;i < path2.size() - 1; i++) {
            if (path2[i] < r_ && path2[i + 1] < r_) number_in_ring2++;
        }
        int pathlen1 = (int)path1.size() - 1;
        int pathlen2 = (int)path2.size() - 1;

        int num_inside = k1 + (pathlen1 - number_in_ring1) + (pathlen2 - number_in_ring2);
        int l = pathlen1 + pathlen2 + k1 + k2;
        return ((num_inside == 0 && l >= 6) || (num_inside <= 3 && l == 7 && cutSize == 6));
    }

    // conf が cutSize (=6,7) のサイクルに囲われているとき、
    // リングの頂点 a, b について、長さ k の ab-contractibly connected path が存在するとき、
    // そのパスが low-cut の条件に矛盾するかを調べる。
    bool checkShortCycle(int a, int b, int k, int cutSize) const {
        assert(a < r_ && b < r_ && a != b);
        const vector<vector<int>> &abpaths = all_paths_[a][b];
        for (auto R : abpaths) {
            if (canBeAlmostMinimal(R, k, cutSize)) {
                continue;
            }
            int m = (int)R.size() - 1;
            auto [s, t] = sizeOfVertices(R);
            int sz = max(s - max(k-1, 0) + 1, 0) / 2 + t;
            if (isForbiddenCut(k+m, sz)) {
                return true;
            }
            if (((k == 2 && m == 3) || (k == 1 && m == 4)) && s == 2 && t == 0 && 
                VtoV_[(a + 1) % r_].size() <= 4 && VtoV_[(a + 2) % r_].size() <= 4) {
                return true;
            }
        }
        return false;
    }

    // 縮約後に contractible loop を持ちうるかのチェック
    void canHaveContractibleLoop(void) const {
        for (int cutSize = 6;cutSize <= 7; cutSize++) {
            for (int p = 0;p < r_; p++) {
                for (int q = 0;q < r_; q++) {
                    if (p == q || p + 1 == q || (p == r_ - 1 && q == 0)) {
                        continue;
                    }
                    int pathlen_min = 0;
                    int pathlen_max = 1 - dist_contracted_[p][q];
                    if (pathlen_min > pathlen_max) continue;

                    for (int pathlen = pathlen_min;pathlen <= pathlen_max; pathlen++) {
                        if (checkShortCycle(p, q, pathlen, cutSize)) {
                            continue;
                        }
                        spdlog::info("dangerous: may be a bridge by {},{}-contractible in {}-cycle, general", p, q, cutSize);
                    }
                }
            }
            const auto &length = cutSize == 6 ? length6_ : length7_;
            for (int p1 = 0;p1 < r_; p1++) {
                for (int q1_ = p1 + 1;q1_ < p1 + r_; q1_++) {
                    for (int p2_ = q1_ + 1;p2_ < p1 + r_; p2_++) {
                        for (int q2_ = p2_ + 1;q2_ < p1 + r_; q2_++) {
                            int q1 = q1_ % r_;
                            int p2 = p2_ % r_;
                            int q2 = q2_ % r_;
                            // p1, q1, p2, q2 の順にリングに並んでいる。
                            int length_inside = dist_contracted_[q1][p2] + dist_contracted_[q2][p1];
                            // p1q1-contractibly connected path & p2q2-contractibly connected path
                            if (length_inside + length[p1][q1] + length[p2][q2] <= 1) {
                                spdlog::info("dangerous: may be a bridge by {},{}-contractible, {},{}-contractible in {}-cycle, general", p1, q1, p2, q2, cutSize);
                            }
                            // p1q1-contractibly connected path & q2p2-contractibly connected path
                            if (length_inside + length[p1][q1] + length[q2][p2] <= 1) {
                                spdlog::info("dangerous: may be a bridge by {},{}-contractible, {},{}-contractible in {}-cycle, general", p1, q1, q2, p2, cutSize);
                            }
                        }
                    }
                }
            }
        }
        return;
    }

    // 1 本のパスで消える頂点を計算
    void calcReductableVertices1(int cutSize, vector<bool> &is_reductable) const {
        for (int p = 0;p < r_; p++) {
            for (int q = 0;q < r_; q++) {
                if (p == q) {
                    continue;
                }
                int pathlen_min = max(0, 5 - dist_[p][q]);
                int pathlen_max = 3 - dist_contracted_[p][q];
                if (pathlen_min > pathlen_max) continue;
                vector<vector<int>> contracted_paths = shortestPaths(p, q, true);

                for (int pathlen = pathlen_min;pathlen <= pathlen_max; pathlen++) {
                    if (checkShortCycle(p, q, pathlen, cutSize)) {
                        continue;
                    }
                    for (const auto &contracted_path : contracted_paths) {
                        if ((int)contracted_path.size() - 1 == dist_[p][q]) continue;
                        auto reducing_component = getComponent(contracted_path);
                        for (int v : reducing_component) {
                            bool equivalent_path = false;
                            for (int u : contracted_path) {
                                if (equivalent(v, u)) equivalent_path = true;
                            }
                            if (equivalent_path) continue;
                            is_reductable[v] = true;
                        }
                    }
                }
            }
        }
        return;
    }

    // p1, q1, p2, q2 がリングに順に並んでいるとき
    // contractible な 2 本のパス (p1q1-contractly connected path と p2q2-contractibly connected path) で消える頂点を計算
    void calcReductableVertices2(int cutSize, vector<bool> &is_reductable) const {
        for (int p1 = 0;p1 < r_; p1++) {
            for (int q1_ = p1 + 1;q1_ < p1 + r_; q1_++) {
                for (int p2_ = q1_ + 1;p2_ < p1 + r_; p2_++) {
                    for (int q2_ = p2_ + 1;q2_ < p1 + r_; q2_++) {
                        int q1 = q1_ % r_;
                        int p2 = p2_ % r_;
                        int q2 = q2_ % r_;
                        // p1, q1, p2, q2 の順にリングに並んでいる。
                        int pathlen_min1 = max(0, 5 - dist_[p1][q1]);
                        int pathlen_min2 = max(0, 5 - dist_[p2][q2]);
                        int pathlen_max = 3 - dist_contracted_[q1][p2] - dist_contracted_[q2][p1];
                        if (pathlen_min1 > pathlen_max || pathlen_min2 > pathlen_max) continue;

                        vector<vector<int>> shortest_path1s = shortestPaths(q1, p2);
                        vector<vector<int>> shortest_path2s = shortestPaths(q2, p1);
                        vector<vector<int>> contracted_path1s = shortestPaths(q1, p2, true);
                        vector<vector<int>> contracted_path2s = shortestPaths(q2, p1, true);
                        
                        for (int pathlen1 = pathlen_min1;pathlen1 <= pathlen_max; pathlen1++) {
                            for (int pathlen2 = pathlen_min2;pathlen2 <= pathlen_max; pathlen2++) {
                                if (pathlen1 + pathlen2 + dist_contracted_[q1][p2] + dist_contracted_[q2][p1] > 3) {
                                    continue;
                                }
                                if (checkShortCycle(p1, q1, pathlen1, cutSize)) {
                                    continue;
                                }
                                if (checkShortCycle(p2, q2, pathlen2, cutSize)) {
                                    continue;
                                }
                                bool has_smallcut = false;
                                for (const auto &shortest_path1 : shortest_path1s) {
                                    for (const auto &shortest_path2 : shortest_path2s) {
                                        if (canBeAlmostMinimal(shortest_path1, shortest_path2, pathlen1, pathlen2, cutSize)) {
                                            continue;
                                        }
                                        auto [s, t] = sizeOfVertices(shortest_path1, shortest_path2);
                                        int sz = max(s - max(pathlen1 + pathlen2 - 2, 0) + 1, 0) / 2 + t;
                                        if (isForbiddenCut(shortest_path1.size()+shortest_path2.size()-2+pathlen1+pathlen2, sz)) {
                                            has_smallcut = true;
                                            break;
                                        }
                                    }
                                    if (has_smallcut) break;
                                }
                                if (has_smallcut) {
                                    continue;
                                }
                                for (const auto &contracted_path1 : contracted_path1s) {
                                    for (const auto &contracted_path2 : contracted_path2s) {
                                        if ((int)contracted_path1.size() - 1 == dist_[q1][p2] && (int)contracted_path2.size() - 1 == dist_[q2][p1]) continue;
                                        auto reducing_component = getComponent(contracted_path1, contracted_path2);
                                        for (int v : reducing_component) {
                                            bool equivalent_path = false;
                                            for (int u : contracted_path1) {
                                                if (equivalent(v, u)) equivalent_path = true;
                                            }
                                            for (int u : contracted_path2) {
                                                if (equivalent(v, u)) equivalent_path = true;
                                            }
                                            if (equivalent_path) continue;
                                            is_reductable[v] = true;
                                        }
                                    }
                                }
                            }
                        }

                    }
                }
            }
        }
        return;
    }

    // p1, q1 間に noncontractible に長さ pathlen1 のパスがあり、
    // p2, q2 間に noncontractible に長さ pathlen2 のパスがあるとき、
    // cutSize (6 or 7) のサイクルがそれらのパスと両立するかのチェックをする。
    int calcLowerBoundCycle(int p1, int q1, int p2, int q2, int pathlen1, int pathlen2, int cutSize) const {
        assert(pathlen1 + pathlen2 <= 3);
        // 6,7 サイクルと path1, path2 が両立するかどうかのチェック
        const auto &length = cutSize == 6 ? length6_ : length7_;
        const auto &length_oneedge = cutSize == 6 ? length_oneedge6_ : length_oneedge7_;

        int L_vertical = max(length[p1][q1], 2 - pathlen1) + max(length[p2][q2], 2 - pathlen2); // 元から rep = 1 なら Petersen-like にならないから 2 - pathlen_i
        int L_horizontal = length[q1][p2] + length[q2][p1];
        int L = (L_vertical + pathlen1 + pathlen2 <= 5 && L_horizontal + pathlen1 + pathlen2 <= 5) ? // サイクルの外側の 2 つの領域がどちらも 5 カットなら 6,7 サイクルの頂点数の仮定に反する
                (L_vertical + L_horizontal + 6 - pathlen1 - pathlen2 - max(L_vertical, L_horizontal)) : // から、そうでなくないように長さを伸ばす。
                L_vertical + L_horizontal;
        if (pathlen1 == 2) {
            // サイクルが pathlen1 の中点を 1 回通るとき
            int L1_vertical = max(length_oneedge[p1][q1], 1) + max(length[p2][q2], 2 - pathlen2);
            int L1_horizontal = min(length[q2][p1] + length_oneedge[q1][p2], length_oneedge[q2][p1] + length[q1][p2]);
            int L1 = (L1_vertical + pathlen2 + 1 <= 5 && L1_horizontal + pathlen2 + 1 <= 5) ?
                        (L1_vertical + L1_horizontal + 5 - pathlen2 - max(L1_vertical, L1_horizontal)) :
                        L1_vertical + L1_horizontal;
            L = min(L, L1);
            if (pathlen2 == 1) {
                // サイクルが p2 (または q2) を 2 回通るとき、
                int L2_vertical = max(length[p1][q1], 2 - pathlen1) + max(length_oneedge[p2][q2], 2);
                int L2_horizontal = min(length[q2][p1] + length_oneedge[q1][p2], length_oneedge[q2][p1] + length[q1][p2]);
                int L2 = (L2_vertical + pathlen1 <= 5 && L2_horizontal + pathlen1 <= 5) ?
                         (L2_vertical + L2_horizontal + 6 - pathlen1 - max(L2_horizontal, L2_vertical)) :
                         L2_vertical + L2_horizontal;
                L = min(L, L2);
            }
        }
        if (pathlen2 == 2) {
            // サイクルが pathlen2 の中点を 1 回通るとき
            int L1_vertical = max(length[p1][q1], 2 - pathlen1) + max(length_oneedge[p2][q2], 1);
            int L1_horizontal = min(length[q2][p1] + length_oneedge[q1][p2], length_oneedge[q2][p1] + length[q1][p2]);
            int L1 = (L1_vertical + pathlen1 + 1 <= 5 && L1_horizontal + pathlen1 + 1 <= 5) ?
                        (L1_vertical + L1_horizontal + 5 - pathlen1 - max(L1_vertical, L1_horizontal)) :
                        L1_vertical + L1_horizontal;
            L = min(L, L1);
            if (pathlen1 == 1) {
                // サイクルが p1 (または q1) を 2 回通るとき、
                int L2_vertical = max(length_oneedge[p1][q1], 2) + max(length[p2][q2], 2 - pathlen2);
                int L2_horizontal = min(length[q2][p1] + length_oneedge[q1][p2], length_oneedge[q2][p1] + length[q1][p2]);
                int L2 = (L2_vertical + pathlen2 <= 5 && L2_horizontal + pathlen2 <= 5) ?
                         (L2_vertical + L2_horizontal + 6 - pathlen2 - max(L2_vertical, L2_horizontal)):
                         L2_vertical + L2_horizontal;
                L = min(L, L2);
            }
        }
        // どちらかの長さが 3 のときは trivial な下限しか考えない。
        if (pathlen1 == 3 || pathlen2 == 3) {
            L = 0;
        }

        return L;
    }

    // p1, q1, p2, q2 がリングに順に並んでいるとき
    // noncontractible な 2 本のパス (p1q1-path と p2q2-path) で消える頂点を計算
    void calcReductableVertices3(int cutSize, vector<bool> &is_reductable) const {
        for (int p1 = 0;p1 < r_; p1++) {
            for (int q1_ = p1 + 1;q1_ < p1 + r_; q1_++) {
                for (int p2_ = q1_ + 1;p2_ < p1 + r_; p2_++) {
                    for (int q2_ = p2_ + 1;q2_ < p1 + r_; q2_++) {
                        if (q1_ + 1 == p2_ && q2_ + 1 == p1 + r_) {
                            continue;
                        }
                        int q1 = q1_ % r_;
                        int p2 = p2_ % r_;
                        int q2 = q2_ % r_;
                        // p1, q1, p2, q2 の順にリングに並んでいる。
                        // 縮約後に rep <= 1 にならないための制約
                        int pathlen_min1 = max(2 - dist_contracted_[p1][q1], 0);
                        int pathlen_min2 = max(2 - dist_contracted_[p2][q2], 0);
                        int pathlen_max = 3 - dist_contracted_[q1][p2] - dist_contracted_[q2][p1];
                        if (pathlen_min1 > pathlen_max || pathlen_min2 > pathlen_max) continue;
    
                        assert(q1 != p2);
                        const vector<vector<int>> &path1s = all_paths_[q1][p2];
                        assert(q2 != p1);
                        const vector<vector<int>> &path2s = all_paths_[q2][p1];

                        vector<vector<int>> contracted_path1s = shortestPaths(q1, p2, true);
                        vector<vector<int>> contracted_path2s = shortestPaths(q2, p1, true);
                        
                        // p1-q1 間に pathlen1 の長さのパス、p2-q2 間に pathlen2 の長さのパス
                        for (int pathlen1 = pathlen_min1;pathlen1 <= pathlen_max; pathlen1++) {
                            for (int pathlen2 = pathlen_min2;pathlen2 <= pathlen_max; pathlen2++) {
                                if (pathlen1 + pathlen2 + dist_contracted_[q1][p2] + dist_contracted_[q2][p1] > 3) {
                                    continue;
                                }

                                // 6,7 サイクルと path1, path2 が両立するかのチェック。
                                int L = calcLowerBoundCycle(p1, q1, p2, q2, pathlen1, pathlen2, cutSize);
                                if (L > cutSize) {
                                    continue;
                                }

                                bool has_smallcut = false;
                                for (const auto &path1 : path1s) {
                                    for (const auto &path2 : path2s) {
                                        int l = pathlen1 + pathlen2 + path1.size() - 1 + path2.size() - 1;
                                        if (l > 5) continue;
                                        auto [s, t] = sizeOfVertices2(path1, path2);
                                        int sz = max(s - max(pathlen1 + pathlen2 - 2, 0) + 1, 0) / 2 + t;
                                        if ((l <= 4 && sz > 0) || (l == 5 && sz > 1)) {
                                            has_smallcut = true;
                                            break;
                                        }
                                    }
                                }
                                if (has_smallcut) {
                                    continue;
                                }
                                for (const auto &contracted_path1 : contracted_path1s) {
                                    for (const auto &contracted_path2 : contracted_path2s) {
                                        if ((int)contracted_path1.size() - 1 == dist_[q1][p2] && (int)contracted_path2.size() - 1 == dist_[q2][p1]) continue;
                                        auto reducing_component = getComponent2(contracted_path1, contracted_path2);
                                        for (int v : reducing_component) {
                                            bool equivalent_path = false;
                                            for (int u : contracted_path1) {
                                                if (equivalent(v, u)) equivalent_path = true;
                                            }
                                            for (int u : contracted_path2) {
                                                if (equivalent(v, u)) equivalent_path = true;
                                            }
                                            if (equivalent_path) continue;
                                            is_reductable[v] = true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return;
    }

    // p1, q1, p2, q2 がリングに順に並んでいるとき
    // contractible な 2 本のパス (p1q1-contractly connected path と q2p2-contractibly connected path) で消える頂点を計算
    void calcReductableVertices4(int cutSize, vector<bool> &is_reductable) const {
        for (int p1 = 0;p1 < r_; p1++) {
            for (int q1_ = p1 + 1;q1_ < p1 + r_; q1_++) {
                for (int p2_ = q1_ + 1;p2_ < p1 + r_; p2_++) {
                    for (int q2_ = p2_ + 1;q2_ < p1 + r_; q2_++) {
                        int q1 = q1_ % r_;
                        int p2 = p2_ % r_;
                        int q2 = q2_ % r_;
                        // p1, q1, p2, q2 の順にリングに並んでいる。
                        int pathlen_min1 = max(0, 5 - dist_[p1][q1]);
                        int pathlen_min2 = max(0, 5 - dist_[p2][q2]);
                        int pathlen_max = 3 - dist_contracted_[q1][p2] - dist_contracted_[q2][p1];
                        if (pathlen_min1 > pathlen_max || pathlen_min2 > pathlen_max) continue;

                        vector<vector<int>> shortest_path1s = shortestPaths(q1, p2);
                        vector<vector<int>> shortest_path2s = shortestPaths(q2, p1);
                        vector<vector<int>> contracted_path1s = shortestPaths(q1, p2, true);
                        vector<vector<int>> contracted_path2s = shortestPaths(q2, p1, true);
                        
                        for (int pathlen1 = pathlen_min1;pathlen1 <= pathlen_max; pathlen1++) {
                            for (int pathlen2 = pathlen_min2;pathlen2 <= pathlen_max; pathlen2++) {
                                if (pathlen1 + pathlen2 + dist_contracted_[q1][p2] + dist_contracted_[q2][p1] > 3) {
                                    continue;
                                }
                                if (checkShortCycle(p1, q1, pathlen1, cutSize)) {
                                    continue;
                                }
                                if (checkShortCycle(q2, p2, pathlen2, cutSize)) {
                                    continue;
                                }
                                bool has_smallcut = false;
                                for (const auto &shortest_path1 : shortest_path1s) {
                                    for (const auto &shortest_path2 : shortest_path2s) {
                                        if (canBeAlmostMinimal2(shortest_path1, shortest_path2, pathlen1, pathlen2, cutSize)) {
                                            continue;
                                        }
                                        auto [s, t] = sizeOfVertices2(shortest_path1, shortest_path2);
                                        int sz = max(s - max(pathlen1 + pathlen2 - 2, 0) + 1, 0) / 2 + t;
                                        if (isForbiddenCut(shortest_path1.size()+shortest_path2.size()-2+pathlen1+pathlen2, sz)) {
                                            has_smallcut = true;
                                            break;
                                        }
                                    }
                                    if (has_smallcut) break;
                                }
                                if (has_smallcut) {
                                    continue;
                                }
                                for (const auto &contracted_path1 : contracted_path1s) {
                                    for (const auto &contracted_path2 : contracted_path2s) {
                                        if ((int)contracted_path1.size() - 1 == dist_[q1][p2] && (int)contracted_path2.size() - 1 == dist_[q2][p1]) continue;
                                        auto reducing_component = getComponent2(contracted_path1, contracted_path2);
                                        for (int v : reducing_component) {
                                            bool equivalent_path = false;
                                            for (int u : contracted_path1) {
                                                if (equivalent(v, u)) equivalent_path = true;
                                            }
                                            for (int u : contracted_path2) {
                                                if (equivalent(v, u)) equivalent_path = true;
                                            }
                                            if (equivalent_path) continue;
                                            is_reductable[v] = true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return;
    }
   
    // configuration の外を通る 2,3-cut reduction で消える可能性のある頂点かどうかを表すフラグを計算する。
    vector<bool> calcReductableVertices(int cutSize) const {
        assert(cutSize == 6 || cutSize == 7);
        vector<bool> is_reductable(n_, false);
        calcReductableVertices1(cutSize, is_reductable);
        calcReductableVertices2(cutSize, is_reductable);
        calcReductableVertices3(cutSize, is_reductable);
        calcReductableVertices4(cutSize, is_reductable);
        return is_reductable;
    }

    bool forbiddenCycle(int a, int b, int k, int cutSize) const {
        assert(cutSize == 6 || cutSize == 7);
        assert(k <= cutSize);
        int b_ = a < b ? b : b + r_;
        int q = b_ - a;

        if (q == k) {
            return false;
        } else if (q < k) {
            // D := C - P + Q
            return true;
        } else {
            // E := P + R 
            return checkShortCycle(a, b, k, cutSize);
        }
    }

    bool forbiddenCycleOneEdge(int a, int b, int k, int cutSize) const {
        assert(cutSize == 6 || cutSize == 7);
        assert(k <= cutSize);
        int b_ = a < b ? b : b + r_;
        int q = b_ - a;

        // D := C - P + Q + one edge
        vector<int> Q(1+b_-a);
        for (int v = a;v < b_ + 1; v++) {
            Q[v - a] = v % r_;
        }
        std::reverse(Q.begin(), Q.end());
        auto [s, t] = sizeOfVertices(Q);
        int sz = max(s - max(cutSize - k - 1, 0) + 1, 0) / 2 + t;
        int l = cutSize - k + q + 1;
        if (!(l == 7 && cutSize == 6) && 
            isForbiddenCut(l, sz)) {
            return true;
        }

        assert(a != b);
        const vector<vector<int>> &abpaths = all_paths_[a][b];
        for (auto R : abpaths) {
            int m = (int)R.size() - 1;

            int number_in_ring = 0;
            for (size_t i = 0;i < R.size() - 1; i++) {
                if (R[i] < r_ && R[i + 1] < r_) number_in_ring++;
            }
            // + R の辺のうち 2 本以下を除いて ring の辺であり、 P + R + one edge が 7 サイクルで 6 サイクルの中にある
            // 場合は矛盾しているとは言えない。
            if (((m <= 2 || number_in_ring >= m - 2) && 
                 k + m + 1 == 7 && cutSize == 6)) {
                continue;
            }

            // E := P + R + one edge
            auto [s, t] = sizeOfVertices(R);
            int sz = max(s - max(k - 1, 0) + 1, 0) / 2 + t;
            if (isForbiddenCut(k + m + 1, sz)) {
                return true;
            }
        }
        return false;
    }

    // 長さが cutSize であるサイクルに囲われているときの length_onedge を計算する。
    vector<vector<int>> calcLowerBoundLengthOuterPath(int cutSize) const {
        vector<vector<int>> length(r_, vector<int>(r_, 0));
        for (int p = 0;p < r_; p++) {
            for (int q = 0;q < r_; q++) {
                if (p == q) continue;
                if (p + 1 == q || (p == r_ - 1 && q == 0)) {
                    length[p][q] = 1;
                    continue;
                }
                int k = 0;
                while (1) {
                    if (k > cutSize || !forbiddenCycle(p, q, k, cutSize)) {
                        length[p][q] = k;
                        break;
                    }
                    ++k;
                }
            }
        }
        return length;
    }

    // 長さが cutSize であるサイクルに囲われているときの length_onedge を計算する。
    vector<vector<int>> calcLowerBoundLengthOuterPathOneEdge(int cutSize) const {
        vector<vector<int>> length_oneedge(r_, vector<int>(r_, 0));
        for (int p = 0;p < r_; p++) {
            for (int q = 0;q < r_; q++) {
                if (p == q) continue;
                if (p + 1 == q || (p == r_ - 1 && q == 0)) {
                    length_oneedge[p][q] = 1;
                    continue;
                }
                int k = 1;
                while (1) {
                    if (k > cutSize || !forbiddenCycleOneEdge(p, q, k, cutSize)) {
                        length_oneedge[p][q] = k;
                        break;
                    }
                    ++k;
                }
            }
        }
        return length_oneedge;
    }

    bool isValid(const vector<int> &vs, const vector<int> &lens, const vector<bool> &onedge) const {
        assert(vs.size() == lens.size());
        assert(vs.size() == onedge.size());
        int cutSize = std::accumulate(lens.begin(), lens.end(), 0);
        assert(cutSize == 6 || cutSize == 7);
        
        size_t m = vs.size();
        for (size_t i = 0;i < m; i++) {
            if (onedge[i] && onedge[(i + 1) % m]) {
                continue;
            }
            if (onedge[i] || onedge[(i + 1) % m]) {
                if (forbiddenCycleOneEdge(vs[i], vs[(i+1) % m], lens[i], cutSize) ||
                    forbiddenCycleOneEdge(vs[(i+1) % m], vs[i], cutSize - lens[i], cutSize)) {
                    return false;
                }
            } else {
                if (forbiddenCycle(vs[i], vs[(i+1) % m], lens[i], cutSize) ||
                    forbiddenCycle(vs[(i+1) % m], vs[i], cutSize - lens[i], cutSize)) {
                    return false;
                }
            }
        }
        return true;
    }

    // 縮約後の component に含まれる頂点の数を計算する。
    pair<int, int> vertexSizeAfterContract(const vector<int> &component, int cutSize) const {
        assert(cutSize == 6 || cutSize == 7);
        const vector<bool> &is_reductable_outside = cutSize == 6 ? is_reductable_outside6_ : is_reductable_outside7_;

        int s = 0; // ring
        int t = 0; // inside ring
        for (int v : component) {
            if (is_reductable_inside_[v] || is_reductable_outside[v]) {
                continue;
            }
            if (v < r_ && representative_[v] == v) {
                s++;
            } else if (v >= r_ && representative_[v] == v) {
                t++;
            }
        }

        return std::make_pair(s, t);
    }

    // リングの頂点の集合 vs の頂点を順番に通るパスであって、vs[i], vs[i+1] (i=0,...,vs.size()-2) を
    // 縮約後の最短路で結ぶようなものを考え、vs[0] と vs[-1] を conf の外側で結ぶ長さ k のパスと合わせて、
    // 縮約後のグラフに既存のスナークに存在しないサイクルができていることを確認する。
    // rev = false のときは、vs[0]+1, vs[0]+2, ... , vs[-1]-1 を含む連結成分を考える。
    // rev = true のときは、true のときとは逆側を含む連結成分を考える。
    bool forbiddenVertexSize(const vector<int> &vs, int k, int cutSize, bool rev=false) const {
        assert(vs.size() >= 2);

        int l = k;
        vector<int> path = {vs[0]};
        for (size_t i = 0;i < vs.size() - 1; i++) {
            assert(vs[i] < r_);
            assert(dist_contracted_[vs[i]][vs[i + 1]] <= 1);
            l += dist_contracted_[vs[i]][vs[i + 1]];
            vector<int> path_i = shortestPaths(vs[i], vs[i + 1], true)[0];
            path.insert(path.end(), path_i.begin() + 1, path_i.end());
        }
        assert(vs.back() < r_);
        if (rev) {
            std::reverse(path.begin(), path.end());
        }

        vector<int> component = getComponent(path);
        auto [s, t] = vertexSizeAfterContract(component, cutSize);
        int sz = max(s - (k-1) + 1, 0) / 2 + t;

        return (l == 4 && sz > 0) || (l == 5 && sz > 1) || (l == 6 && sz > 2);
    }

    // リングの頂点の集合 vs1 の頂点を順番に通るパスであって、vs1[i], vs1[i+1] (i=0,...,vs1.size()-2) を
    // 縮約後の最短路で結ぶようなものと vs2 でも同様のパスを考えて、
    // それぞれ vs1[-1] と vs2[0], vs2[-1] と vs1[0] を結ぶ長さ k1, k2 のパスがあるとき、
    // 縮約後のグラフに既存のスナークに存在しないサイクルができていることを確認する。
    bool forbiddenVertexSize(const vector<int> &vs1, const vector<int> &vs2, int k1, int k2, int cutSize) const {
        int l = k1 + k2;
        assert(vs1.size() >= 2);
        vector<int> path1 = {vs1[0]};
        for (size_t i = 0;i < vs1.size() - 1; i++) {
            assert(vs1[i] < r_);
            assert(dist_contracted_[vs1[i]][vs1[i + 1]] <= 1);
            l += dist_contracted_[vs1[i]][vs1[i + 1]];
            vector<int> path_i = shortestPaths(vs1[i], vs1[i + 1], true)[0];
            path1.insert(path1.end(), path_i.begin() + 1, path_i.end());
        }
        assert(vs1.back() < r_);

        assert(vs2.size() >= 2);
        vector<int> path2 = {vs2[0]};
        for (size_t i = 0;i < vs2.size() - 1; i++) {
            assert(vs2[i] < r_);
            assert(dist_contracted_[vs2[i]][vs2[i + 1]] <= 1);
            l += dist_contracted_[vs2[i]][vs2[i + 1]];
            vector<int> path_i = shortestPaths(vs2[i], vs2[i + 1], true)[0];
            path2.insert(path2.end(), path_i.begin() + 1, path_i.end());
        }
        assert(vs2.back() < r_);

        vector<int> component = getComponent(path1, path2);
        auto [s, t] = vertexSizeAfterContract(component, cutSize);
        int sz = max(s - max(k1+k2-2, 0) + 1, 0) / 2 + t;

        return (l == 4 && sz > 0) || (l == 5 && sz > 1) || (l == 6 && sz > 2);
    }

    // 7 サイクルの中の conf の辺を縮約したあと、そのサイクルの外の頂点を含む 2,3-cut reduction は起きないとしたとき、
    // 次数 7 が 1 点だけの状況になっているかをチェックする。
    bool checkDegree7(void) const {
        vector<set<int>> VtoV_contracted(n_);
        for (int v = 0;v < n_; v++) {
            if (is_reductable_inside_[v] || is_reductable_outside7_[v]) continue;
            for (int u : VtoV_[v]) {
                if (is_reductable_inside_[u] || is_reductable_outside7_[u]) continue;
                VtoV_contracted[representative_[v]].insert(representative_[u]);
                VtoV_contracted[representative_[u]].insert(representative_[v]);
            }
        }

        int n_ring = 0, n_conf = 0;
        bool not_deg7 = false;
        for (int v = 0;v < n_; v++) {
            if (is_reductable_inside_[v] || is_reductable_outside7_[v]) continue;
            if (v < r_ && representative_[v] == v) n_ring++;
            if (v >= r_ && representative_[v] == v) {
                n_conf++;
                if (VtoV_contracted[v].size() != 7) {
                    not_deg7 = true;
                    break;
                }
            }
        }
        return (n_conf >= 2 || not_deg7);
    }
};


// 双対グラフの辺で edgeids の id を持つ辺に対応する主グラフの辺を返す。
vector<pair<int, int>> edgeFromId(const Configuration &conf, const vector<int> &edgeids) {
    auto is3Cycle = [&] (int x, int y, int z) {
        return conf.VtoV_.at(x).count(y) && conf.VtoV_.at(y).count(z) && conf.VtoV_.at(z).count(x);
    };
    set<tuple<int, int, int>> triangles;
    for (int i = 0; i < conf.n_; i++) {
        for (int j = 0; j < i; j++) {
            for (int k = 0; k < j; k++) {
                if (is3Cycle(k, j, i)) {
                    triangles.insert({k, j, i});
                }
            }
        }
    }

    map<pair<int, int>, int> indexOfEdge;
    vector<pair<int, int>> edgeOfIndex;
    int counter = 0;
    auto addEdge = [&] (int x, int y) {
        if (x > y) std::swap(x, y);
        if (!indexOfEdge.count({x, y})) {
            indexOfEdge[{x, y}] = counter++;
            edgeOfIndex.push_back({x, y});
        }
    };
    for (int i = 0; i < conf.r_; i++) {
        addEdge(i, (i+1) % conf.r_);
    }
    for (auto tri : triangles) {
        auto [a,b,c] = tri;
        addEdge(a, b);
        addEdge(b, c);
        addEdge(c, a);
    }

    vector<pair<int, int>> primal_edges(edgeids.size());
    for (size_t i = 0;i < edgeids.size(); i++) {
        primal_edges[i] = edgeOfIndex[edgeids[i]];
    }
    
    return primal_edges;
}

string join(const vector<pair<int, int>> &edges) {
    string res = "";
    for (const auto &e : edges) {
        res += fmt::format("({}, {}), ", e.first, e.second);
    }
    return res;
}

vector<int> reductableVertices(int n, const vector<bool> &is_reductable) {
    vector<int> reductable_vertices;
    for (int v = 0;v < n; v++) {
        if (is_reductable[v]) {
            reductable_vertices.push_back(v);
        }
    }
    return reductable_vertices;
}

// a,b は ring にその順に並んでいる頂点
// dist[a][b] = d0
vector<pair<int, int>> find_ab(int d0, int n, int r, const vector<vector<int>> &contract_dist) {
    vector<pair<int, int>> abs;
    for (int a = 0;a < r; a++) {
        for (int b = a+1;b < r; b++) {
            if (contract_dist[a][b] == d0) {
                abs.emplace_back(a, b);
            }
        }
    }
    return abs;
}

// a,b,c は ring にその順に並んでいる頂点
// dist[a][b] = d0
// dist[b][c] = d1
vector<tuple<int, int, int>> find_ab_bc(int d0, int d1, int n, int r, const vector<vector<int>> &contract_dist) {
    vector<tuple<int, int, int>> abcs;
    for (int a = 0;a < r; a++) {
        for (int b = a+1;b < r; b++) {
            if (contract_dist[a][b] == d0) {
                for (int c = a+1;c < b; c++) {
                    if (contract_dist[a][c] == d1) {
                        abcs.emplace_back(b, a, c);
                    }
                }
                for (int c = b+1;c < a+r; c++) {
                    if (contract_dist[b][c%r] == d1) {
                        abcs.emplace_back(a, b, c%r);
                    }
                }
            }
        }
    }
    std::sort(abcs.begin(), abcs.end());
    abcs.erase(std::unique(abcs.begin(), abcs.end()), abcs.end());
    return abcs;
}

// a,b,c は ring にその順に並んでいる頂点
// dist[a][b] = d0
// dist[a][c] = d1
// dist[b][c] = d2
vector<tuple<int, int, int>> find_ab_ac_bc(int d0, int d1, int d2, int n, int r, const vector<vector<int>> &contract_dist) {
    vector<tuple<int, int, int>> abcs;
    for (int a = 0;a < r; a++) {
        for (int b = a+1;b < r; b++) {
            if (contract_dist[a][b] == d0) {
                for (int c = a+1;c < b; c++) {
                    if (contract_dist[b][c] == d1 && contract_dist[a][c] == d2) {
                        abcs.emplace_back(b, a, c);
                    }
                }
                for (int c = b+1;c < a+r; c++) {
                    if (contract_dist[a][c%r] == d1 && contract_dist[b][c%r] == d2) {
                        abcs.emplace_back(a, b, c%r);
                    }
                }
            }
        }
    }
    std::sort(abcs.begin(), abcs.end());
    abcs.erase(std::unique(abcs.begin(), abcs.end()), abcs.end());
    return abcs;
}

// a,b,c,d は ring にその順に並んでいる頂点
// dist[a][b] = d0
// dist[c][d] = d1
vector<tuple<int, int, int, int>> find_ab_cd(int d0, int d1, int n, int r, const vector<vector<int>> &contract_dist) {
    vector<tuple<int, int, int, int>> abcds;
    for (int a = 0;a < r; a++) {
        for (int b = a+1;b < r; b++) {
            if (contract_dist[a][b] == d0) {
                for (int c = b+1;c < a+r; c++) {
                    for (int d = c+1;d < a+r; d++) {
                        if (contract_dist[c%r][d%r] == d1) {
                            abcds.emplace_back(a, b, c%r, d%r);
                        }
                    }
                }
                for (int c = a+1;c < b; c++) {
                    for (int d = c+1;d < b; d++) {
                        if (contract_dist[c][d] == d1) {
                            abcds.emplace_back(b, a, c, d);
                        }
                    }
                }
            }
        }
    }
    std::sort(abcds.begin(), abcds.end());
    abcds.erase(std::unique(abcds.begin(), abcds.end()), abcds.end());
    return abcds;
}

// a,b,c,d は ring にその順に並んでいる頂点
// dist[a][b] = d0
// dist[b][c] = d1
// dist[c][d] = d2
vector<tuple<int, int, int, int>> find_ab_bc_cd(int d0, int d1, int d2, int n, int r, const vector<vector<int>> &contract_dist) {
    vector<tuple<int, int, int, int>> abcds;
    for (int a = 0;a < r; a++) {
        for (int b = a+1;b < r; b++) {
            if (contract_dist[a][b] == d0) {
                for (int c = b+1;c < a+r; c++) {
                    if (contract_dist[b][c%r] == d1) {
                        for (int d = c+1;d < a+r; d++) {
                            if (contract_dist[c%r][d%r] == d2) {
                                abcds.emplace_back(a, b, c%r, d%r);
                            }
                        }
                    }
                }
                for (int c = a+1;c < b; c++) {
                    if (contract_dist[a][c] == d1) {
                        for (int d = c+1;d < b; d++) {
                            if (contract_dist[c][d] == d2) {
                                abcds.emplace_back(b, a, c, d);
                            }
                        }
                    }
                }
            }
        }
    }
    std::sort(abcds.begin(), abcds.end());
    abcds.erase(std::unique(abcds.begin(), abcds.end()), abcds.end());
    return abcds;
}

// a,b,c,d,e は ring にその順に並んでいる頂点
// dist[a][b] = d0
// dist[b][c] = d1
// dist[d][e] = d2
vector<tuple<int, int, int, int, int>> find_ab_bc_de(int d0, int d1, int d2, int n, int r, const vector<vector<int>> &contract_dist) {
    vector<tuple<int, int, int, int, int>> abcdes;
    for (int a = 0;a < r; a++) {
        for (int b = a+1;b < r; b++) {
            if (contract_dist[a][b] == d0) {
                for (int c = b+1;c < a+r; c++) {
                    if (contract_dist[b][c%r] == d1) {
                        for (int d = c+1;d < a+r; d++) {
                            for (int e = d+1;e < a+r; e++) {
                                if (contract_dist[d%r][e%r] == d2) {
                                    abcdes.emplace_back(a, b, c%r, d%r, e%r);
                                }
                            }
                        }
                    }
                }
                for (int c = a+1;c < b; c++) {
                    if (contract_dist[a][c] == d1) {
                        for (int d = c+1;d < b; d++) {
                            for (int e = d+1;e < b; e++) {
                                if (contract_dist[d][e] == d2) {
                                    abcdes.emplace_back(b, a, c, d, e);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    std::sort(abcdes.begin(), abcdes.end());
    abcdes.erase(std::unique(abcdes.begin(), abcdes.end()), abcdes.end());
    return abcdes;
}

void check(const string &filename, const vector<int> &edgeids) {
    spdlog::info("filename: {}", filename);
    Configuration conf = Configuration::readConfFile(filename);
    vector<pair<int, int>> edges = edgeFromId(conf, edgeids);

    conf.setContract(edges);

    vector<vector<int>> contract_dist = conf.WF(true);

    vector<pair<int, int>> ab0s = find_ab(0, conf.n_, conf.r_, contract_dist);
    vector<pair<int, int>> ab1s = find_ab(1, conf.n_, conf.r_, contract_dist);

    vector<tuple<int, int, int>> ab0_bc1s = find_ab_bc(0, 1, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int>> ab1_bc0s = find_ab_bc(1, 0, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int>> ab1_bc1s = find_ab_bc(1, 1, conf.n_, conf.r_, contract_dist);

    vector<tuple<int, int, int>> ab0_ac0_bc0s = find_ab_ac_bc(0, 0, 0, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int>> ab0_ac1_bc1s = find_ab_ac_bc(0, 1, 1, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int>> ab1_ac1_bc1s = find_ab_ac_bc(1, 1, 1, conf.n_, conf.r_, contract_dist);

    vector<tuple<int, int, int, int>> ab0_cd0s = find_ab_cd(0, 0, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int>> ab0_cd1s = find_ab_cd(0, 1, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int>> ab1_cd1s = find_ab_cd(1, 1, conf.n_, conf.r_, contract_dist);
    
    vector<tuple<int, int, int, int>> ab0_bc0_cd0s = find_ab_bc_cd(0, 0, 0, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int>> ab0_bc0_cd1s = find_ab_bc_cd(0, 0, 1, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int>> ab0_bc1_cd0s = find_ab_bc_cd(0, 1, 0, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int>> ab0_bc1_cd1s = find_ab_bc_cd(0, 1, 1, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int>> ab1_bc0_cd0s = find_ab_bc_cd(1, 0, 0, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int>> ab1_bc0_cd1s = find_ab_bc_cd(1, 0, 1, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int>> ab1_bc1_cd0s = find_ab_bc_cd(1, 1, 0, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int>> ab1_bc1_cd1s = find_ab_bc_cd(1, 1, 1, conf.n_, conf.r_, contract_dist);

    vector<tuple<int, int, int, int, int>> ab0_bc0_de0s = find_ab_bc_de(0, 0, 0, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int, int>> ab0_bc1_de0s = find_ab_bc_de(0, 1, 0, conf.n_, conf.r_, contract_dist);
    vector<tuple<int, int, int, int, int>> ab1_bc0_de0s = find_ab_bc_de(1, 0, 0, conf.n_, conf.r_, contract_dist);

    // check loop except two difficutl types of loops
    conf.canHaveContractibleLoop();

    // 6cut-1
    for (auto [a, b]: ab0s) {
        if (conf.isValid(vector<int>{a, b}, vector<int>{2, 4}, vector<bool>{false, false})
            && !conf.forbiddenVertexSize(vector<int>{b, a}, 4, 6)) {
            spdlog::info("6cut-1 (24) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{4, 2}, vector<bool>{false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, 4, 6)) {
            spdlog::info("6cut-1 (42) ({}, {}) is dangerous in {}", a, b, filename);
        }
    }

    // 6cut-2
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{false, false, false, false})) {
            spdlog::info("6cut-2 (2121) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 6cut-3
    for (auto [a, b, c]: ab0_ac0_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{false, false, false})) {
            spdlog::info("6cut-3 (222) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }

    // 6cut-4
    for (auto [a, b, c, d]: ab0_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{false, false, false, false})) {
            spdlog::info("6cut-4 (2121) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{true, false, false, false})) {
            spdlog::info("6cut-4 (2121-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{false, true, false, false})) {
            spdlog::info("6cut-4 (2121-2) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{false, false, true, false})) {
            spdlog::info("6cut-4 (2121-3) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{false, false, false, true})) {
            spdlog::info("6cut-4 (2121-4) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 6cut-5
    for (auto [a, b, c]: ab0_ac1_bc1s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{false, false, false})) {
            spdlog::info("6cut-5 (222) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab0_ac0_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{true, false, false})) {
            spdlog::info("6cut-5 (222-1) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{false, true, false})) {
            spdlog::info("6cut-5 (222-2) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{false, false, true})) {
            spdlog::info("6cut-5 (222-3) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }

    // 6cut-6
    for (auto [a, b]: ab0s) {
        if (conf.isValid(vector<int>{a, b}, vector<int>{3, 3}, vector<bool>{false, false})) {
            spdlog::info("6cut-6 (33) ({}, {}) is dangerous in {}", a, b, filename);
        }
    }

    // 6cut-7
    for (auto [a, b]: ab1s) {
        if (conf.isValid(vector<int>{a, b}, vector<int>{2, 4}, vector<bool>{false, false})
            && !conf.forbiddenVertexSize(vector<int>{b, a}, 4, 6)) {
            spdlog::info("6cut-7 (24) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{4, 2}, vector<bool>{false, false}) 
            && !conf.forbiddenVertexSize(vector<int>{a, b}, 4, 6) ) {
            spdlog::info("6cut-7 (42) ({}, {}) is dangerous in {}", a, b, filename);
        }
    }
    for (auto [a, b]: ab0s) {
        if (conf.isValid(vector<int>{a, b}, vector<int>{2, 4}, vector<bool>{true, false}) 
            && !conf.forbiddenVertexSize(vector<int>{b, a}, 5, 6)) {
            spdlog::info("6cut-7 (24-1) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{4, 2}, vector<bool>{true, false}) 
            && !conf.forbiddenVertexSize(vector<int>{a, b}, 5, 6)) {
            spdlog::info("6cut-7 (42-1) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{2, 4}, vector<bool>{false, true}) 
            && !conf.forbiddenVertexSize(vector<int>{b, a}, 5, 6)) {
            spdlog::info("6cut-7 (24-2) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{4, 2}, vector<bool>{false, true}) 
            && !conf.forbiddenVertexSize(vector<int>{a, b}, 5, 6)) {
            spdlog::info("6cut-7 (42-2) ({}, {}) is dangerous in {}", a, b, filename);
        }
    }

    // 6cut-8
    for (auto [a, b, c, d]: ab1_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{false, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 1, 6)) {
            spdlog::info("6cut-8 (2121) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{true, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 1, 6)) {
            spdlog::info("6cut-8 (2121-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{false, true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 1, 6)) {
            spdlog::info("6cut-8 (2121-2) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{true, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 3, 1, 6)) {
            spdlog::info("6cut-8 (2121-14) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{false, true, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 3, 1, 6)) {
            spdlog::info("6cut-8 (2121-23) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{true, false, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 6)) {
            spdlog::info("6cut-8 (2121-13) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 1}, vector<bool>{false, true, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 6)) {
            spdlog::info("6cut-8 (2121-24) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 6cut-9
    for (auto [a, b, c]: ab1_bc1s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 2, 6, true)) {
            spdlog::info("6cut-9 (222) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab0_bc1s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 3, 6, true)) {
            spdlog::info("6cut-9 (222-1) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab1_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 3, 6, true)) {
            spdlog::info("6cut-9 (222-3) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab0_ac0_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{true, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 4, 6, true)) {
            spdlog::info("6cut-9 (222-13) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{b, c, a}, vector<int>{2, 2, 2}, vector<bool>{true, false, true})
            && !conf.forbiddenVertexSize(vector<int>{b, c, a}, 4, 6, true)) {
            spdlog::info("6cut-9 (222-13) ({}, {}, {}) is dangerous in {}", b, c, a, filename);
        }
        if (conf.isValid(vector<int>{c, a, b}, vector<int>{2, 2, 2}, vector<bool>{true, false, true})
            && !conf.forbiddenVertexSize(vector<int>{c, a, b}, 4, 6, true)) {
            spdlog::info("6cut-9 (222-13) ({}, {}, {}) is dangerous in {}", c, a, b, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 0}, vector<bool>{true, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 6)) {
            spdlog::info("6cut-9 (2220-14) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 0, 2, 2}, vector<bool>{false, true, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 6)) {
            spdlog::info("6cut-9 (2022-23) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 6cut-10
    for (auto [a, b, c]: ab1_ac1_bc1s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 2}, vector<bool>{false, false, false})) {
            spdlog::info("6cut-10 (222) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_bc1_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 0}, vector<bool>{true, false, false, true})) {
            spdlog::info("6cut-10 (2220-14) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 7cut-1
    for (auto [a, b]: ab0s) {
        if (conf.isValid(vector<int>{a, b}, vector<int>{2, 5}, vector<bool>{false, false})
            && !conf.forbiddenVertexSize(vector<int>{b, a}, 5, 7)) {
            spdlog::info("7cut-1 (25) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{5, 2}, vector<bool>{false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, 5, 7)) {
            spdlog::info("7cut-1 (52) ({}, {}) is dangerous in {}", a, b, filename);
        }
    }

    // 7cut-2
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{3, 1, 2, 1}, vector<bool>{false, false, false, false})) {
            spdlog::info("7cut-2 (3121) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 3, 1}, vector<bool>{false, false, false, false})) {
            spdlog::info("7cut-2 (2131) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 7cut-3
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{false, false, false, false})) {
            spdlog::info("7cut-3 (2122) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, false})) {
            spdlog::info("7cut-3 (2221) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 7cut-4
    for (auto [a, b, c]: ab0_ac0_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{3, 2, 2}, vector<bool>{false, false, false})) {
            spdlog::info("7cut-4 (322) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 3, 2}, vector<bool>{false, false, false})) {
            spdlog::info("7cut-4 (232) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 3}, vector<bool>{false, false, false})) {
            spdlog::info("7cut-4 (223) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }

    // 7cut-5
    for (auto [a, b, c]: ab0_bc1s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 3}, vector<bool>{false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 3, 7, true)) {
            spdlog::info("7cut-5 (223) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab1_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 3}, vector<bool>{false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 3, 7, true)) {
            spdlog::info("7cut-5 (223) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab0_ac0_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 3}, vector<bool>{true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 4, 7, true)) {
            spdlog::info("7cut-5 (223-1) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{b, c, a}, vector<int>{2, 2, 3}, vector<bool>{true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{b, c, a}, 4, 7, true)) {
            spdlog::info("7cut-5 (223-1) ({}, {}, {}) is dangerous in {}", b, c, a, filename);
        }
        if (conf.isValid(vector<int>{c, a, b}, vector<int>{2, 2, 3}, vector<bool>{true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{c, a, b}, 4, 7, true)) {
            spdlog::info("7cut-5 (223-1) ({}, {}, {}) is dangerous in {}", c, a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{3, 2, 2}, vector<bool>{true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{b, c, a}, 4, 7, true)) {
            spdlog::info("7cut-5 (223-1) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{b, c, a}, vector<int>{3, 2, 2}, vector<bool>{true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{c, a, b}, 4, 7, true)) {
            spdlog::info("7cut-5 (223-1) ({}, {}, {}) is dangerous in {}", b, c, a, filename);
        }
        if (conf.isValid(vector<int>{c, a, b}, vector<int>{3, 2, 2}, vector<bool>{true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 4, 7, true)) {
            spdlog::info("7cut-5 (223-1) ({}, {}, {}) is dangerous in {}", c, a, b, filename);
        }
    }

    // 7cut-6
    for (auto [a, b, c, d]: ab0_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{false, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 2, 7)) {
            spdlog::info("7cut-6 (2122) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 2, 7)) {
            spdlog::info("7cut-6 (2221) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{true, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 3, 7)) {
            spdlog::info("7cut-6 (2122-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 3, 7)) {
            spdlog::info("7cut-6 (2221-2) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 3, 7)) {
            spdlog::info("7cut-6 (2221-3) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{false, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 3, 7)) {
            spdlog::info("7cut-6 (2122-4) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 7)) {
            spdlog::info("7cut-6 (2221-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{false, true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 7)) {
            spdlog::info("7cut-6 (2122-2) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{false, false, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 7)) {
            spdlog::info("7cut-6 (2122-3) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 7)) {
            spdlog::info("7cut-6 (2221-4) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 7cut-7
    for (auto [a, b, c, d]: ab0_bc1_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, false})) {
            spdlog::info("7cut-7 (2221) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab1_bc1_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, false})) {
            spdlog::info("7cut-7 (2221) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_bc1_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false ,false, false})) {
            spdlog::info("7cut-7 (2221-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false ,false, true})) {
            spdlog::info("7cut-7 (2221-4) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d, e]: ab0_bc0_de0s) {
        if (conf.isValid(vector<int>{a, b, c, d, e}, vector<int>{2, 2, 0, 2, 1}, vector<bool>{false, false, true, true, false})) {
            spdlog::info("7cut-7 (22021-34) ({}, {}, {}, {}, {}) is dangerous in {}", a, b, c, d, e, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d, e}, vector<int>{2, 2, 1, 2, 0}, vector<bool>{true, false, false, false, true})) {
            spdlog::info("7cut-7 (22120-15) ({}, {}, {}, {}, {}) is dangerous in {}", a, b, c, d, e, filename);
        }
    }

    // 7cut-8
    for (auto [a, b, c, d]: ab1_bc0_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, false})) {
            spdlog::info("7cut-8 (2221) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_bc0_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, false})) {
            spdlog::info("7cut-8 (2221-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab1_bc0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, true})) {
            spdlog::info("7cut-8 (2221-4) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_bc0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, true})) {
            spdlog::info("7cut-8 (2221-14) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{b, c, d, a}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, true})) {
            spdlog::info("7cut-8 (2221-14) ({}, {}, {}, {}) is dangerous in {}", b, c, d, a, filename);
        }
        if (conf.isValid(vector<int>{c, d, a, b}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, true})) {
            spdlog::info("7cut-8 (2221-14) ({}, {}, {}, {}) is dangerous in {}", c, d, a, b, filename);
        }
        if (conf.isValid(vector<int>{d, a, b, c}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, true})) {
            spdlog::info("7cut-8 (2221-14) ({}, {}, {}, {}) is dangerous in {}", d, a, b, c, filename);
        }
    }

    // 7cut-9
    for (auto [a, b]: ab0s) {
        if (conf.isValid(vector<int>{a, b}, vector<int>{3, 4}, vector<bool>{false, false})) {
            spdlog::info("7cut-9 (34) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{4, 3}, vector<bool>{false, false})) {
            spdlog::info("7cut-9 (43) ({}, {}) is dangerous in {}", a, b, filename);
        }
    }

    // 7cut-10
    for (auto [a, b, c]: ab0_ac1_bc1s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{3, 2, 2}, vector<bool>{false, false, false})) {
            spdlog::info("7cut-10 (322) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab0_ac0_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 3, 2}, vector<bool>{true, false, false})) {
            spdlog::info("7cut-10 (232-1) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 3}, vector<bool>{false, true, false})) {
            spdlog::info("7cut-10 (223-2) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{3, 2, 2}, vector<bool>{false, false, true})) {
            spdlog::info("7cut-10 (322-3) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }

    // 7cut-11
    for (auto [a, b, c, d]: ab0_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{3, 1, 2, 1}, vector<bool>{false, false, false, false})) {
            spdlog::info("7cut-11 (3121) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 3, 1}, vector<bool>{true, false, false, false})) {
            spdlog::info("7cut-11 (2131-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 3, 1}, vector<bool>{false, true, false, false})) {
            spdlog::info("7cut-11 (2131-2) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{3, 1, 2, 1}, vector<bool>{false, false, true, false})) {
            spdlog::info("7cut-11 (3121-3) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{3, 1, 2, 1}, vector<bool>{false, false, false, true})) {
            spdlog::info("7cut-11 (3121-4) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 7cut-12
    for (auto [a, b]: ab1s) {
        if (conf.isValid(vector<int>{a, b}, vector<int>{2, 5}, vector<bool>{false, false})
            && !conf.forbiddenVertexSize(vector<int>{b, a}, 5, 7)) {
            spdlog::info("7cut-12 (25) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{5, 2}, vector<bool>{false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, 5, 7)) {
            spdlog::info("7cut-12 (52) ({}, {}) is dangerous in {}", a, b, filename);
        }
    }
    for (auto [a, b]: ab0s) {
        if (conf.isValid(vector<int>{a, b}, vector<int>{2, 5}, vector<bool>{true, false})
            && !conf.forbiddenVertexSize(vector<int>{b, a}, 6, 7)) {
            spdlog::info("7cut-12 (25-1) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{5, 2}, vector<bool>{true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, 6, 7)) {
            spdlog::info("7cut-12 (52-1) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{2, 5}, vector<bool>{false, true})
            && !conf.forbiddenVertexSize(vector<int>{b, a}, 6, 7)) {
            spdlog::info("7cut-12 (25-2) ({}, {}) is dangerous in {}", a, b, filename);
        }
        if (conf.isValid(vector<int>{a, b}, vector<int>{5, 2}, vector<bool>{false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, 6, 7)) {
            spdlog::info("7cut-12 (52-2) ({}, {}) is dangerous in {}", a, b, filename);
        }
    }

    // 7cut-13 
    for (auto [a, b, c]: ab1_bc1s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 3}, vector<bool>{false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 3, 7, true)) {
            spdlog::info("7cut-13 (223) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab0_bc1s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 3}, vector<bool>{true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 4, 7, true)) {
            spdlog::info("7cut-13 (223-1) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab1_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 3}, vector<bool>{false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 4, 7, true)) {
            spdlog::info("7cut-13 (223-3) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c]: ab0_ac0_bc0s) {
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{3, 2, 2}, vector<bool>{true, true, false})
            && !conf.forbiddenVertexSize(vector<int>{b, c, a}, 5, 7, true)) {
            spdlog::info("7cut-13 (322-12) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 2, 3}, vector<bool>{true, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, 5, 7, true)) {
            spdlog::info("7cut-13 (223-13) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
        if (conf.isValid(vector<int>{a, b, c}, vector<int>{2, 3, 2}, vector<bool>{false, true, true})
            && !conf.forbiddenVertexSize(vector<int>{c, a, b}, 5, 7, true)) {
            spdlog::info("7cut-13 (232-23) ({}, {}, {}) is dangerous in {}", a, b, c, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 3, 2, 0}, vector<bool>{true, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 3, 7)) {
            spdlog::info("7cut-13 (2320-14) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 0, 2, 3}, vector<bool>{false, true, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 3, 7)) {
            spdlog::info("7cut-13 (2023-23) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 7cut-14
    for (auto [a, b, c, d]: ab1_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 2, 7)) {
            spdlog::info("7cut-14 (2221) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{false, false, false, false})
           && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 2, 7)) {
            spdlog::info("7cut-14 (2122) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{true, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 3, 7)) {
            spdlog::info("7cut-14 (2122-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 3, 7)) {
            spdlog::info("7cut-14 (2221-2) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 7)) {
            spdlog::info("7cut-14 (2221-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{false, true, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 2, 7)) {
            spdlog::info("7cut-14 (2122-2) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{true, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 4, 7)) {
            spdlog::info("7cut-14 (2122-14) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, true, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 1, 4, 7)) {
            spdlog::info("7cut-14 (2221-23) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 3, 7)) {
            spdlog::info("7cut-14 (2221-14) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{false, true, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 3, 7)) {
            spdlog::info("7cut-14 (2122-23) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{true, false, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 3, 7)) {
            spdlog::info("7cut-14 (2122-13) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, true, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 3, 7)) {
            spdlog::info("7cut-14 (2221-24) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 3, 7)) {
            spdlog::info("7cut-14 (2221-13) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 1, 2, 2}, vector<bool>{false, true, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b}, vector<int>{c, d}, 2, 3, 7)) {
            spdlog::info("7cut-14 (2122-24) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }

    // 7cut-15
    for (auto [a, b, c, d]: ab1_bc1_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c, d}, 1, 7, true)) {
            spdlog::info("7cut-15 (2221) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_bc1_cd1s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c, d}, 2, 7, true)) {
            spdlog::info("7cut-15 (2221-1) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab1_bc1_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{false, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c, d}, 2, 7, true)) {
            spdlog::info("7cut-15 (2221-4) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d]: ab0_bc1_cd0s) {
        if (conf.isValid(vector<int>{a, b, c, d}, vector<int>{2, 2, 2, 1}, vector<bool>{true, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c, d}, 3, 7, true)) {
            spdlog::info("7cut-15 (2221-14) ({}, {}, {}, {}) is dangerous in {}", a, b, c, d, filename);
        }
    }
    for (auto [a, b, c, d, e]: ab1_bc0_de0s) {
        if (conf.isValid(vector<int>{a, b, c, d, e}, vector<int>{2, 2, 0, 2, 1}, vector<bool>{false, false, true, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, vector<int>{d, e}, 1, 2, 7)) {
            spdlog::info("7cut-15 (22021-34) ({}, {}, {}, {}, {}) is dangerous in {}", a, b, c, d, e, filename);
        }
    }
    for (auto [a, b, c, d, e]: ab0_bc1_de0s) {
        if (conf.isValid(vector<int>{a, b, c, d, e}, vector<int>{2, 2, 1, 2, 0}, vector<bool>{true, false, false, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, vector<int>{d, e}, 1, 2, 7)) {
            spdlog::info("7cut-15 (22120-15) ({}, {}, {}, {}, {}) is dangerous in {}", a, b, c, d, e, filename);
        }
    }
    for (auto [a, b, c, d, e]: ab0_bc0_de0s) {
        if (conf.isValid(vector<int>{a, b, c, d, e}, vector<int>{2, 2, 1, 2, 0}, vector<bool>{true, false, true, false, true})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, vector<int>{d, e}, 2, 2, 7)) {
            spdlog::info("7cut-15 (22120-135) ({}, {}, {}, {}, {}) is dangerous in {}", a, b, c, d, e, filename);
        }
        if (conf.isValid(vector<int>{a, b, c, d, e}, vector<int>{2, 2, 0, 2, 1}, vector<bool>{true, false, true, true, false})
            && !conf.forbiddenVertexSize(vector<int>{a, b, c}, vector<int>{d, e}, 2, 2, 7)) {
            spdlog::info("7cut-15 (22021-134) ({}, {}, {}, {}, {}) is dangerous in {}", a, b, c, d, e, filename);
        }
    }

    // 7cut-16
    if (!conf.checkDegree7()) {
        spdlog::info("7cut-16 (degree 7 in 7-cycle) is dangerous in {}", filename);
    }

    return;
}


