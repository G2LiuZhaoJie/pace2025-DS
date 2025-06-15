#define _CRT_SECURE_NO_WARNINGS
// 平台检测
#ifdef _WIN32
#define NOMINMAX  // 关键！！禁止Windows的min/max宏
#include <windows.h>
#else
#include <unistd.h>
#include <csignal>
#endif
#include <climits>  // for INT_MAX
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <algorithm>
#include "parallel_hashmap/phmap.h"
#include <chrono>
#include <sstream>  // 添加stringstream支持
#include <csignal>
#include <random>
#include <queue>
#include "robin_hood.h"
using namespace std;
typedef unsigned ui;
typedef pair<ui, ui> pii;
typedef pair<ui, vector<pii>> edge_list_graph;
//using phmap::flat_hash_set;
//using phmap::flat_hash_map;
//using robin_hood::unordered_set;
using namespace std::chrono;
vector<pii> esss;
// 全局数据
vector<char> global_data = vector<char>();
ui num = 0; // 全局数据实例point_num
ui all_point = 0; // 全局数据实例point_num

vector<ui> best_dom_set;
ui min_size = UINT_MAX;

using Clock = std::chrono::steady_clock; // 单调时钟，不受系统时间调整影响
const auto deadline = Clock::now() + std::chrono::minutes(5);

void saveToFile(const string& filename);

template<class T>
struct closed_adj_t {
	T p_begin;
	T p_end;
	const char* p_mat;
	vector<robin_hood::unordered_set<ui>>::const_iterator p_set;


	T begin() { return p_begin; }
	T end() { return p_end; }
	size_t size() { return p_end - p_begin; }

	bool contains(ui v) const noexcept { return p_mat ? p_mat[v] : p_set->count(v); }
};

const ui thr_big = 5000;

class ugraph {
public:
	typedef vector<ui>::iterator iterator;
	typedef vector<ui>::const_iterator const_iterator;

	ui n;
	vector<ui> off, dst;
	vector<char> mat;
	vector<robin_hood::unordered_set<ui>> umap;

	ugraph() = default;
	ugraph(const ugraph&) = default;

	ugraph(ui n, const vector<pii>& es) : n(n), umap(n) {
		assign(n, es);
	}

	closed_adj_t<iterator> adj(ui u) {
		return closed_adj_t<iterator>{
			dst.begin() + off[u],
				dst.begin() + off[u + 1],
				n < thr_big ? &mat.front() + u * n : nullptr,
				umap.begin() + u,
		};
	}

	closed_adj_t<const_iterator> adj(ui u) const {
		return closed_adj_t<const_iterator>{
			dst.begin() + off[u],
				dst.begin() + off[u + 1],
				n < thr_big ? &mat.front() + u * n : nullptr,
				umap.begin() + u,
		};
	}

	closed_adj_t<iterator> operator[](ui u) {
		return adj(u);
	}

	closed_adj_t<const_iterator> operator[](ui u) const {
		return adj(u);
	}

	void assign(ui n, const vector<pii>& es) {
		this->n = n;
		off.assign(n + 1, 1); off.back() = 0;
		dst.assign(es.size() * 2 + n, ~0u);
		if (n < thr_big) {
			mat.assign(n * n, 0);
			for (ui i = 0; i < n; ++i)
				mat[n * i + i] = 1;
			for (pii e : es)
				mat[n * e.first + e.second] = mat[n * e.second + e.first] = 1;
		}
		for (pii e : es) {
			off[e.first]++;
			off[e.second]++;
			umap[e.first].insert(e.second);
			umap[e.second].insert(e.first);
		}
		for (ui i = 0; i < n; ++i)
			off[i + 1] += off[i];
		for (pii e : es) {
			dst[--off[e.first]] = e.second;
			dst[--off[e.second]] = e.first;
		}
		for (ui i = 0; i < n; ++i) {
			dst[--off[i]] = i;
			sort(adj(i).begin() + 1, adj(i).end());
		}

	}
};

ugraph read_graph_dimacs() {
	ui n, m; scanf("p ds %u %u", &n, &m);
	vector<pii> es(m);
	all_point = n;

	for (ui i = 0; i < m; ++i) {
		scanf("%u %u", &es[i].first, &es[i].second);
		es[i].first--;
		es[i].second--;
	}
	esss = es; // 保存全局变量
	return ugraph(n, es);
}

ugraph read_graph() {
	return read_graph_dimacs();
}

ugraph read_graph_dimacs(istream& is) {
	string line;
	getline(is, line);
	ui n, m; sscanf(line.c_str(), "p ds %u %u", &n, &m);
	vector<pii> es(m);
	all_point = n;
	for (ui i = 0; i < m; ++i) {
		getline(is, line);
		sscanf(line.c_str(), "%u %u", &es[i].first, &es[i].second);
		es[i].first--;
		es[i].second--;

	}
	esss = es; // 保存全局变量

	return ugraph(n, es);
}

ugraph read_graph(istream& is) {
	return read_graph_dimacs(is);
}


class IndexedMaxHeap {
private:
	struct Node {
		ui idx;      // 外部索引（0-based）
		double value; // 排序依据的值
		ui age;      // 当 value 相同时，age 小的更高优先级
	};

	std::vector<Node> heap;     // 堆数组 [0..size-1]
	std::vector<ui> idx2pos;    // idx → heap 位置，初始化为无效值（如 max_ui）
	ui size;                    // 当前堆大小
	ui capacity;                // 最大容量

	bool is_larger(const Node& a, const Node& b) const {
		if (a.value != b.value) return a.value > b.value;
		return a.age < b.age;  // value 相同时，age 小的优先
	}

	void swap_nodes(ui i, ui j) {
		std::swap(heap[i], heap[j]);
		idx2pos[heap[i].idx] = i;
		idx2pos[heap[j].idx] = j;
	}

	void up(ui u) {
		while (u > 0) {
			ui parent = (u - 1) / 2;
			if (!is_larger(heap[u], heap[parent])) break;
			swap_nodes(u, parent);
			u = parent;
		}
	}

	void down(ui u) {
		while (true) {
			ui left = 2 * u + 1;
			ui right = 2 * u + 2;
			ui largest = u;

			if (left < size && is_larger(heap[left], heap[largest]))
				largest = left;
			if (right < size && is_larger(heap[right], heap[largest]))
				largest = right;

			if (largest == u) break;
			swap_nodes(u, largest);
			u = largest;
		}
	}

public:
	IndexedMaxHeap(ui max_size)
		: heap(max_size),
		idx2pos(max_size, std::numeric_limits<ui>::max()),  // 初始化为无效值
		size(0),
		capacity(max_size) {
	}

	void push(ui idx, double value, ui age) {
		if (size >= capacity) throw std::out_of_range("Heap is full");
		if (idx >= capacity) throw std::invalid_argument("Invalid idx");
		if (idx2pos[idx] != std::numeric_limits<ui>::max())
			throw std::invalid_argument("Duplicate idx");

		heap[size] = { idx, value, age };
		idx2pos[idx] = size;
		up(size++);  // 插入后上调
	}

	std::pair<ui, double> top() const {
		if (empty()) throw std::out_of_range("Heap is empty");
		return { heap[0].idx, heap[0].value };
	}

	std::pair<ui, double> pop() {
		auto res = top();
		swap_nodes(0, --size);
		idx2pos[heap[size].idx] = std::numeric_limits<ui>::max();  // 标记为无效
		if (size > 0) down(0);  // 堆非空时下调
		return res;
	}

	void update(ui idx, double new_value, ui new_age) {
		if (idx >= capacity) throw std::invalid_argument("Invalid idx");
		if (idx2pos[idx] == std::numeric_limits<ui>::max()) {
			push(idx, new_value, new_age);
			return;
		}

		ui pos = idx2pos[idx];
		double old_value = heap[pos].value;
		ui old_age = heap[pos].age;

		heap[pos].value = new_value;
		heap[pos].age = new_age;  // 无论 new_age 是否为 0，都更新

		// 判断是否需要调整堆
		if ((new_value > old_value) || (new_value == old_value && new_age < old_age)) {
			up(pos);
		}
		else if ((new_value < old_value) || (new_value == old_value && new_age > old_age)) {
			down(pos);
		}
	}

	ui get_age(ui idx) const {
		if (idx >= capacity) throw std::invalid_argument("Invalid idx");
		ui pos = idx2pos[idx];
		if (pos == std::numeric_limits<ui>::max())
			throw std::invalid_argument("Index not found");
		return heap[pos].age;
	}

	bool empty() const { return size == 0; }
	ui get_size() const { return size; }
};

class WeightMaxHeap {
private:

	struct Node {
		ui idx;      // 外部索引（0-based）
		int value; // 排序依据的值
		int age;
	};
	std::vector<Node> heap;     // 堆数组 [0..size-1]
	std::vector<ui> idx2pos;    // idx → heap 位置，初始化为无效值（如 max_ui）
	ui size;                    // 当前堆大小
	ui capacity;                // 最大容量

	bool is_larger(const Node& a, const Node& b) const {
		if (a.value != b.value) return a.value > b.value;
		return a.age < b.age;  // age 小的优先级高
	}

	void swap_nodes(ui i, ui j) {
		std::swap(heap[i], heap[j]);
		idx2pos[heap[i].idx] = i;
		idx2pos[heap[j].idx] = j;
	}

	void up(ui u) {
		while (u > 0) {
			ui parent = (u - 1) / 2;
			if (!is_larger(heap[u], heap[parent])) break;
			swap_nodes(u, parent);
			u = parent;
		}
	}

	void down(ui u) {
		while (true) {
			ui left = 2 * u + 1;
			ui right = 2 * u + 2;
			ui largest = u;

			if (left < size && is_larger(heap[left], heap[largest]))
				largest = left;
			if (right < size && is_larger(heap[right], heap[largest]))
				largest = right;

			if (largest == u) break;
			swap_nodes(u, largest);
			u = largest;
		}
	}

public:

	WeightMaxHeap(ui max_size)
		: heap(max_size),
		idx2pos(max_size, std::numeric_limits<ui>::max()),  // 初始化为无效值
		size(0),
		capacity(max_size) {
	}

	void push(ui idx, int value, int age) {
		if (idx >= capacity) throw std::invalid_argument("Invalid idx");
		if (idx2pos[idx] != std::numeric_limits<ui>::max())
			throw std::invalid_argument("Duplicate idx");
		if (size >= capacity) throw std::out_of_range("Heap is full");

		heap[size] = { idx, value, age };
		idx2pos[idx] = size;
		up(size++);
	}

	std::pair<ui, int> top() const {
		if (empty()) throw std::out_of_range("Heap is empty");
		return { heap[0].idx, heap[0].value };
	}

	std::pair<ui, int> pop() {
		auto res = top();
		swap_nodes(0, --size);
		idx2pos[heap[size].idx] = std::numeric_limits<ui>::max();  // 标记为无效
		if (size > 0) down(0);  // 堆非空时下调
		return res;
	}

	void update(ui idx, int new_value, int new_age) {
		if (idx >= capacity) throw std::invalid_argument("Invalid idx");

		ui pos = idx2pos[idx];
		if (pos == std::numeric_limits<ui>::max()) {
			push(idx, new_value, new_age);
			return;
		}

		Node& node = heap[pos];
		int old_value = node.value;
		int old_age = node.age;

		node.value = new_value;
		node.age = new_age;

		// 判断调整方向
		bool should_up = (new_value > old_value) ||
			(new_value == old_value && new_age < old_age);

		if (should_up) {
			up(pos);
		}
		else {
			down(pos);
		}
	}

	// 根据索引删除元素
	void remove_by_idx(ui idx) {
		if (idx >= capacity || idx2pos[idx] == std::numeric_limits<ui>::max())
			throw std::invalid_argument("Invalid idx");

		ui pos = idx2pos[idx];

		// 删除最后一个元素的特殊情况
		if (pos == size - 1) {
			idx2pos[idx] = std::numeric_limits<ui>::max();
			--size;
			return;
		}

		// 常规删除流程
		swap_nodes(pos, size - 1);  // 与末尾交换
		idx2pos[idx] = std::numeric_limits<ui>::max();  // 先标记原始节点无效
		--size;

		// 对交换到pos的新节点进行调整
		Node& moved_node = heap[pos];
		if (pos > 0 && is_larger(moved_node, heap[(pos - 1) / 2])) {
			up(pos);
		}
		else {
			down(pos);
		}
	}

	bool empty() const { return size == 0; }
	ui get_size() const { return size; }
};

// 顶点及其非支配度
struct Vertex {
	ui id;
	double non_dominated_degree;
	bool operator<(const Vertex& other) const {
		return non_dominated_degree < other.non_dominated_degree; // 大顶堆
	}
};

class CFeature_Info {

private:
	std::random_device rd;  // 硬件熵源
	std::minstd_rand gen;       // 更高质量的引擎（替代 minstd_rand）
	std::uniform_int_distribution<ui> dist{ 0, 0 };  // 初始范围占位
	std::uniform_real_distribution<double> urd{ 0.0, 1.0 };

public:
	ui n;
	ui cover_num;
	//vector<ui> IFromOne;
	// c_d[u]: How many vertices in N[u] are selected into the solution.
   // c_d[u] > 0 ==> u is dominated.
	vector<ui> c_d;

	// c_nd[u]: How many vertices in N[u] are dominated
	// Select u int solution will dominate |N[u]|-c_nd[u] more vertices.
	vector<ui> c_nd;

	// c_x[u]: How many vertices in N[u] are excluded by the solution.
	vector<ui> c_x;

	ui cnt_s;   //  Size of the current solution, |D|
	ui cnt_d;   //  Number of the dominated vertices, |N[D]| = point_num 就是全支配了
	ui cnt_x;   //  Number of the excluded vertices, |X|

	vector<char> D, X, I;      // 排除集、忽略集

	vector<vector<ui>> h;

	ugraph graph;   // 输入图 点：邻居x x x
	ugraph new_graph;   // 输入图 点：邻居x x x
	vector<robin_hood::unordered_set<ui>> is_dominated; // 被支配点 点：被x x x支配
	vector<ui> dominate_num; // 点u被支配的点数
	vector<ui> only_dominate; // 点u覆盖的点数
	vector<ui> unselected; // 候选集合
	vector<ui> selected_no_must; // 非必选的支配点
	// 黑白约简
	vector<bool> is_fix;
	vector<ui> tabu;
	// 原来MDSP
	vector<ui> dominate_age; // 支配点的年龄
	vector<ui> point_to_idx; //[u]=idx
	int area_idx;
	// parameters
	const int BMS_sample_size = 74;
	const double add_prob = 0.6;
	vector<int> area_check_num;
	vector<int> area_D_num;
	WeightMaxHeap add_heap1;
	WeightMaxHeap remove_heap1;
	vector<ui> BMS_candidates;
	vector<double> inv_degree_max;
	vector<ui> point_to_area;
	vector<vector<ui>> res_area;
	vector<vector<ui>> D_by_area; // 每个区域的D点集合
	vector<robin_hood::unordered_set<ui>> nei_2; // 2跳邻居
	//flat_hash_map<ui, vector<ui>> x_by_dominate; // [i]必须被哪些点中的一个支配
	//flat_hash_map<ui, vector<ui>> can_dominate_x; // [i]可以支配哪些必不选点x
	//flat_hash_map<ui, ui> dominate_x_num; // [i]被几个支配
	vector<char> important_point; // 是否是重要点
	void do_add(ui v, ui iter);
	void do_remove(ui v, ui iter);
	bool can_cut;
	/// <summary>
	/// 小规模算例数据结构
	/// </summary>
	robin_hood::unordered_set<ui> no_dominate; // 无支配点
	vector<ui> delta;
	vector<ui> weight;
	//vector<ui> small_tabuList;
	int f, best_f, best_delta_f, close_f, open_f; //f函数，记录加权和
	int tabu_open, tabu_close;//禁忌期为1，记录禁忌元素
	vector<ui> best_open, best_close;
	vector<ui> move_check;
	vector<ui> org_delta;
	//unordered_map<ui, flat_hash_set<ui>> n2_map; // 记录2跳邻居


	CFeature_Info(const ugraph& _g) :
		gen(std::random_device{}() ^
			std::chrono::high_resolution_clock::now().time_since_epoch().count()),
		n(_g.off.size() - 1),
		cover_num(0),
		is_dominated(n), dominate_num(n, 0), only_dominate(n, 0),
		//domination_count(n),
		graph(_g),
		h(n),
		can_cut(false),
		important_point(n, 0),
		org_delta(n, 0),
		D(n, 0), X(n, 0), I(n, 0),
		c_d(n, 0), c_nd(n, 0), c_x(n, 0),
		cnt_s(0), cnt_d(0), cnt_x(0),
		tabu(n, 0), inv_degree_max(n + 1, 0.0), dominate_age(),
		add_heap1(0), remove_heap1(0),
		best_delta_f(INT_MAX), tabu_open(-1), tabu_close(-1)  // 初始化
	{
		//cout << n << endl;
		for (ui u = 0; u < n; ++u) {
			h[u].assign(graph[u].begin(), graph[u].end());
			sort(h[u].begin(), h[u].end(), [this](ui v1, ui v2) { return this->graph[v1].size() < this->graph[v2].size(); });
			if (u != 0) inv_degree_max[u] = 1.0 / u;
			//is_dominated[u].reserve(graph[u].size()/3);
		}
		inv_degree_max[n] = 1.0 / n;
		//cout << n << endl;
	}

	void new_reduce_2();
	void init_reduction();
	bool reduce_single_dominator(ui u);
	bool reduce_ignore(ui u);
	bool reduce_subset(ui u);
	bool check_subset(ui u);

	bool selected(ui u) const { return D[u]; }

	bool dominated(ui u) const { return c_d[u] > 0; }

	bool excluded(ui u) const { return X[u]; }

	bool undetermined(ui u) const { return !X[u] && !D[u]; }

	bool ignored(ui u) const { return I[u]; }

	ui selected() const { return cnt_s; }

	ui selected(const vector<ui>& V) const {
		return count_if(V.begin(), V.end(), [this](ui v) { return selected(v); });
	}

	ui dominated() const { return cnt_d; }

	ui dominated(const vector<ui>& V) const {
		return count_if(V.begin(), V.end(), [this](ui v) { return dominated(v); });
	}

	ui excluded() const { return cnt_x; }

	ui undetermined() const { return n - cnt_s - cnt_x; }

	ui coverage_size(ui u) const {
		return graph[u].size() - c_nd[u];
	}

	vector<ui> coverage(ui u) const {
		vector<ui> w;
		for (ui v : graph.adj(u))
			if (!dominated(v))
				w.emplace_back(v);
		return w;
	}

	ui frequency(ui u) const {
		return graph.adj(u).size() - c_x[u];
	}

	vector<ui> dominators(ui u) const {
		vector<ui> w;
		for (ui v : graph[u])
			if (!excluded(v))
				w.emplace_back(v);
		return w;
	}

	//  Basic operations
	void mark_dominated(ui u) {
		if (!c_d[u]++) {
			cnt_d++;
			for (ui w : graph[u])
				c_nd[w]++;
		}
	}

	void mark_undominated(ui u) {
		if (!--c_d[u]) {
			cnt_d--;
			for (ui w : graph[u])
				c_nd[w]--;
		}
	}

	void select(ui u) {
		D[u] = 1;
		cnt_s++;
		for (ui v : graph[u])
			mark_dominated(v);
	}

	void unselect(ui u) {
		D[u] = 0;
		cnt_s--;
		for (ui v : graph[u])
			mark_undominated(v);
	}

	void exclude(ui u) {
		X[u] = 1;
		cnt_x++;
		for (ui v : graph[u]) {
			c_x[v]++;
			if (!dominated(v) && frequency(v) == 1) {
				for (ui w : graph[v])
					if (!excluded(w)) {
						select(w);
						break;
					}
			}
		}
	}

	void unexclude(ui u) {
		X[u] = 0;
		cnt_x--;
		for (ui v : graph[u])
			c_x[v]--;
	}

	void ignore(ui u) {
		I[u] = 1;
		mark_dominated(u);
	}

	void unignore(ui u) {
		I[u] = 0;
		mark_undominated(u);
	}

	bool contains(const vector<ui>& S, const vector<ui>& T);
	// 原来 MDSP

	void check_redundancy(ui age);
	void check_redundancy_2();
	void check_redundancy_3(ui age);
	ui random_select(const std::vector<ui>& s);

	void local_improvement_2();
	void local_improvement_3();

	void InitialDelta();
	void SwapMove(int v_open, int v_close);
	void findBestSwap(int& v_open, int& v_close);
	void Open(ui v);
	void Close(ui v);
	void update_affected_2(ui v);
	void init_delta_config();

};

class UnionFind {
	vector<ui> parent, rank;
public:
	UnionFind(ui n) : parent(n), rank(n, 0) {
		for (ui i = 0; i < n; ++i) parent[i] = i;
	}

	ui find(ui x) {
		if (parent[x] != x) parent[x] = find(parent[x]); // 路径压缩
		return parent[x];
	}

	void unite(ui x, ui y) {
		ui px = find(x), py = find(y);
		if (px == py) return;
		if (rank[px] < rank[py]) swap(px, py);
		parent[py] = px;
		if (rank[px] == rank[py]) rank[px]++;
	}
};

bool CFeature_Info::contains(const vector<ui>& S, const vector<ui>& T) {
	if (S.size() == T.size())
		return S == T;
	else if (T.size() * log(S.size()) < S.size() + T.size()) {
		for (ui u : T)
			if (!binary_search(S.begin(), S.end(), u))
				return false;
		return true;
	}
	else
		return includes(S.begin(), S.end(), T.begin(), T.end());
}

//  Reduce when u has only one dominator.
bool CFeature_Info::reduce_single_dominator(ui u) {
	if (frequency(u) != 1)
		return false;
	for (ui v : graph[u]) {
		if (!undetermined(v))
			continue;
		select(v);
		break;
	}
	return true;
}

//  Reduce when there exists an undominated vertex v such that v is dominated implies u is dominated.
bool CFeature_Info::reduce_ignore(ui u) {
	bool reduced = false;
	ui w = ~0;  //  Let w be a dominator of u that its coverage is minimized.
	for (ui v : graph[u])
		if (!excluded(v) && (!~w || coverage_size(v) < coverage_size(w)))
			w = v;

	static vector<ui> vz;
	vz.clear();

	for (ui z : h[u])
		if (z != w && !excluded(z))
			vz.emplace_back(z);

	for (ui v : graph[w]) {
		if (v == u || dominated(v) || frequency(v) < frequency(u))
			continue;
		//  v isn't dominated. check whether v is dominated implies u is dominated
		bool fail = false;
		for (ui z : vz)   //  z is a set that contains u. check whether z contains v.
			if (v != z && !graph[z].contains(v)) {
				fail = true;
				break;
			}

		if (!fail) {
			ignore(v);
			reduced = true;
		}
	}
	return reduced;
}

bool CFeature_Info::check_subset(ui u) {
	if (coverage_size(u) == 0)
		return true;

	//  Find the vertex in N[u]-N[S] with minimum frequency
	ui w = ~0;
	for (ui v : graph[u])
		if (!dominated(v) && (!~w || frequency(v) < frequency(w)))
			w = v;

	//  Every vertex in vz=N[u]-N[S] should be adjacent to v
	static vector<ui> vz;
	vz.clear();
	for (ui z : h[u])
		if (z != w && !dominated(z))
			vz.emplace_back(z);

	for (ui v : graph[w]) {
		if (v == u || !undetermined(v))
			continue;
		//  Check whether u's coverage is a subset of v's coverage.
		//  i.e., every vertex in N[u]-N[S] is incident to v.
		bool fail = false;
		for (ui z : vz)
			if (v != z && !graph[v].contains(z)) {
				fail = true;
				break;
			}
		if (!fail)
			return true;
	}
	return false;
}

bool CFeature_Info::reduce_subset(ui u) {
	if (check_subset(u)) {
		exclude(u);
		return true;
	}
	return false;
}

//  Apply the rules exhaustively.
void CFeature_Info::new_reduce_2() {
	using namespace std::chrono; // 简化时间单位写法
	auto start_time = steady_clock::now(); // 开始时间点
	auto timeout_duration = seconds(10); // 超时时长
	int iter = 0;
	bool reduced;
	do {
		reduced = false;
		for (ui u = 0; u < n; ++u) {
			auto elapsed = steady_clock::now() - start_time;
			if (elapsed >= timeout_duration && iter > 0) {
				reduced = false;
				//std::cout << "超时退出！" << std::endl;
				break;
			}
			if (undetermined(u)) {
				if (graph[u].size() == 3) {
					ui v1 = *(graph[u].begin() + 1);
					ui v2 = *(graph[u].begin() + 2);
					if (X[v1] && X[v2]) {
						select(u);
						continue;
					}
					else if (graph[v1].contains(v2) || graph[v2].contains(v1)) {
						exclude(u);
						reduced = true;
						continue;
					}
				}
			}
			if (undetermined(u)) {
				reduced |= reduce_subset(u);
			}
			if (!dominated(u)) {
				reduced |= reduce_single_dominator(u);
			}

			if (!dominated(u)) {
				reduced |= reduce_ignore(u);
			}
		}
		iter++;
	} while (reduced);
}

// 计算连通分量并记录每个分量的节点
vector<vector<ui>> countConnectedComponentsWithNodes(int n, const vector<pii>& rvalid_es, const vector<robin_hood::unordered_set<ui>> is_domin) {
	// Step 1: 初始化并查集
	UnionFind uf(n);

	// Step 2: 处理有效边，合并连通分量
	for (const auto& e : rvalid_es) {
		if (e.first < 0 || e.first >= n || e.second < 0 || e.second >= n) {
			continue; // 输入验证
		}
		uf.unite(e.first, e.second);
	}

	// Step 3: 收集连通分量中的节点
	robin_hood::unordered_map<ui, vector<ui>> components;
	robin_hood::unordered_set<ui> active_nodes;

	// 标记所有出现在 rvalid_es 中的节点
	for (const auto& e : rvalid_es) {
		active_nodes.insert(e.first);
		active_nodes.insert(e.second);
	}

	// 将活跃节点分组到连通分量
	for (ui i : active_nodes) {
		int root = uf.find(i);
		components[root].push_back(i);
	}

	//// 如果有孤立节点（未出现在 rvalid_es 中），单独成连通分量
	//for (int i = 0; i < n; ++i) {
	//	if (!active_nodes.count(i)) {
	//		int root = uf.find(i);
	//		components[root].push_back(i);
	//	}
	//}

	// Step 4: 转换为输出格式
	vector<vector<ui>> result;
	for (auto& p : components) {
		if (p.second.empty()) {
			continue;
		}
		// 检查连通分量是否全被支配
		bool all_dominated = true;
		for (ui node : p.second) {
			if (is_domin[node].size() == 0) {
				all_dominated = false;
				break;
			}
		}
		// 只有非全被支配的连通分量才加入结果
		if (!all_dominated) {
			result.push_back(move(p.second));
		}
	}

	// 按连通分量大小升序排序
	sort(result.begin(), result.end(),
		[](const vector<ui>& a, const vector<ui>& b) {
			return a.size() < b.size(); // 点数少的排前面
		});
	return result;
}

// 初始化约简
void CFeature_Info::init_reduction() {
	new_reduce_2(); // 双重约简
	//cout << "约简规则完成 " << endl;
	is_fix = vector<bool>(n, false);
	vector<ui> positions(n, 0);
	ui index = 0;
	for (ui v = 0; v < n; v++) {
		if (undetermined(v)) {
			unselected.emplace_back(v);
			positions[v] = index++;
		}
		else {
			is_fix[v] = true; // 选定的点
			if (D[v]) { // 邻居支配
				for (ui u : graph[v]) {
					is_dominated[u].insert(v);
					dominate_num[u]++;
					if (dominate_num[u] == 1) only_dominate[u] = v;
				}
			}
		}
	}

	robin_hood::unordered_set<ui> del_node;
	for (ui i = 0; i < n; i++) {
		if (D[i]) {
			del_node.insert(i);
		}
		else if (X[i]) {

			if (dominate_num[i] > 0) {
				del_node.insert(i);
			}
			else {
				for (int nei : graph[i]) {
					if (!X[nei]) {
						important_point[nei] = 1;
					}
					/*if (v != i) {
						x_by_dominate[i].insert(v);
						can_dominate_x[v].push_back(i);
					}*/
				}
			}

		}
	}

	auto filter_edges = [](const vector<pii>& edges, const robin_hood::unordered_set<ui>& del) {
		vector<pii> res;
		for (const auto& e : edges) {
			if (!del.count(e.first) && !del.count(e.second)) {
				res.push_back(e);
			}
		}
		return res;
		};

	auto valid_es = filter_edges(esss, del_node);
	graph = ugraph(n, valid_es);

	//res_area = countConnectedComponentsWithNodes(n, valid_es, is_dominated);
	area_check_num = vector<int>(n, 0);
	area_D_num = vector<int>(n, 0);
	point_to_area = vector<ui>(n); // 初始化为无效值
	//D_by_area = vector<vector<ui>>(res_area.size());
	//cout << "####" << endl;
	

	// ==================== 非支配度 ====================
	// 优先队列（大顶堆）按非支配度排序
	//cout << "贪心插入过程" << endl;
	priority_queue<Vertex> max_heap;
	vector<double> latest_score(n, 0.0);
	// 初始化优先队列
	for (ui x = 0; x < n; x++) {
		if (is_fix[x]) continue;
		for (ui nei : graph[x]) { // x的邻居
			if (dominated(nei)) continue; // 算 x 只管未被支配的邻居
			latest_score[x] += inv_degree_max[graph[nei].size()];
		}
		max_heap.push({ x, latest_score[x] });
	}
	//int iter = 0;
	while (!max_heap.empty() && cnt_d < n) {
		//iter++;
		Vertex current = max_heap.top();
		max_heap.pop();
		ui v = current.id;  // 当前顶点
		// 检查顶点是否有效（必须：未选中、可调整、优先级是最新的）
		if (D[v] || X[v] || current.non_dominated_degree != latest_score[v]) {
			continue;  // 跳过无效顶点
		}
		//cout << iter << "  ";
		//cout << "贪心选中" << v << "  " << latest_score[v] << "  " << iter << endl;
		// 选中当前顶点 v
		//latest_score[v] = 0;  // 标记为已选中（防止重复处理）
		selected_no_must.emplace_back(v);
		ui pos = positions[v];                   // unselected[pos] == v
		//std::swap(unselected[pos], unselected.back());
		unselected[pos] = unselected.back();
		positions[unselected[pos]] = pos;         // 更新原最后一位的位置
		unselected.pop_back();
		//unselected.erase(remove(unselected.begin(), unselected.end(), v), unselected.end());

		for (ui u : graph[v]) {
			is_dominated[u].insert(v); // v支配u
			dominate_num[u]++;
			if (dominate_num[u] == 1) only_dominate[u] = v;
			if (dominated(u)) continue; // 如果u之前是被支配的，那么不需要处理自身，u的邻居也不需要管
			for (ui w : graph[u]) {
				if (!undetermined(w)) continue; // w是u的邻居，不能是v
				latest_score[w] -= inv_degree_max[graph[u].size()]; // 来自u的影响
				if (latest_score[w] >= 0) max_heap.push({ w, latest_score[w] });
			}
		}
		select(v);  // 此操作会影响所有支配关系及 coverage_size

	}

	num = cnt_s;
	global_data = D;
	//cout << num << "贪结束" << cnt_d << endl;
	for (int i = 0; i < res_area.size(); i++) { // 第i个连通分量
		for (ui v : res_area[i]) {
			point_to_area[v] = i; // v属于第i个连通分量
			if (D[v]) {
				//D_by_area[i].push_back(v);
				area_D_num[i]++;
			}
		}
	}
	unselected.erase(
		remove_if(
			unselected.begin(),
			unselected.end(),
			[&](ui v) { return is_fix[v]; }),
		unselected.end()
	);
	/*if (cnt_d == n) {
		cout << "支配完成" << endl;
	}
	else {
		cout << "支配失败" << endl;
	}*/

}

void CFeature_Info::check_redundancy_2() {

	// 使用迭代器以便在遍历中安全删除
	auto it = selected_no_must.begin();
	while (it != selected_no_must.end()) {
		ui v = *it;
		if (delta[v] == 0) {
			Close(v); // 删除v
			it = selected_no_must.begin();
		}
		else {
			++it;
		}
	}

}

void CFeature_Info::update_affected_2(ui v) {

	for (ui x : nei_2[v]) {
		if (is_fix[x]) continue; // 跳过已被支配的点
		if (D[x]) {
			remove_heap1.update(x, -1 * delta[x], dominate_age[x]);
		}
		else { // 当前点改变了状态，不在支配集中
			add_heap1.update(x, delta[x], dominate_age[x]);
		}
	}
}

ui CFeature_Info::random_select(const std::vector<ui>& s) {
	dist.param(std::uniform_int_distribution<ui>::param_type(0, s.size() - 1));
	return s[dist(gen)];  // vector 直接通过下标访问，无需 std::advance
}

// Iterated Greedy 算法
void iterated_greedy(ugraph& graph) {
	// 预处理图信息
	// 初始解
	//cout << "开始约简" << endl;
	CFeature_Info CI(graph);
	//cout << "##" << endl;
	CI.init_reduction();

	//cout << "约简完毕,初始解生成" << CI.selected_no_must.size() << " " << CI.unselected.size() << endl;
	CI.point_to_idx.resize(CI.n);
	for (ui i = 0; i < CI.selected_no_must.size(); i++) {
		CI.point_to_idx[CI.selected_no_must[i]] = i;
	}
	for (ui i = 0; i < CI.unselected.size(); i++) {
		CI.point_to_idx[CI.unselected[i]] = i;
	}


	if (CI.cnt_s > 5000) {
		// ====== 初始化分数并更新 ======
		/*CI.score.resize(CI.n, 0);
		for (ui v = 0; v < CI.n; v++) {
			CI.update_score(v);
		}*/
		// ===== 分数初始化完毕 ======
		// ===== 初始化年龄 ======
		CI.dominate_age.resize(CI.n, 0);
		//CI.local_improvement_1();
		CI.local_improvement_3();
	}
	else {
		CI.local_improvement_2(); // 更强力的局部搜索
	}


}

// 小规模算例优化
void CFeature_Info::InitialDelta() {

	for (ui i : selected_no_must) {

		//如果是非中心节点，delta为覆盖未覆盖元素数量
		//如果是中心，delta为仅由该中心覆盖元素数量
		delta[i] = 0;
		for (ui v : graph.adj(i)) {
			if (dominate_num[v] == 1) { // 只被 i 支配
				//delta[i] += weight[v];
				delta[i]++;
			}
		}
	}
}

void CFeature_Info::SwapMove(int v_open, int v_close) {

	Open(v_open);
	Close(v_close);

	f += best_delta_f;

	if (f < best_f) best_f = f;
	tabu_close = tabu_open; // 简化，只记录一个
	tabu_open = v_open;
}

void CFeature_Info::Open(ui v) {
	//if (D[v]) cout << "出问题,已成为支配点" << endl;
	open_f = 0;
	select(v);
	for (ui vc : graph.adj(v)) { // 支配点 v 的邻居 vc
		if (dominate_num[vc] == 1) { // 邻居中原来只被一个点支配
			delta[only_dominate[vc]] -= weight[vc];
		}
		else if (dominate_num[vc] == 0) { // 邻居中原来不被支配
			for (ui u : graph.adj(vc)) { // 那么 vc 的邻居 u 都不存在支配点
				//if (is_fix[u]) continue; 
				delta[u] -= weight[vc]; // 所以选中 v 可支配 vc, 那么 u 要 -vc 的 weight
			}
			open_f += weight[vc];
			delta[v] += weight[vc]; // v 现在是唯一支配 vc 还需要 +vc 的 w 权重
			no_dominate.erase(vc); // 如果邻居没有被支配，加入未支配集合
			cover_num--;
			only_dominate[vc] = v; // 现在 v 是唯一支配点
		}
		is_dominated[vc].insert(v);
		dominate_num[vc]++;
	}
	// 1️⃣ 将 best_v1 加入 selected_no_must
	selected_no_must.emplace_back(v);
	// 2️⃣ 记录 best_v1 在 unselected 的原索引（必须先获取旧值）
	ui old_candidate_idx = point_to_idx[v];
	// 3️⃣ 交换 unselected 中的 best_v1 和末尾元素
	//std::swap(unselected[old_candidate_idx], unselected.back());
	unselected[old_candidate_idx] = unselected.back();
	// 4️⃣ 更新 point_to_idx: 交换后的 unselected.back() 现在在 old_candidate_idx
	point_to_idx[unselected[old_candidate_idx]] = old_candidate_idx;
	// 5️⃣ 更新 point_to_idx: best_v1 现在在 selected_no_must 末尾
	point_to_idx[v] = selected_no_must.size() - 1;
	// 6️⃣ 删除 unselected 的末尾（旧的 best_v1）
	unselected.pop_back();

}

void CFeature_Info::Close(ui v)
{
	close_f = 0;
	//if (!D[v] || X[v]) cout << "出问题，已不再支配中" << endl;
	unselect(v);
	//delta[v] = 0; // 关闭点v，delta[v]归零
	//更新邻域delta
	for (ui vc : graph.adj(v)) // 关闭支配点的邻居vc
	{
		if (dominate_num[vc] == 1)// vc只被当前点支配
		{
			for (ui jc : graph.adj(vc)) {
				//if (is_fix[jc]) continue;
				delta[jc] += weight[vc];
			}
			close_f += weight[vc]; // 关闭点v，delta[v]归零
			no_dominate.insert(vc); // 如果邻居没有被支配，加入未支配集合
			delta[v] -= weight[vc]; // 之前是只支配vc 加上vc的传播权重，现在是选中可支配vc，加上vc的传播权重 故不变
			cover_num++;
		}
		else if (dominate_num[vc] == 2)// close v 后支配 vc 的点压力变大
		{
			ui domi_1 = *is_dominated[vc].begin(); // 唯一支配点
			ui domi_2 = *next(is_dominated[vc].begin()); // 第二个支配点
			if (domi_1 == v) {
				delta[domi_2] += weight[vc]; // 第二个支配点的压力变大
			}
			else if (domi_2 == v) {
				delta[domi_1] += weight[vc]; // 唯一支配点的压力变大
			}
			only_dominate[vc] = (domi_1 == v) ? domi_2 : domi_1; // 更新唯一支配点
		}
		dominate_num[vc]--;
		is_dominated[vc].erase(v); // 更新邻居的支配点
	}
	// 1️⃣ 将 best_v1 加入 selected_no_must
	unselected.emplace_back(v);
	// 2️⃣ 记录 best_v1 在 unselected 的原索引（必须先获取旧值）
	ui old_candidate_idx = point_to_idx[v];
	// 3️⃣ 交换 unselected 中的 best_v1 和末尾元素
	//std::swap(selected_no_must[old_candidate_idx], selected_no_must.back());
	selected_no_must[old_candidate_idx] = selected_no_must.back();
	// 4️⃣ 更新 point_to_idx: 交换后的 unselected.back() 现在在 old_candidate_idx
	point_to_idx[selected_no_must[old_candidate_idx]] = old_candidate_idx;
	// 5️⃣ 更新 point_to_idx: best_v1 现在在 selected_no_must 末尾
	point_to_idx[v] = unselected.size() - 1;
	// 6️⃣ 删除 unselected 的末尾（旧的 best_v1）
	selected_no_must.pop_back();
}

void CFeature_Info::findBestSwap(int& v_open, int& v_close) {
	best_delta_f = INT_MAX;
	best_open.clear();
	best_close.clear();

	static vector<ui> vector_no_dominate; // 备份未支配点集合
	vector_no_dominate = vector<ui>(no_dominate.begin(), no_dominate.end());
	//cout << "no+_" << no_dominate.size() << endl;
	/*if (temp_unselected.size() != vector_no_dominate.size()) {
		cout << "出问题，temp_unselected.size() != vector_no_dominate.size() " << temp_unselected.size() << " " << vector_no_dominate.size() << endl;
		system("pause");
	}*/
	ui v_f = random_select(vector_no_dominate); // 选点应该在v周围，能够支配v

	// 对所有的邻居
	for (ui nei : graph.adj(v_f)) {
		if (is_fix[nei]) continue;
		// 尝试打开nei 这样nei周围的delta会变化 公共支配不做处理


		for (ui u : graph.adj(nei)) { // open a center virtually
			if (dominate_num[u] == 1) { // 支配点中共同可支配的单支配->不被单支配
				ui center = *is_dominated[u].begin();
				if (org_delta[center] == 0) {
					move_check.push_back(center);
					org_delta[center] = delta[center]; // 记录原来的delta
				}

				delta[center] -= weight[u]; // 打开nei会增加u的支配
			}
		}
		//vector<ui> BMS_unselected;
		//const auto total = selected_no_must.size();
		//const auto sample_size = BMS_sample_size;
		//const double prob = static_cast<double>(sample_size) / total;
		//std::geometric_distribution<ui> geo_dist(prob);
		//for (ui i = 0; i < total && BMS_unselected.size() < sample_size; ) {
		//	ui skip = geo_dist(gen);  // 直接计算下一个采样点的距离
		//	i += skip + 1;             // +1 保证不重复
		//	if (i < total) {          // 防止越界
		//		BMS_unselected.emplace_back(selected_no_must[i]);  // 转为 1-based
		//	}
		//}

		// 关闭 u
		for (ui u : selected_no_must) {
			//for (ui u : n2_map[nei]) {
			// 判断点对禁忌
			int cur_delta_f = delta[u] - delta[nei];// 删除u会增加的vw和 加入nei会降低的vw和 计算delta差 负数
			if (u != tabu_open && u != tabu_close || f - cur_delta_f < best_f) {
				if (cur_delta_f < best_delta_f) {
					best_delta_f = cur_delta_f;
					best_open = { nei };
					best_close = { u };
				}
				else if (cur_delta_f == best_delta_f) {
					best_open.emplace_back(nei);
					best_close.emplace_back(u);
				}
			}



		}

		for (auto& p : move_check) {
			delta[p] = org_delta[p]; // 恢复原来的 delta
			org_delta[p] = 0;
			move_check.clear();
		}
	}


	if (best_open.empty()) {
		v_open = v_close = -1; // 没有找到合适的交换
		//tabu_open = tabu_close = -1;
		tabu_close = tabu_open;
		tabu_open = -1;
		//system("pause");
	}
	else {
		//static std::minstd_rand gen(std::random_device{}());
		//std::uniform_int_distribution<ui> dist(0, best_open.size() - 1);
		dist.param(std::uniform_int_distribution<ui>::param_type(0, best_open.size() - 1));
		int choose = dist(gen);
		//cout << "best_open " << best_open.size() << " choose " << best_open[choose] << ", " << best_close[choose] << endl;
		v_open = best_open[choose];
		v_close = best_close[choose];
	}

}

void CFeature_Info::local_improvement_2() {
	//cout << "开始局部搜索" << endl;
	delta = vector<ui>(n, 0);
	weight = vector<ui>(n, 1);

	int v_open, v_close;
	InitialDelta();
	check_redundancy_2();

	ui v_del = random_select(selected_no_must);
	Close(v_del);
	best_f = f = close_f;
	int out_nonimpr = 0; // 非改善次数
	int iter = 0; // 设置最大迭代次数
	//constexpr double TARGET_TIME = 1.0; // 1秒
	//auto start = high_resolution_clock::now();
	//auto elapsed = duration_cast<duration<double>>(
		//high_resolution_clock::now() - start).count();
	while (true) {
		/*for (int i = 0; i < n; i++) {
			if (is_dominated[i].size() != dominate_num[i]) {
				cout << i << " " << is_dominated[i].size() << " " << dominate_num[i] << "对不上" << endl;
				system("pause");
			}
		}*/
		iter++;
		out_nonimpr++;
		//auto elapsed = duration_cast<duration<double>>(
			//high_resolution_clock::now() - start).count();
		//if (elapsed >= TARGET_TIME) {
			//cout << "Age: " << iter << ", Elapsed time: " << elapsed << " seconds" << "|不被支配" << no_dominate.size() << "|支配点数" << cnt_s << endl;
			//start = high_resolution_clock::now();
		//}


		findBestSwap(v_open, v_close);
		//cout << "Best swap: " << v_open << " " << v_close << endl;
		//cout << "Best f size: " << f << endl;
		if (v_open == -1 || v_close == -1) {
			continue;
		}
		//cout << "best_delta_f: " << best_delta_f << endl;
		SwapMove(v_open, v_close);



		//cout << "Best solution size: " << cnt_s << "  snt_D" << cnt_d <<  endl;
		//if (f == 0) system("pause");
		if (cover_num == 0) {
			if (cnt_s < num) {
				check_redundancy_2();
				num = cnt_s;
				global_data = D;
				out_nonimpr = 0;
				//auto max_it = std::max_element(std::begin(weight), std::end(weight), [](int a, int b) {
					//return a < b; // 返回 true 表示 a 应该排在 b 前面
					//});
				//cout << "Best solution size: " << cnt_s << "|snt_D:" << cnt_d << "|iteration：" << iter << "| max_weight" << *max_it << endl;
				// 完成支配再删一个点

			}
			int v_f = -1;
			for (int u : selected_no_must) {
				bool flag = true;
				for (int nei : graph[u]) {
					if (!X[nei] && dominate_num[nei] == 1) {
						flag = false;
						break;
					}
				}
				if (flag) {
					v_f = u;
					break;
				}
			}
			if (v_f == -1) v_f = random_select(selected_no_must); // 如果没有找到合适的点，就随机选择一个未支配点
			//ui v_f = *std::min_element(selected_no_must.begin(), selected_no_must.end(),
				//[this](ui a, ui b) {
					//return weight[a] < weight[b];  // 修改为找最小值
				//});
			Close(v_f);
			best_f = f = close_f;
		}
		else {
			//cout << "no+d " << no_dominate.size() << "  ";
			for (ui v_1 : no_dominate) {
				//if (X[v_1]) cout << "$$$$$$$$$$$$$$$$$$$$$" << endl;
				weight[v_1] += 1; // 增量权重
				f += 1;
				// 当前点未支配，邻居中不存在支配点故都需要加一
				for (ui ic : graph.adj(v_1)) {
					delta[ic] += 1;
				}
			}
		}

		//if (out_nonimpr > 4000) {
		//	cout << "####" << endl;
		//	// 1. 随机选择要挖洞的支配点
		//	//vector<ui> del_node;
		//	//vector<ui> add_node;
		//	// 2. 随机决定挖洞的层级（1~5 层）
		//	/**/std::uniform_int_distribution<ui> dist(4, 7);
		//	int max_level = dist(gen);
		//	int del_num = 0;

		//	for (int i = 0; i < max_level; i++) {
		//		int v = random_select(selected_no_must);
		//		if (important_point[v]) {
		//			for (int x : graph[v]) { // 必不选邻居点
		//				if (X[x]) {
		//					for (int nei : graph[x]) {
		//						if (is_fix[nei] || !D[nei]) continue; // 忽略固定点
		//						Close(nei);
		//						//del_node.push_back(nei);
		//						del_num++;
		//					}
		//				}
		//			}
		//		}
		//		else {
		//			if (is_fix[v] || !D[v]) continue; // 忽略固定点
		//			Close(v);
		//			//del_node.push_back(v);
		//			del_num++;
		//		}

		//	}
		//	cout << "$$$$" << del_num << endl;


		//	// 4. 重新贪心选择新支配点（补回被删除的点）
		//	while (del_num-- > 0) {
		//		int best_v = -1; // 实现你的选择逻辑
		//		int w = INT_MAX;
		//		for (int u : no_dominate) {
		//			for (int nei : graph[u]) {
		//				if (is_fix[nei]) continue;
		//				if (weight[nei] < w) { // 找到一个更好的点
		//					w = delta[nei];
		//					best_v = nei;
		//				}
		//			}
		//		}
		//		Open(best_v);
		//		//add_node.push_back(best_v);
		//	}
		//	cout << "@####" << endl;
		//	//sort(del_node.begin(), del_node.end());	
		//	//sort(add_node.begin(), add_node.end());
		//	//cout << "删除点:";
		//	//for (int u : del_node) {
		//		//cout << u << " ";
		//	//}
		//	//cout << endl << "添加点:";
		//	//for (int u : add_node) {
		//		//cout << u << " ";
		//	//}
		//	out_nonimpr = 0;
		//}

		//vector<ui> tttt(n, 0);
		//for (ui i = 0; i < n; ++i) {
		//	tttt[i] = 0;
		//	if (D[i]) {
		//		for (ui v : graph.adj(i)) {
		//			if (is_dominated[v].size() == 1) { // 只被 i 支配
		//				tttt[i] += weight[v];
		//			}
		//		}
		//	}
		//	else {
		//		for (ui v : graph.adj(i)) {
		//			if (is_dominated[v].size() == 0) { // 未被支配
		//				tttt[i] += weight[v];
		//			}
		//		}
		//	}
		//}
		//for (ui i = 0; i < n; ++i) {
		//	if (tttt[i] != delta[i]) {
		//		cout << "出问题，tttt[" << i << "] = " << tttt[i] << "  delta[" << i << "] = " << delta[i] << endl;
		//		system("pause");
		//	}
		//}
		//iter++;
	}
}

void CFeature_Info::init_delta_config() {
	for (ui i = 0; i < n; i++) {
		//如果是非中心节点，delta为覆盖未覆盖元素数量
		//如果是中心，delta为仅由该中心覆盖元素数量
		if (D[i]) {
			for (ui v : graph.adj(i)) {
				if (dominate_num[v] == 1) { // 只被 i 支配
					delta[i] += weight[v];
					//delta[i]++;
				}
			}
		}
	}
}

void CFeature_Info::check_redundancy_3(ui age) {
	auto it = selected_no_must.begin();
	while (it != selected_no_must.end()) {
		ui v = *it;
		if (delta[v] == 0) {
			// 更新状态
			do_remove(v, age);
			area_D_num[point_to_area[v]]--;
			remove_heap1.update(v, -1e9, 0);
			update_affected_2(v);
			it = selected_no_must.begin();
		}
		else {
			++it;
		}
	}
}

void CFeature_Info::do_add(ui v, ui age_iter) {
	select(v);
	for (ui vc : graph[v]) { // 支配点 v 的邻居 vc

		if (is_dominated[vc].size() == 1) { // 邻居中原来只被一个点支配
			delta[*is_dominated[vc].begin()] -= weight[vc];
		}
		else if (is_dominated[vc].size() == 0) { // 邻居中原来不被支配
			for (ui u : graph[vc]) { // 那么 vc 的邻居 u 都不存在支配点
				if (u == v) continue; // 忽略自己
				delta[u] -= weight[vc]; // 所以选中 v 可支配 vc, 那么 u 要 -vc 的 weight
			}
			no_dominate.erase(vc); // 如果邻居没有被支配，加入未支配集合
			cover_num--;
		}

		is_dominated[vc].insert(v);
		//domination_count[vc]++;
	}


	// 1️⃣ 将 best_v1 加入 selected_no_must
	selected_no_must.emplace_back(v);
	// 2️⃣ 记录 best_v1 在 unselected 的原索引（必须先获取旧值）
	ui old_candidate_idx = point_to_idx[v];
	// 3️⃣ 交换 unselected 中的 best_v1 和末尾元素
	//std::swap(unselected[old_candidate_idx], unselected.back());
	unselected[old_candidate_idx] = unselected.back();
	// 4️⃣ 更新 point_to_idx: 交换后的 unselected.back() 现在在 old_candidate_idx
	point_to_idx[unselected[old_candidate_idx]] = old_candidate_idx;
	// 5️⃣ 更新 point_to_idx: best_v1 现在在 selected_no_must 末尾
	point_to_idx[v] = selected_no_must.size() - 1;
	// 6️⃣ 删除 unselected 的末尾（旧的 best_v1）
	unselected.pop_back();

	tabu[v] = age_iter + 1;
	dominate_age[v] = age_iter;

	update_affected_2(v);
}

void CFeature_Info::do_remove(ui v, ui age_iter) {

	//更新邻域delta
	for (ui vc : graph.adj(v)) // 关闭支配点的邻居vc
	{
		if (is_dominated[vc].size() == 1)// vc只被当前点支配 将变为非支配点 vc = x
		{
			/*if (*is_dominated[vc].begin() != v) {
				cout << "############" << endl;
				system("pause");
			}*/
			for (ui jc : graph.adj(vc)) {
				delta[jc] += weight[vc];
			}
			no_dominate.insert(vc); // 如果邻居没有被支配，加入未支配集合
			cover_num++;
			delta[v] -= weight[vc]; // 之前是只支配vc 加上vc的传播权重，现在是选中可支配vc，加上vc的传播权重 故不变
		}
		else if (is_dominated[vc].size() == 2)// close v 后支配 vc 的点压力变大
		{
			ui domi_1 = *is_dominated[vc].begin(); // 唯一支配点
			ui domi_2 = *next(is_dominated[vc].begin()); // 第二个支配点
			if (domi_1 == v) {
				delta[domi_2] += weight[vc]; // 第二个支配点的压力变大
			}
			else if (domi_2 == v) {
				delta[domi_1] += weight[vc]; // 唯一支配点的压力变大
			}
		}

		is_dominated[vc].erase(v); // 更新邻居的支配点
		//domination_count[vc]--;


	}
	/*for (ui u : nei_2[v]) {
		if (is_fix[u] || temp_set.count(u) || config[u] != 0) continue;
		config[u] = 1;
	}*/
	unselect(v);

	// 1️⃣ 将 best_v1 加入 selected_no_must
	unselected.emplace_back(v);
	// 2️⃣ 记录 best_v1 在 unselected 的原索引（必须先获取旧值）
	size_t old_candidate_idx = point_to_idx[v];
	// 3️⃣ 交换 unselected 中的 best_v1 和末尾元素
	//std::swap(selected_no_must[old_candidate_idx], selected_no_must.back());
	selected_no_must[old_candidate_idx] = selected_no_must.back();
	// 4️⃣ 更新 point_to_idx: 交换后的 unselected.back() 现在在 old_candidate_idx
	point_to_idx[selected_no_must[old_candidate_idx]] = old_candidate_idx;
	// 5️⃣ 更新 point_to_idx: best_v1 现在在 selected_no_must 末尾
	point_to_idx[v] = unselected.size() - 1;
	// 6️⃣ 删除 unselected 的末尾（旧的 best_v1）
	selected_no_must.pop_back();

	tabu[v] = age_iter;
	dominate_age[v] = age_iter; // 重置年龄

}

// 局部改进3
void CFeature_Info::local_improvement_3() {
	nei_2 = vector<robin_hood::unordered_set<ui>>(n);
	for (ui v = 0; v < n; v++) {
		for (ui nei : graph[v]) {
			nei_2[v].insert(nei);
			for (ui nei2 : graph[nei]) {
				nei_2[v].insert(nei2);
			}
		}
	}

	weight = vector<ui>(n, 1);
	delta = vector<ui>(n, 0);
	init_delta_config(); // 初始化 delta

	add_heap1 = WeightMaxHeap(n);
	remove_heap1 = WeightMaxHeap(n);


	for (ui v : unselected) {
		//if (is_fix[v]) system("pause");
		add_heap1.update(v, delta[v], 0);  // 候选插入点
	}

	for (ui v : selected_no_must) {
		//if (is_fix[v]) system("pause");
		remove_heap1.update(v, -1 * delta[v], 0);// 支配集中点
	}


	vector<ui> BMS_unselected;
	BMS_unselected.resize(BMS_sample_size);
	int out_nonimpr = 0;
	ui age_iter = 0; // 年龄迭代器
	//constexpr double TARGET_TIME = 1.0; // 1秒
	//auto start = high_resolution_clock::now();
	//auto elapsed = duration_cast<duration<double>>(
		//high_resolution_clock::now() - start).count();
	//int num_line = 0;
	//bool down_flag = false;
	//cout << "$";
	while (true) {

		//if (Clock::now() > deadline) {
			//saveToFile("C:\\Users\\28172\\Desktop\\ds\\solution\\heuristic\\heuristic_001.txt");
			//break;
		//}
		age_iter++; out_nonimpr++;
		//auto elapsed = duration_cast<duration<double>>(
			//high_resolution_clock::now() - start).count();
		//if (elapsed >= TARGET_TIME) {
			//cout << "Age: " << age_iter << ", Elapsed time: " << elapsed << " seconds" << endl;
			//cout << "cnt_s" << cnt_s << "num" << num <<"num_line" << num_line << "out_nonimpr: " << out_nonimpr << ", cover_num: " << cover_num << endl;
			//start = high_resolution_clock::now();
		//}
		//cout << cnt_d << " " << cnt_s << endl;
		if (cover_num == 0) {

			check_redundancy_3(age_iter); // 检查冗余 移除1

			if (cnt_s < num) {
				num = cnt_s;
				//num_line = cnt_s;
				//down_flag = false;
				global_data = D;
				out_nonimpr = 0;
				//cout << "Best solution size: " << num << endl;
			}


			ui best_v = random_select(selected_no_must);
			do_remove(best_v, age_iter);
			remove_heap1.update(best_v, -1e9, 0); // 更新堆
			//remove_heap1.pop(); // 删除堆顶元素
			//for (ui v_1 : temo_del) {
				//remove_heap1.update(v_1, delta[v_1], config[v_1], dominate_age[v_1]);
				//remove_heap1.remove_by_idx(v_1);
			//}


		}
		else {
			for (ui v_1 : no_dominate) {
				//if (X[v_1]) cout << "$$$$$$$$$$$$$$$$$$$$$" << endl;
				//if (gen() % 100 < 80) continue; // 10% 概率跳过
				weight[v_1] += 1; // 增量权重
				f += 1;
				// 当前点未支配，邻居中不存在支配点故都需要加一
				for (ui ic : graph.adj(v_1)) {
					delta[ic] += 1;
					if (is_fix[ic]) continue; // 忽略固定点
					add_heap1.update(ic, delta[ic], dominate_age[ic]);
				}
			}
		}
		//cout << "当前支配点个数：" << cnt_s << ", best_size: " << best_size << endl;
		// 移除阶段 make |D| = |D*| - 3 or |D*| - 2
		// BMS heuristic: sample t vertices and pick best
		BMS_unselected.clear();
		ui best_v = INT_MAX;
		int best_s = INT_MAX; // best分数
		int age = INT_MAX;

		const auto total = selected_no_must.size();
		const double prob = static_cast<double>(BMS_sample_size) / total;
		std::geometric_distribution<ui> geo_dist(prob);
		for (ui i = 0; i < total && BMS_unselected.size() < BMS_sample_size; ) {
			ui skip = geo_dist(gen);  // 直接计算下一个采样点的距离
			i += skip + 1;             // +1 保证不重复
			if (i < total) {          // 防止越界
				if (delta[selected_no_must[i]] < best_s || (delta[selected_no_must[i]] == best_s && dominate_age[selected_no_must[i]] < age)) {
					best_s = delta[selected_no_must[i]];
					best_v = selected_no_must[i];
					age = dominate_age[selected_no_must[i]];
				}
				//BMS_unselected.emplace_back(selected_no_must[i]);  // 转为 1-based
			}
		}
		//area_idx = point_to_area[best_v]; // 记录当前区域
		// 移除3
		do_remove(best_v, age_iter);
		remove_heap1.update(best_v, -1e9, 0);
		//remove_heap1.remove_by_idx(best_v);

		//cout << "当前支配点个数：" << ds_now_size << ", best_size: " << best_size << endl;
		if (cnt_s == num - 2) {
			// 随机选一个u2
			ui u_2 = random_select(selected_no_must);
			remove_heap1.update(u_2, -1e9, 0);
			do_remove(u_2, age_iter);
			//dist.param(std::uniform_int_distribution<ui>::param_type(0, res_area[area_idx].size() - 1));
			//int size_it = res_area[area_idx].size();
			//int i = dist(gen);
			//int u_f = -1;
			//while (size_it-- >= 0) {
			//	ui u_2 = res_area[area_idx][i];
			//	if (is_fix[u_2] || !D[u_2]) {
			//		if (i + 1 >= res_area[area_idx].size()) {
			//			i = 0; // 如果是固定点或者不在支配集中，跳到下一个点
			//		}
			//		else {
			//			i = i + 1;
			//		}
			//		continue; // 忽略固定点
			//	}
			//	u_f = res_area[area_idx][i]; // 选中一个点
			//	remove_heap1.update(u_f, -1e9, age_iter); // 更新堆
			//	do_remove(u_f, age_iter); // 执行删除操作
			//	break;
			//}
			//if (u_f == -1) {
			//	cout << "@" << u_f << endl;
			//	u_f = random_select(selected_no_must);
			//	remove_heap1.update(u_f, -1e9, age_iter);
			//	do_remove(u_f, age_iter);
			//}

		}
		//cout << "$$$$" << endl;
		// 添加阶段 未支配点 + 未支配邻居 都要计算分数
		// Add first vertex
		//if (urd(gen) < 0.4) {
		ui best_v1 = std::numeric_limits<ui>::max();
		//int best_s1 = -1e9; // best分数
		//int oldest_age1 = -1; // 年龄
		// 如果堆顶元素已经被选中了就继续弹出
		while (selected(add_heap1.top().first) || tabu[add_heap1.top().first] > age_iter) {
			add_heap1.pop(); // 删除堆顶元素
		}
		//cout << add_heap.size() << endl;
		best_v1 = add_heap1.top().first;

		add_heap1.pop(); // 删除堆顶元素
		do_add(best_v1, age_iter);
		//}
		//else {
		//	// 找一波邻居
		//	best_v = INT_MAX;
		//	best_s = 0; // best分数
		//	age = INT_MAX;

		//	static vector<ui> vector_no_dominate; // 备份未支配点集合
		//	vector_no_dominate = vector<ui>(no_dominate.begin(), no_dominate.end());

		//	ui v_f = random_select(vector_no_dominate); // 选点应该在v周围，能够支配v
		//	//for (ui v : no_dominate) {
		//	for (ui nei : graph[v_f]) {
		//		if (is_fix[nei] || D[nei]|| tabu[add_heap1.top().first] > age_iter) continue; // 忽略固定点

		//		if (delta[nei] > best_s || (delta[nei] == best_s && dominate_age[nei] < age)) {
		//			best_s = delta[nei];
		//			best_v = nei;
		//			age = dominate_age[nei];
		//		}
		//	}
		//	//}
		//	if (best_v != INT_MAX) {
		//		do_add(best_v, age_iter);
		//		add_heap1.update(best_v, -1e9, 0);
		//	}

		//}
		// Check if still undominated vertices
		if (cover_num == 0) {
			continue;
		}
		// With probability, add second vertex
		if (urd(gen) < add_prob) {

			ui best_v2 = std::numeric_limits<ui>::max();
			while (selected(add_heap1.top().first) || tabu[add_heap1.top().first] > age_iter) {
				add_heap1.pop(); // 删除堆顶元素
			}
			best_v2 = add_heap1.top().first;
			add_heap1.pop(); // 删除堆顶元素
			do_add(best_v2, age_iter);

		}
		//if (out_nonimpr > 5000 && !down_flag) {
		//		// 配置扩散参数
		//
		//	std::bernoulli_distribution dist_prob(0.7);         // 每层衰减概率 70%
		//	int cnt_del = 0;
		//	// 随机选择中心点
		//	ui del_v = random_select(selected_no_must);
		//	ui radius = 2;

		//	// 分层扩散删除
		//	std::queue<std::pair<ui, ui>> q;  // <节点, 当前层数>
		//	flat_hash_set<ui> visited;
		//	q.push({ del_v, 0 });
		//	visited.insert(del_v);

		//	while (!q.empty()) {
		//		auto p = q.front();
		//		q.pop();

		//		// 删除条件：非固定 + 是支配点 + 概率通过
		//		if (!is_fix[p.first] && D[p.first] && (p.second == 0 || dist_prob(gen))) {
		//			do_remove(p.first, age_iter);
		//			remove_heap1.update(p.first, -1e9, 0);  // 从堆中移除
		//			cnt_del++;
		//		}

		//		// 向下一层扩散
		//		if (p.second < radius) {
		//			for (ui u : nei_2[p.first]) {  // 使用二阶邻居（可替换为 nei_1）
		//				if (!visited.count(u)) {
		//					visited.insert(u);
		//					q.push({ u, p.second + 1 });
		//				}
		//			}
		//		}
		//	}
		//	//cout << cnt_del << " nodes removed." << endl;
			//num_line = num - cnt_del;
			//down_flag = true;

			//while (cover_num != 0) {
			//	//cout << "### " << endl;
			//	int v_open = -1, v_close = -1;
			//	findBestSwap1(v_open, v_close, age_iter);
			//	//cout << "Best swap: " << v_open << " " << v_close << endl;
			//	//cout << "Best f size: " << f << endl;
			//	if (v_open == -1 || v_close == -1) {
			//		continue;
			//	}
			//	do_add(v_open, age_iter);
			//	add_heap1.update(v_open, -1e9, dominate_age[v_open]);
			//	do_remove(v_close, age_iter);
			//	remove_heap1.update(v_close, -1e9, dominate_age[v_open]);
			//	cout << "Best e: " << v_open << "  and  " << v_close << "  " << cover_num << endl;
			//	//cout << "best_delta_f: " << best_delta_f << endl;
			//	//SwapMove(v_open, v_close);
			//	if (cover_num != 0) {
			//		for (ui v_1 : no_dominate) {
			//			//if (X[v_1]) cout << "$$$$$$$$$$$$$$$$$$$$$" << endl;
			//			//if (gen() % 100 < 80) continue; // 10% 概率跳过
			//			weight[v_1] += 1; // 增量权重
			//			f += 1;
			//			// 当前点未支配，邻居中不存在支配点故都需要加一
			//			for (ui ic : graph.adj(v_1)) {
			//				delta[ic] += 1;
			//				if (is_fix[ic]) continue; // 忽略固定点
			//				add_heap1.update(ic, delta[ic], dominate_age[ic]);
			//			}
			//		}
			//	}
			//}
		//}
		//if (out_nonimpr > 20000) {
		//	//cout << "$$" << no_dominate.size() << " " << cnt_s << endl;
		//	// 配置扩散参数
		//	std::uniform_int_distribution<ui> dist_radius(1, 3); // 扩散半径 1~3 层
		//	std::bernoulli_distribution dist_prob(0.7);         // 每层衰减概率 70%
		//	int cnt_del = 0;
		//	// 随机选择中心点
		//	ui del_v = random_select(selected_no_must);
		//	ui radius = dist_radius(gen);

		//	// 分层扩散删除
		//	std::queue<std::pair<ui, ui>> q;  // <节点, 当前层数>
		//	flat_hash_set<ui> visited;
		//	q.push({ del_v, 0 });
		//	visited.insert(del_v);

		//	while (!q.empty()) {
		//		auto p = q.front();
		//		q.pop();

		//		// 删除条件：非固定 + 是支配点 + 概率通过
		//		if (!is_fix[p.first] && D[p.first] && (p.second == 0 || dist_prob(gen))) {
		//			do_remove(p.first, age_iter);
		//			remove_heap1.update(p.first, -1e9, 0);  // 从堆中移除
		//			cnt_del++;
		//		}

		//		// 向下一层扩散
		//		if (p.second < radius) {
		//			for (ui u : nei_2[p.first]) {  // 使用二阶邻居（可替换为 nei_1）
		//				if (!visited.count(u)) {
		//					visited.insert(u);
		//					q.push({ u, p.second + 1 });
		//				}
		//			}
		//		}
		//	}
		//	//cout << cnt_del << " nodes removed." << endl;
		//	while (cover_num != 0 && cnt_del-- > 0) {
		//		// 重新贪心选择新支配点（补回被删除的点）
		//		ui best_v = std::numeric_limits<ui>::max();
		//		int best_s = 0; // best分数
		//		int age = INT_MAX;
		//		for (ui u : no_dominate) {
		//			for (ui nei : graph[u]) {
		//				if (is_fix[nei]) continue; // 忽略固定点
		//				//cout << delta[nei] << " ";
		//				if (delta[nei] > best_s || (delta[nei] == best_s && dominate_age[nei] < age)) {
		//					best_s = delta[nei];
		//					best_v = nei;
		//					age = dominate_age[nei];
		//				}
		//				
		//			}
		//		}
		//		if (best_v != std::numeric_limits<ui>::max()) {
		//			do_add(best_v, age_iter);
		//			add_heap1.update(best_v, -1e9, 0);
		//		}
		//		if (cover_num != 0) {
		//			for (ui v_1 : no_dominate) {
		//				//if (X[v_1]) cout << "$$$$$$$$$$$$$$$$$$$$$" << endl;
		//				weight[v_1] += 1; // 增量权重
		//				f += 1;
		//				// 当前点未支配，邻居中不存在支配点故都需要加一
		//				for (ui ic : graph.adj(v_1)) {
		//					delta[ic] += 1;
		//					if (is_fix[ic]) continue; // 忽略固定点
		//					add_heap1.update(ic, delta[ic], dominate_age[ic]);
		//				}
		//			}
		//		}
		//	}
		//	out_nonimpr = 0;
		//	////cout << "check1" << endl;
		//	//vector<char> back_D = D; // 备份 D
		//	//int in_nonimpr = 0; // 非改善计数
		//	//int innerDepth = 47; // 内部深度
		//	//vector<ui> temp_no_dominate(no_dominate.begin(), no_dominate.end()); // 备份未支配点集合
		//	//while (true) {

		//	//	while (cover_num != 0) {
		//	//		temp_no_dominate.clear();
		//	//		temp_no_dominate.insert(temp_no_dominate.end(), no_dominate.begin(), no_dominate.end()); // 备份未支配点集合
		//	//		ui rand_v = random_select(temp_no_dominate);
		//	//		rand_v = adding_rule(rand_v); // 选择一个点
		//	//		do_add(rand_v, age_iter - 1);
		//	//		//add_heap1.remove_by_idx(rand_v); // 从堆中删除
		//	//		add_heap1.update(rand_v, -1e9, 0);
		//	//		if (cover_num != 0) {
		//	//			for (ui v_1 : no_dominate) {
		//	//				//if (X[v_1]) cout << "$$$$$$$$$$$$$$$$$$$$$" << endl;
		//	//				weight[v_1] += 1; // 增量权重
		//	//				f += 1;
		//	//				// 当前点未支配，邻居中不存在支配点故都需要加一
		//	//				for (ui ic : graph.adj(v_1)) {
		//	//					delta[ic] += 1;
		//	//					if (is_fix[ic]) continue; // 忽略固定点
		//	//					add_heap1.update(ic, delta[ic], dominate_age[ic]);
		//	//				}
		//	//			}
		//	//		}
		//	//		else break;

		//	//	}
		//	//	//cout << "check2" << endl;
		//	//	check_redundancy_3(age_iter - 1); // 检查冗余 移除1

		//	//	//cout << "check3" << endl;
		//	//	if (cover_num == 0) {
		//	//		//cout << "dep_Best solution size: " << num << "  " << out_nonimpr << "  " << in_nonimpr << endl;
		//	//		if (cnt_s < num) {
		//	//			num = cnt_s;
		//	//			global_data = D;
		//	//			in_nonimpr = 0;
		//	//		}
		//	//		if (in_nonimpr > innerDepth) {
		//	//			out_nonimpr = 0;
		//	//			break;
		//	//		}
		//	//	}
		//	//	//cout << "check4" << endl;
		//	//	// 删两个扰动
		//	//	// no1
		//	//	// 如果堆顶元素已经被删了就继续弹出
		//	//	ui top_v = remove_heap1.top().first;
		//	//	while (!selected(top_v)) {
		//	//		remove_heap1.pop(); // 删除堆顶元素
		//	//		top_v = remove_heap1.top().first;
		//	//	}
		//	//	do_remove(top_v, age_iter - 1);
		//	//	remove_heap1.pop(); // 删除堆顶元素
		//	//	// no2
		//	//	// 随机选一个u2
		//	//	ui u_2 = random_select(selected_no_must);
		//	//	while (back_D[u_2]) {
		//	//		u_2 = random_select(selected_no_must);
		//	//	}
		//	//	remove_heap1.update(u_2, -1e9, 0);
		//	//	//remove_heap1.remove_by_idx(u_2);
		//	//	do_remove(u_2, age_iter - 1);

		//	//	in_nonimpr++;
		//	//}
		//}
	}
}

//-------------------------------
// 安全打印单个数字（带换行）
//-------------------------------
void safe_print_num(unsigned int n) {
	char buf[32];
	int len = snprintf(buf, sizeof(buf), "%u\n", n);  // 数字+换行一次性格式化

#ifdef _WIN32
	HANDLE stdout_handle = GetStdHandle(STD_OUTPUT_HANDLE);
	DWORD written;
	WriteFile(stdout_handle, buf, len, &written, NULL);
#else
	write(STDOUT_FILENO, buf, len);
#endif
}

//-------------------------------
// 终止处理（信号安全）
//-------------------------------
#ifdef _WIN32
BOOL WINAPI CtrlHandler(DWORD fdwCtrlType) {
	if (fdwCtrlType == CTRL_C_EVENT || fdwCtrlType == CTRL_CLOSE_EVENT) {
		safe_print_num(num);
		for (unsigned int i = 0; i < all_point; ++i) {
			if (global_data[i] == 1) safe_print_num(i + 1);
		}
		ExitProcess(0);
		return TRUE;
	}
	return FALSE;
}
#else
void signal_handler(int sig) {
	safe_print_num(num);
	for (unsigned int i = 0; i < all_point; ++i) {
		if (global_data[i] == 1) safe_print_num(i + 1);
	}
	_exit(0);
}
#endif

void saveToFile(const string& filename) {
	ofstream outfile(filename); // 创建/覆盖文件

	/**/outfile << num << endl;
	for (ui i = 0; i < all_point; i++) {
		if (global_data[i] == 1) outfile << i + 1 << endl;
	}

	outfile.close(); // 显式关闭（实际上析构时会自动关闭）

}


void gracefulExit(int sig) {
	/*std::cout << "\n捕获信号: " << sig
		<< " - 正在保存进度..." << std::endl;*/
		// 输出改用 printf（确保性能和无序问题）
	//saveToFile("C:\\Users\\28172\\Desktop\\ds\\solution\\heuristic\\heuristic_001.txt");
	printf("%u\n", num);
	for (ui i = 0; i < all_point; i++) {
		if (global_data[i] == 1) printf("%u\n", i + 1);
	}
	cout.flush(); // 确保所有输出完成
	exit(0); // 必须调用exit，不可用return
	// 提交
	/*safe_print_num(STDOUT_FILENO, num);
	for (unsigned i = 0; i < all_point; ++i) {
		if (global_data[i] == 1) {
			safe_print_num(STDOUT_FILENO, i + 1);
		}
	}
	_exit(0);*/
}

int main() {

#ifdef _WIN32
	SetConsoleCtrlHandler(CtrlHandler, TRUE);
#else
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);
#endif
	//// 设置优雅退出处理器
	//goal::os::setSignalHandler(gracefulExit);
	//// 主程序逻辑（示例）
	////  提交版
	ugraph read = read_graph();
	//// 测试版
	//string name = "heuristic_";
	//string back; cin >> back;
	//ifstream ifs("C:\\Users\\28172\\Desktop\\ds\\heuristic\\" + name + back + ".gr");
	//ugraph read = read_graph(ifs);
	iterated_greedy(read);
	//// 恢复默认处理器（可选）
	//goal::os::resetSignalHandler();

	return 0;
}