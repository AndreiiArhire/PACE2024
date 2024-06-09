#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <deque>
#include <queue>
#include <iomanip>
#include <stack>
#include <chrono>
#include <stdio.h>
#include <array>        
#include <random>       
#include <chrono> 
#include <string> 
#include <unordered_set>
#include <unordered_map>
#include "Highs.h"
#include <iostream>
#include <vector>
#include <stdexcept>
#include <queue>

using namespace std;
#define ever (;;)
#define SECONDS 285
#define debug false
const int MOD1 = 100000007;
const int PRIME1 = 10000019;
const int MOD2 = 100000037;
const int PRIME2 = 10000079;
const int EXIT_CODE = 1;
std::chrono::time_point<std::chrono::high_resolution_clock> beginTime;

double check_time() {
	auto curTime = std::chrono::high_resolution_clock::now();
	auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(curTime - beginTime);
	double sec = elapsed.count() * 1e-9;
	return sec;
}

void ckeck_force_stop() {
	auto end = std::chrono::high_resolution_clock::now();
	auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(end - beginTime);
	double sec = elapsed.count() * 1e-9;
	if (sec > 30 * 60 - 10) {
		exit(EXIT_CODE);
	}
}

struct pair_hash {
	template <class T1, class T2>
	std::size_t operator () (const std::pair<T1, T2>& p) const {
		auto a = std::hash<T1>{}(p.first);
		auto b = std::hash<T2>{}(p.second);
		// Cantor function for pairing hash
		return  1ll * (1ll * (a + b) * (a + b + 1) / 2 + 1ll * b) % 1000000009;
	}
};


unordered_map < pair <int, int>, int, pair_hash > hash_to_index;
vector< pair <int, int> > hashes;
vector<long long> bkt_hashes(1000000, 0);


int na, n, m;
vector<int> mobile_edges[1000005];
vector<int> fixed_edges[1000005];
vector<pair<int, int>> input;
set <int> fixed_set, mobile_set;
vector<int> fixed_vec, mobile_vec, fixed_nodes, mobile_nodes;
map <int, int> fixed_pos, mobile_pos, real_mobile_nodes;
vector<pair<int, int>> fixed_nodes_range;
vector<int> mobile_isolated;
vector<vector<int>> bb_comps;
vector<vector<int>> fixed_interval_starter;
vector<vector<int>> compressed;
vector< pair <vector<int>, int> > mobile_nodes_lists;
vector<pair<pair<int, int>, vector<int>> > ret, secv;
vector <pair< pair <int, int>, int >> mobile_ends;
vector< unordered_set <int> > bkt_comps;
vector<set <int>> tree_edges(bb_comps.size(), set<int>());
vector<vector<long long>> scor;
//vector<vector<long long>> scor2;
vector<vector<int>> must_before;
vector<int>prt;
int bb_root;
int test;
long long cost_overall, bestKnown;
set <pair <int, int>> pairs;

const int oo = ((int)1e9);
int last_a[20005];
long long dp_a[20005];
int ansBkt[20005];
bool isUsed[20005];
long long dp_pref[20005];
int inv[20005];
int ansFinal[20005];
vector<long long>dp_lb(200000, 1000000000);
vector<long long>dp_lb_in(200000, 1000000000);

std::vector<int> run_ilp(int n, const std::vector<std::vector<int>>& score);

void preprocess_branch_and_bound(vector<int>& heuristic, long long& lower_bound, long long& upper_bound);

using namespace std;

Highs highs;
long long val;
std::vector<int> run_ilp(int n, const std::vector<std::vector<int>>& score) {
	val = 0;
	highs.clearModel();
	highs.setOptionValue("output_flag", false);
	highs.setOptionValue("threads", 1);

	int num_vars = n * (n - 1);

	std::vector<double> col_cost(num_vars, 0.0);
	std::vector<double> col_lower(num_vars, 0.0);
	std::vector<double> col_upper(num_vars, 1.0);

	std::vector<int> x_idx(n * n, -1);
	int idx = 0;
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			if (i != j) {
				col_cost[idx] = score[i][j];
				x_idx[i * n + j] = idx++;
			}
		}
	}

	highs.addCols(num_vars, col_cost.data(), col_lower.data(), col_upper.data(), 0, nullptr, nullptr, nullptr);

	std::vector<int> Astart;
	std::vector<int> Aindex;
	std::vector<double> Avalue;
	std::vector<double> row_lower;
	std::vector<double> row_upper;

	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			if (i != j) {
				Astart.push_back(Aindex.size());
				pair <int, int> currPair = make_pair(i, j);
				pair <int, int> invPair = make_pair(j, i);
				if (pairs.count(currPair)) {
					Aindex.push_back(x_idx[i * n + j]);
					Avalue.push_back(1.0);
					row_lower.push_back(1.0);
					row_upper.push_back(1.0);
				}
				else if (pairs.count(invPair)) {
					Aindex.push_back(x_idx[i * n + j]);
					Avalue.push_back(0.0);
					row_lower.push_back(0.0);
					row_upper.push_back(0.0);
				}
				else {
					Aindex.push_back(x_idx[i * n + j]);
					Aindex.push_back(x_idx[j * n + i]);
					Avalue.push_back(1.0);
					Avalue.push_back(1.0);
					row_lower.push_back(1.0);
					row_upper.push_back(1.0);
				}
			}
		}
	}
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			for (int k = 0; k < n; k++) {
				if (i != j && j != k && i != k) {
					if (pairs.count(make_pair(j, i)) ||
						pairs.count(make_pair(k, j)) ||
						pairs.count(make_pair(i, k)))
					{

						continue;
					}
					val += 9 * 8;
					Astart.push_back(Aindex.size());
					Aindex.push_back(x_idx[i * n + j]);
					Aindex.push_back(x_idx[j * n + k]);
					Aindex.push_back(x_idx[i * n + k]);
					Avalue.push_back(1.0);
					Avalue.push_back(1.0);
					Avalue.push_back(-1.0);
					row_lower.push_back(-kHighsInf);
					row_upper.push_back(1.0);
				}
			}
		}
	}
	Astart.push_back(Aindex.size());

	highs.addRows(row_lower.size(), row_lower.data(), row_upper.data(), Aindex.size(), Astart.data(), Aindex.data(), Avalue.data());
	highs.changeObjectiveSense(ObjSense::kMinimize);
	HighsStatus status = highs.run();
	if (status != HighsStatus::kOk) {
		throw std::runtime_error("HiGHS failed to solve the ILP problem.");
	}

	const HighsSolution& solution = highs.getSolution();

	std::vector<std::vector<int>> adjacency_list(n);
	std::vector<int> in_degree(n, 0);

	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			if (i != j && solution.col_value[x_idx[i * n + j]] > 0.5) {
				adjacency_list[i].push_back(j);
				in_degree[j]++;
			}
		}
	}

	std::vector<int> sorted_order;
	std::queue<int> zero_in_degree;
	for (int i = 0; i < n; ++i) {
		if (in_degree[i] == 0) {
			zero_in_degree.push(i);
		}
	}

	while (!zero_in_degree.empty()) {
		int node = zero_in_degree.front();
		zero_in_degree.pop();
		sorted_order.push_back(node);

		for (int neighbor : adjacency_list[node]) {
			if (--in_degree[neighbor] == 0) {
				zero_in_degree.push(neighbor);
			}
		}
	}

	if (sorted_order.size() != n) {
		throw std::runtime_error("Topological sorting failed; graph has a cycle.");
	}
	return sorted_order;
}


vector<vector<int>>perms_chunks[10], perms_gaps[10];
vector < pair < vector<vector<int>>, vector<vector<int>> > > move_rules[2];

pair <int, int> get_hash(vector<int>& val);

long long cntCross(vector<int>& a, vector<int>& b);

void get_score_table();

long long get_brut_score(vector<int>& perm, int st, int dr);

void fun(int fix_node);

void update_scores(vector<int>& perm);

void dfs(int pos);

bool cmpList(pair <vector<int>, int >& a, pair <vector<int>, int>& b);

bool cmpSimpleList(vector<int>& a, vector<int>& b);

bool egal(vector<int>& a, vector<int>& b);

void delete_nodes(vector<int>& v);

void eliminate_mobile_duplicates();

void clear_data();

bool cmpEnds(pair <pair <int, int>, int> i, pair <pair<int, int>, int> j);

void preprocess_and_build_tree();

void run_branch_bound_solver_and_check(vector<int>& sol);

long double avg[200005];

bool compAvg(int x, int y);

int custom_pop_count(int x);

void brut_reord(vector<int>& v, int st, int dr, int maxDist);

bool calc_dp_andrei(int start_pos, vector<int>szChunks, vector<int> szGaps, vector<int>& s);

void apply_just_dp(int st, int dr, vector<int>& s, int search_type = 0);

void try_optimize(vector<int>& s, int st, int dr);

void run_local_search(vector<int>& s, int st, int dr);

void run_heuristic(vector<int>& s);

void preprocess_ilp(vector<int>& heuristic);

void run_branch_and_bound(int p, long long curScore, long long lowerBound, long long right_lb, long long upperBound, vector<int>& val);

bool check_dp(int dr, int szBuc);

bool check_shift(int p);

bool check_bef(int p);

bool check_dp_pref(int dr, long long curScore);

void print_result(vector<int>& sol);

void solve_brance_and_bound(vector <int>& s);

long long get_minimal_lowerbound(vector<int>& act, int st, int dr);

long long get_extra_segment(vector<int>& act);



int cnt = 0;

long long get_extra_lower_bound(vector<int>& val, vector<int>& lb);

bool check_hash(vector<int>& val, long long cost);


void run_branch_and_bound(int p, long long curScore, long long lowerBound, long long right_lb, long long upperBound, vector<int>& val) {
	ckeck_force_stop();
	if (p != 0) {
		vector<int> lb;
		long long best_lower_bound = lowerBound + get_extra_lower_bound(val, lb);
		long long best_right_lower_bound = right_lb + get_extra_lower_bound(val, lb);


		if (curScore + best_lower_bound >= bestKnown)
			return;

		if (best_right_lower_bound == upperBound) {
			bestKnown = curScore + best_lower_bound;

			for (int i = p; i < val.size(); ++i) {
				ansFinal[i] = lb[i - p];
			}

			for (int i = 0; i < p; i++)
				ansFinal[i] = ansBkt[i];
			return;
		}

		if (!check_dp(p - 1, min(10, p)))
			return;

		if (!check_shift(p - 1))
			return;

		if (!check_bef(p - 1))
			return;

		if (!check_dp_pref(p - 1, curScore))
			return;

		if (!check_hash(val, curScore))
			return;

	}

	if (p == (int)val.size())
	{
		bestKnown = curScore;
		for (int i = 0; i < (int)val.size(); i++)
			ansFinal[i] = ansBkt[i];
		return;
	}

	int fixedNxt = 0;

	for (int nxtVal : val)
	{
		if (isUsed[nxtVal])
			continue;

		bool ok = true;
		for (int aft : val)
		{
			if (isUsed[aft] || aft == nxtVal)
				continue;

			if (scor[nxtVal][aft] > scor[aft][nxtVal])
			{
				ok = false;
				break;
			}
		}

		if (ok)
		{
			fixedNxt = nxtVal;
			break;
		}
	}

	if (!fixedNxt && (int)val.size() - p <= 10) {
		vector<int> act;
		for (int x : val)
			if (!isUsed[x]) {
				act.emplace_back(x);
			}
		calc_dp_andrei(0, vector<int>() = { (int)act.size() }, vector<int>(), act);
		fixedNxt = act[0];
	}

	for (int nxtVal : val)
	{
		if (fixedNxt)
			nxtVal = fixedNxt;

		if (isUsed[nxtVal])
			continue;

		long long newCurScore = curScore;
		long long newLowerBound = lowerBound;
		long long newUpperBound = upperBound;
		long long new_right_lb = right_lb;

		for (int bef : val)
			if (isUsed[bef])
			{
				newCurScore += scor[bef][nxtVal];
				newLowerBound -= scor[bef][nxtVal];
			}

		for (int aft : val)
		{
			if (isUsed[aft] || aft == nxtVal)
				continue;
			new_right_lb -= min(scor[nxtVal][aft], scor[aft][nxtVal]);
			newLowerBound -= min(scor[nxtVal][aft], scor[aft][nxtVal]);
			newLowerBound += scor[nxtVal][aft];

			if (inv[aft] < inv[nxtVal]) {
				newUpperBound -= scor[aft][nxtVal];
			}
			else {
				newUpperBound -= scor[nxtVal][aft];
			}
		}

		isUsed[nxtVal] = true;
		ansBkt[p] = nxtVal;
		run_branch_and_bound(p + 1, newCurScore, newLowerBound, new_right_lb, newUpperBound, val);
		isUsed[nxtVal] = false;

		if (fixedNxt)
			return;
	}
}


int main() {
	beginTime = std::chrono::high_resolution_clock::now();

	string s;
	cin >> s >> s;
	cin >> na >> n >> m;
	for (int i = 1; i <= m; i++) {
		int x, y;
		cin >> x >> y;
		input.emplace_back(make_pair(x, y - na));
		fixed_set.insert(x);
		mobile_set.insert(y - na);
	}

	preprocess_and_build_tree();

	vector<int> sol;

	run_branch_bound_solver_and_check(sol);

	print_result(sol);

	return 0;
}


void print_result(vector <int>& sol) {
	for (auto it : mobile_isolated) {
		std::cout << it + na << '\n';
	}
	for (auto it : sol) {
		std::cout << mobile_vec[it - 1] + na << '\n';
	}
}

bool check_dp_pref(int dr, long long curScore) {
	int max_id = -1;
	for (int i = 0; i <= dr; i++)
		max_id = max(max_id, inv[ansBkt[i]]);

	if (max_id != dr)
		return true;

	if (curScore < dp_pref[dr])
	{
		dp_pref[dr] = curScore;
		return true;
	}

	return false;

}

bool check_bef(int p) {
	for (int it : must_before[ansBkt[p]])
		if (!isUsed[it])
			return false;

	return true;
}

bool check_shift(int p) {
	long long val = 0;
	for (int j = p - 1; j >= 0; j--)
	{
		val -= scor[ansBkt[j]][ansBkt[p]];
		val += scor[ansBkt[p]][ansBkt[j]];

		if (val < 0)
			return false;
	}

	return true;
}

bool check_dp(int dr, int szBuc) {
	int st = dr - szBuc + 1;

	long long curScor = 0;
	for (int i = st; i <= dr; i++)
		for (int j = i + 1; j <= dr; j++)
			curScor += scor[ansBkt[i]][ansBkt[j]];

	vector<int> buc;
	for (int i = st; i <= dr; ++i) {
		buc.emplace_back(ansBkt[i]);
	}
	calc_dp_andrei(0, vector<int>() = { szBuc }, vector<int>(), buc);

	long long dpScor = get_brut_score(buc, 0, buc.size() - 1);

	if (curScor > dpScor)
		return false;

	return true;
}

void preprocess_branch_and_bound(vector<int>& heuristic, long long& lower_bound, long long& upper_bound) {
	lower_bound = 0;
	upper_bound = 0;
	for (int i = 0; i < heuristic.size(); ++i) {
		for (int j = i + 1; j < heuristic.size(); ++j) {
			lower_bound += min(scor[heuristic[i]][heuristic[j]], scor[heuristic[j]][heuristic[i]]);
		}
	}
	for (int i = 0; i < heuristic.size(); ++i) {
		for (int j = i + 1; j < heuristic.size(); ++j) {
			upper_bound += scor[heuristic[i]][heuristic[j]];
		}
	}
	for (int i = 0; i < heuristic.size(); ++i) {
		for (int j = 0; j < heuristic.size(); ++j) {
			int x = heuristic[i];
			int y = heuristic[j];

			if (x == y) {
				continue;
			}
			if (scor[x][y] == 0 && scor[y][x] > 0)
			{
				must_before[y].push_back(x);
			}

			else
				if (heuristic.size() <= 1000)
				{
					bool all_strict = true;
					bool all_egal = true;

					if (scor[x][y] > scor[y][x] || (scor[x][y] == scor[y][x] && inv[x] < inv[y])) {
						continue;
					}

					for (int z : heuristic)
					{
						if (z == x || z == y)
							continue;

						long long scor_a = scor[x][z] + scor[z][y];
						long long scor_b = scor[y][z] + scor[z][x];

						all_strict &= (scor_a < scor_b);
						all_egal &= (scor_a <= scor_b);

						if (!(all_strict || (all_egal && inv[x] < inv[y])))
							break;
					}

					if (all_strict || (all_egal && inv[x] < inv[y]))
						must_before[y].push_back(x);
				}
		}
	}
}


void preprocess_ilp(vector<int>& heuristic) {

	for (int i = 0; i < heuristic.size(); ++i) {
		for (int j = 0; j < heuristic.size(); ++j) {
			int x = heuristic[i];
			int y = heuristic[j];

			if (x == y) {
				continue;
			}
			if (scor[x][y] == 0 && scor[y][x] > 0)
			{
				must_before[j].push_back(i);
			}

			else
				if (heuristic.size() <= 1000)
				{
					bool all_strict = true;
					bool all_egal = true;

					if (scor[x][y] > scor[y][x] || (scor[x][y] == scor[y][x] && inv[x] < inv[y])) {
						continue;
					}

					for (int z : heuristic)
					{
						if (z == x || z == y)
							continue;

						long long scor_a = scor[x][z] + scor[z][y];
						long long scor_b = scor[y][z] + scor[z][x];

						all_strict &= (scor_a < scor_b);
						all_egal &= (scor_a <= scor_b);

						if (!(all_strict || (all_egal && inv[x] < inv[y])))
							break;
					}

					if (all_strict || (all_egal && inv[x] < inv[y]))
						must_before[j].push_back(i);
				}
		}
	}
}


void run_heuristic(vector<int>& s) {
	sort(s.begin(), s.end(), compAvg);
	try_optimize(s, 0, s.size() - 1);
	auto st = check_time();
	for (int c = 20; c <= 100 && check_time() - st < 30; c += 20) {
		for (int i = 0; i + c < s.size() && check_time() - st < 30; i += c / 2) {
			run_local_search(s, i, i + c);
		}
		try_optimize(s, 0, s.size() - 1);
	}
}


void run_branch_bound_solver_and_check(vector<int>& sol) {
	vector<int> tt;
	for (auto it : bkt_comps.back()) {
		tt.emplace_back(it);
	}
	dfs(bb_root);
	sol = compressed[mobile_nodes[0]];
}

void preprocess_and_build_tree() {
	for (auto node : fixed_set) {
		fixed_vec.emplace_back(node);
		fixed_pos[node] = fixed_vec.size();
		fixed_nodes.emplace_back(fixed_vec.size());
	}
	for (auto node : mobile_set) {
		mobile_vec.emplace_back(node);
		mobile_pos[node] = mobile_vec.size();
		mobile_nodes.emplace_back(mobile_vec.size());
	}


	hashes.resize(2 * mobile_nodes.size() + 5, make_pair(PRIME1, PRIME2));
	for (int i = 1; i < hashes.size(); ++i) {
		hashes[i].first = 1ll * hashes[i - 1].first * PRIME1 % MOD1;
		hashes[i].second = 1ll * hashes[i - 1].second * PRIME2 % MOD2;
	}



	std::sort(fixed_nodes.begin(), fixed_nodes.end());
	std::sort(mobile_nodes.begin(), mobile_nodes.end());
	fixed_nodes_range.resize(fixed_nodes.size() + 1, make_pair(1000000000, -1));
	fixed_interval_starter.resize(fixed_nodes.size() + 1, vector<int>());

	for (auto edge : input) {
		int fixed_node = fixed_pos[edge.first];
		int mobile_node = mobile_pos[edge.second];
		fixed_edges[fixed_node].emplace_back(mobile_node);
		mobile_edges[mobile_node].emplace_back(fixed_node);
	}
	scor.resize(mobile_nodes.size() + 1, vector<long long>(mobile_nodes.size() + 1, 0));

	for (auto node : mobile_nodes) {
		std::sort(mobile_edges[node].begin(), mobile_edges[node].end());
	}
	for (auto node : fixed_nodes) {
		std::sort(fixed_edges[node].begin(), fixed_edges[node].end());
	}

	get_score_table();
	must_before.resize(mobile_nodes.size() + 1, vector<int>());
	prt.resize(mobile_nodes.size() + 1, 0);
	for (int i = 1; i <= mobile_nodes.size(); ++i) {
		prt[i] = i;
	}
	for (int i = 1; i <= n; ++i) {
		if (!mobile_set.count(i)) {
			mobile_isolated.emplace_back(i);
		}
	}

	eliminate_mobile_duplicates();

	for (auto node : mobile_nodes)
	{
		avg[node] = 0;

		for (int it : mobile_edges[node])
			avg[node] += it;

		avg[node] /= (long double)mobile_edges[node].size();
	}


	for (auto node : mobile_nodes) {
		fixed_interval_starter[mobile_edges[node][0]].emplace_back(node);
	}

	for (int i = 0; i < fixed_nodes.size(); ++i) {
		int node = fixed_nodes[i];
		for (auto it : fixed_edges[node]) {
			fixed_nodes_range[node].first = min(fixed_nodes_range[node].first, mobile_edges[it][0]);
			fixed_nodes_range[node].second = max(fixed_nodes_range[node].second, mobile_edges[it].back());
		}
	}
	for (int p1 = 0; p1 < fixed_nodes.size(); ++p1) {
		auto node = fixed_nodes[p1];

		if (fixed_interval_starter[node].empty()) {
			continue;
		}
		set <int> current_comp;
		int left_from_mobile = node;

		int right_from_fixed = node;

		for (auto node : fixed_interval_starter[node]) {
			right_from_fixed = max(right_from_fixed, mobile_edges[node].back());
			current_comp.insert(node);
		}
		int right_from_mobile = right_from_fixed;
		for (int fixed = p1 + 1; fixed < fixed_nodes.size(); ++fixed) {

			if (fixed_nodes_range[fixed_nodes[fixed]].first < left_from_mobile) {
				break;
			}
			if (fixed_nodes[fixed] == right_from_mobile && fixed_nodes[fixed] >= right_from_fixed) {
				vector<int> act;

				for (auto it : current_comp) {
					act.emplace_back(it);
				}

				if (act.size() > 1 && (bb_comps.empty() || (!egal(bb_comps.back(), act)))) {
					bb_comps.emplace_back(act);
				}
				break;
			}

			for (auto mobile : fixed_interval_starter[fixed_nodes[fixed]]) {
				right_from_mobile = max(right_from_mobile, mobile_edges[mobile].back());
				current_comp.insert(mobile);
			}
		}
	}
	//bb_comps.clear();
	for (auto it : mobile_nodes) {
		mobile_ends.emplace_back(make_pair(make_pair(mobile_edges[it][0], mobile_edges[it].back()), it));
	}
	sort(mobile_ends.begin(), mobile_ends.end(), cmpEnds);
	int last_right_end = -1;
	vector <int> act_comp;
	for (auto i : mobile_ends) {
		if (last_right_end == -1) {
			last_right_end = i.first.second;
			act_comp.emplace_back(i.second);
			continue;
		}
		if (i.first.first < last_right_end) {
			act_comp.emplace_back(i.second);
			last_right_end = max(last_right_end, i.first.second);
		}
		else {
			bb_comps.emplace_back(act_comp);
			last_right_end = i.first.second;
			act_comp = vector<int>() = { i.second };
		}
	}
	bb_comps.emplace_back(act_comp);
	act_comp.clear();

	if (bb_comps.back().size() != mobile_nodes.size()) {
		for (auto it : mobile_nodes) {
			act_comp.emplace_back(it);
		}
		bb_comps.emplace_back(act_comp);
		act_comp = vector<int>();
	}

	for (int i = 0; i < bb_comps.size(); ++i) {
		sort(bb_comps[i].begin(), bb_comps[i].end());
	}

	sort(bb_comps.begin(), bb_comps.end(), cmpSimpleList);


	for (int i = 0; i < bb_comps.size(); ++i) {
		if (i > 0 && egal(bb_comps[i], bb_comps[i - 1])) {
			continue;
		}
		unordered_set <int> act;
		for (auto l : bb_comps[i]) {
			act.insert(l);
		}
		bkt_comps.emplace_back(act);
	}

	bb_root = bkt_comps.size() - 1;
	tree_edges.resize(bkt_comps.size(), set<int>());
	for (auto node : mobile_nodes) {
		vector < pair <int, int> > act;
		for (int i = 0; i < bkt_comps.size(); ++i) {
			if (bkt_comps[i].count(node)) {
				act.emplace_back(make_pair(bkt_comps[i].size(), i));
			}
		}
		sort(act.begin(), act.end());
		for (int l = 0; l < act.size(); ++l) {
			for (int p = l + 1; p < act.size(); ++p) {
				tree_edges[act[p].second].insert(act[l].second);
				break;
			}
		}
	}

	perms_chunks[1].emplace_back(vector<int>() = { 6 });
	perms_chunks[2].emplace_back(vector<int>() = { 3, 3 });
	perms_chunks[3].emplace_back(vector<int>() = { 2, 2, 2 });

	perms_gaps[1].emplace_back(vector<int>() = {});
	perms_gaps[2].emplace_back(vector<int>() = { 3 });
	perms_gaps[3].emplace_back(vector<int>() = { 3, 3 });


	for (int i = 1; i <= 3; ++i) {
		move_rules[0].emplace_back(make_pair(perms_chunks[i], perms_gaps[i]));
	}
}
int comp_cnt;

void dfs(int pos) {
	for (auto it : tree_edges[pos]) {
		dfs(it);
	}
	ckeck_force_stop();

	vector<int> act_nodes, xx;
	set <int> act_node_set;
	for (auto node : bkt_comps[pos]) {
		if (compressed[node].empty()) {
			int x = node;
			while (x != prt[x]) {
				x = prt[x];
			}
			act_node_set.insert(x);
			continue;
		}
		act_node_set.insert(node);
		//act_nodes.emplace_back(node);
		xx.emplace_back(node);
	}
	for (auto it : act_node_set) {
		act_nodes.emplace_back(it);
	}
	cnt = 0;

	solve_brance_and_bound(act_nodes);

	update_scores(act_nodes);

	vector<int> to_be_deleted;
	for (int i = 1; i < act_nodes.size(); ++i) {
		for (auto it : compressed[act_nodes[i]]) {
			compressed[act_nodes[0]].emplace_back(it);
		}
		prt[act_nodes[i]] = act_nodes[0];
		compressed[act_nodes[i]].clear();
		to_be_deleted.emplace_back(act_nodes[i]);
	}
	delete_nodes(to_be_deleted);
}

void clear_data() {
	cost_overall = 0;
	for (int i = 0; i <= n; ++i) {
		mobile_edges[i] = vector<int>();
	}
	for (int i = 0; i <= m; ++i) {
		fixed_edges[i] = vector<int>();
	}
	input = vector<pair<int, int>>();
	fixed_set = set <int>(), mobile_set = set <int>();
	fixed_vec = vector<int>(), mobile_vec = vector<int>(), fixed_nodes = vector<int>(), mobile_nodes = vector<int>();
	fixed_pos = map <int, int>(), mobile_pos = map <int, int>(), real_mobile_nodes = map <int, int>();
	fixed_nodes_range = vector<pair<int, int>>();
	mobile_isolated = vector<int>();
	bb_comps = vector<vector<int>>();
	fixed_interval_starter = vector<vector<int>>();
	compressed = vector<vector<int>>();
	mobile_nodes_lists = vector< pair <vector<int>, int> >();
	mobile_ends = vector <pair< pair <int, int>, int >>();
	bkt_comps = vector< unordered_set <int> >();
	tree_edges = vector<set <int>>();
	scor = vector<vector<long long>>();
	move_rules[0] = vector < pair < vector<vector<int>>, vector<vector<int>> > >();
	move_rules[1] = vector < pair < vector<vector<int>>, vector<vector<int>> > >();
	for (int i = 0; i < 10; ++i) {
		perms_chunks[i] = vector<vector<int>>();
		perms_gaps[i] = vector<vector<int>>();
	}
	must_before = vector<vector<int>>();
	prt = vector<int>();
}


bool cmpEnds(pair <pair <int, int>, int> i, pair <pair<int, int>, int> j) {
	if (i.first.first == j.first.first) {
		return i.first.second > j.first.second;
	}
	return i.first.first < j.first.first;
}

void update_scores(vector<int>& perm) {
	set <int> act;
	for (auto it : perm) {
		act.insert(it);
	}

	for (int i = 0; i < perm.size(); ++i) {
		for (int j = i + 1; j < perm.size(); ++j) {
			cost_overall += scor[perm[i]][perm[j]];
		}
	}

	for (auto node : mobile_nodes) {
		char is_outside = 1;
		long long from_ = 0, to_ = 0;
		for (auto it : perm) {
			if (node == it) {
				is_outside = 0;
				break;
			}
			from_ += scor[node][it];
			to_ += scor[it][node];
		}
		if (!is_outside) {
			continue;
		}
		scor[node][perm[0]] = from_;
		scor[perm[0]][node] = to_;
	}
}

long long get_brut_score(vector<int>& perm, int st, int dr) {
	long long ret = 0;
	for (int i = st; i <= dr; ++i) {
		for (int j = i + 1; j <= dr; ++j) {
			ret += scor[perm[i]][perm[j]];
		}
	}
	return ret;
}

long long cntCross(vector<int>& a, vector<int>& b)
{
	int p = -1;
	long long ans = 0;

	for (int it : b)
	{
		while (p + 1 < (int)a.size() && a[p + 1] <= it)
			p++;

		ans += (int)a.size() - p - 1;
	}

	return ans;
}

void get_score_table() {
	for (int i = 0; i < mobile_nodes.size(); ++i) {
		for (int j = i + 1; j < mobile_nodes.size(); ++j) {
			scor[mobile_nodes[i]][mobile_nodes[j]] = cntCross(mobile_edges[mobile_nodes[i]], mobile_edges[mobile_nodes[j]]);
			scor[mobile_nodes[j]][mobile_nodes[i]] = cntCross(mobile_edges[mobile_nodes[j]], mobile_edges[mobile_nodes[i]]);
		}
	}
	//scor2 = scor;
}

bool cmpList(pair <vector<int>, int >& a, pair <vector<int>, int>& b) {
	if (a.first.size() == b.first.size()) {
		for (int i = 0; i < a.first.size(); ++i) {
			if (a.first[i] == b.first[i]) {
				continue;
			}
			return a.first[i] < b.first[i];
		}
		return a.second < b.second;
	}
	return a.first.size() < b.first.size();
}

void eliminate_mobile_duplicates() {
	for (auto i : mobile_nodes) {
		mobile_nodes_lists.emplace_back(make_pair(mobile_edges[i], i));
	}
	std::sort(mobile_nodes_lists.begin(), mobile_nodes_lists.end(), cmpList);
	compressed.resize(mobile_nodes.size() + 1, vector<int>());
	for (int i = 0; i < mobile_nodes_lists.size(); ++i) {
		vector<int> act;
		int j = i;
		for (; j < mobile_nodes_lists.size(); ++j) {
			if (!egal(mobile_nodes_lists[i].first, mobile_nodes_lists[j].first)) {
				break;
			}
			act.emplace_back(mobile_nodes_lists[j].second);
		}
		compressed[mobile_nodes_lists[i].second] = act;
		if (j != i + 1) {
			for (int l = 0; l < mobile_nodes_lists.size(); ++l) {
				if (i <= l && l < j) {
					continue;
				}
				scor[mobile_nodes_lists[l].second][mobile_nodes_lists[i].second] *= 1ll * (j - i);
				scor[mobile_nodes_lists[i].second][mobile_nodes_lists[l].second] *= 1ll * (j - i);
			}
			cost_overall += scor[mobile_nodes_lists[i].second][mobile_nodes_lists[i + 1].second] * (1ll * (j - i)) * (1ll * (j - i - 1)) / 2;
			//cost_overall += cntCross(mobile_nodes_lists[i].first, mobile_nodes_lists[i].first) * (1ll * (j - i)) * (1ll * (j - i - 1)) / 2;
		}
		i = j - 1;
	}
	vector<int> to_be_deleted;
	for (auto it : mobile_nodes) {
		if (compressed[it].empty()) {
			to_be_deleted.emplace_back(it);
		}
	}
	delete_nodes(to_be_deleted);
}


void delete_nodes(vector<int>& v) {

	set <int> s;
	vector<int> new_vec;
	for (auto it : v) {
		s.insert(it);
		mobile_edges[it].clear();
	}
	for (auto it : mobile_nodes) {
		if (!s.count(it)) {
			new_vec.emplace_back(it);
		}
	}
	mobile_nodes = new_vec;
	for (auto it : fixed_nodes) {
		vector<int> updated_version;
		for (auto i : fixed_edges[it]) {
			if (!s.count(i)) {
				updated_version.emplace_back(i);
			}
		}
		fixed_edges[it] = updated_version;
	}
}


bool egal(vector<int>& a, vector<int>& b) {
	if (a.size() != b.size()) {
		return 0;
	}
	for (int i = 0; i < a.size(); ++i) {
		if (a[i] != b[i]) {
			return 0;
		}
	}
	return 1;
}

bool cmpSimpleList(vector<int>& a, vector<int>& b) {
	if (a.size() == b.size()) {
		for (int i = 0; i < a.size(); ++i) {
			if (a[i] == b[i]) {
				continue;
			}
			return a[i] < b[i];
		}
	}
	return a.size() < b.size();
}

void fun(int fix_node) {
	ret = vector<pair<pair<int, int>, vector<int>> >();
	vector< pair<pair <int, int>, int> > nodes;
	vector<int> one_grade;
	int flag_last_saved = 0;
	for (auto node : fixed_interval_starter[fix_node]) {
		if (mobile_edges[node].size() == 1) {
			one_grade.emplace_back(node);
			continue;
		}
		if (mobile_edges[node].size() == 2) {
			nodes.emplace_back(make_pair(make_pair(mobile_edges[node][1], 2), node));
			continue;
		}
		nodes.emplace_back(make_pair(make_pair(mobile_edges[node][1], 3), node));
		nodes.emplace_back(make_pair(make_pair(mobile_edges[node].back(), 1), node));
	}

	if (one_grade.size()) {
		ret.emplace_back(make_pair(make_pair(fix_node, 1000000000), one_grade));
		flag_last_saved = 1;
	}
	std::sort(nodes.begin(), nodes.end());
	set <int> nodes_used, nodes_current;
	for (auto it : nodes) {
		if (it.first.second == 1) {
			nodes_current.erase(it.second);
			if (nodes_current.empty()) {
				vector<int> act = one_grade;
				for (auto it : nodes_used) {
					act.emplace_back(it);
				}
				ret.emplace_back(make_pair(make_pair(it.first.first, 1000000000), act));
				flag_last_saved = 1;
			}
		}
		if (it.first.second == 2) {
			if (flag_last_saved) {
				if (!ret.empty()) {
					ret[ret.size() - 1].first.second = it.first.first;
				}
				flag_last_saved = 0;
			}
			nodes_used.insert(it.second);
			if (nodes_current.empty()) {
				vector<int> act = one_grade;
				for (auto it : nodes_used) {
					act.emplace_back(it);
				}
				ret.emplace_back(make_pair(make_pair(it.first.first, 1000000000), act));
				flag_last_saved = 1;
			}
		}
		if (it.first.second == 3) {
			if (flag_last_saved) {
				if (!ret.empty()) {
					ret[ret.size() - 1].first.second = it.first.first;
				}
				flag_last_saved = 0;
			}
			nodes_current.insert(it.second);
			nodes_used.insert(it.second);
		}
	}
}


bool calc_dp_andrei(int start_pos, vector<int>szChunks, vector<int> szGaps, vector<int>& s) {
	vector <int> vals;
	vector <int> gaps;

	int pred_gaps = 0, pred_chunks = 0, total_chunks_sz = 0;
	for (int i = 0; i < szChunks.size(); ++i) {
		for (int j = 0; j < szChunks[i]; ++j) {
			vals.emplace_back(start_pos + pred_gaps + pred_chunks + j);
		}
		pred_chunks += szChunks[i];

		if (i + 1 != szChunks.size()) {
			for (int j = 0; j < szGaps[i]; ++j) {
				int pos = start_pos + pred_gaps + pred_chunks + j;
				gaps.emplace_back(pos);
			}
		}
		if (i + 1 != szChunks.size()) {
			pred_gaps += szGaps[i];
		}
	}
	total_chunks_sz = pred_chunks;


	vector<vector<int>> bitmask_cost(total_chunks_sz + 2, vector<int>(total_chunks_sz + 2, 0));

	for (int i = 0; i < vals.size(); ++i) {
		int element = vals[i];
		for (int j = 0; j < vals.size(); ++j) {
			int pos = vals[j];
			for (int l = 0; l < gaps.size(); ++l) {
				int gap = gaps[l];
				if (gap < pos) {
					bitmask_cost[i][j] += scor[s[gap]][s[element]];
				}
				else {
					bitmask_cost[i][j] += scor[s[element]][s[gap]];
				}
			}
		}
	}

	int lim = (1 << total_chunks_sz) - 1;
	dp_a[0] = 0;

	for (int mask = 1; mask <= lim; ++mask) {
		dp_a[mask] = oo;
		for (int i = 0; i < total_chunks_sz; ++i) {
			if (!((1 << i) & mask)) {
				continue;
			}
			int cost = bitmask_cost[i][custom_pop_count(mask) - 1];
			for (int j = 0; j < total_chunks_sz; ++j) {
				if (i == j) {
					continue;
				}
				if (!((1 << j) & mask)) {
					continue;
				}
				cost += scor[s[vals[j]]][s[vals[i]]];
			}
			if (cost + dp_a[mask - (1 << i)] < dp_a[mask]) {
				dp_a[mask] = cost + dp_a[mask - (1 << i)];
				last_a[mask] = i;
			}
		}
	}
	long long maxi = dp_a[lim];
	vector<int> sol, upd(vals.size(), 0);
	while (lim) {
		sol.emplace_back(last_a[lim]);
		lim -= (1 << last_a[lim]);
	}


	for (int i = ((int)sol.size()) - 1; i >= 0; --i) {
		upd[sol.size() - 1 - i] = s[vals[sol[i]]];

	}
	int sw = 0;
	for (int i = 0; i < upd.size(); ++i) {
		if (s[vals[i]] != upd[i]) {
			sw = 1;
		}
		s[vals[i]] = upd[i];
	}
	return sw;
}

void try_optimize(vector<int>& s, int st, int dr) {
	long long last_sc = get_brut_score(s, st, dr), sw = 1;
	while (sw) {
		sw = 0;
		apply_just_dp(st, dr, s, 0);
		brut_reord(s, st, dr, 1000);
		long long curr_sc = get_brut_score(s, st, dr);
		if (curr_sc != last_sc) {
			last_sc = curr_sc;
			sw = 1;
		}
	}
}


void apply_just_dp(int st, int dr, vector<int>& s, int search_type) {

	vector<pair <int, int >> coef;
	vector<int> new_seq_3;
	vector<int> new_seq;
	long long tot_cost = 0;
	for (int i = st; i <= dr; ++i) {
		new_seq_3.emplace_back(s[i]);
	}


	for (int reps = 1; reps <= 1; ++reps) {
		for (int i = 0; i < new_seq_3.size(); ++i) {
			for (auto move : move_rules[search_type]) {
				for (auto chunk : move.first) {
					int spaces = 0;
					for (auto it : chunk) {
						spaces += it;
					}
					for (auto gap : move.second) {
						for (auto it : gap) {
							spaces += it;
						}
						if (i + spaces < new_seq_3.size()) {
							calc_dp_andrei(i, chunk, gap, new_seq_3);
						}
					}
				}
			}
		}
	}

	long long cost3 = 0;
	for (int i = st; i <= dr; ++i) {
		for (int j = i + 1; j <= dr; ++j) {
			cost3 += scor[s[i]][s[j]];

		}
	}

	long long tot2 = 0;
	for (int i = 0; i < new_seq_3.size(); ++i) {
		for (int j = i + 1; j < new_seq_3.size(); ++j) {
			tot2 += scor[new_seq_3[i]][new_seq_3[j]];
		}
	}

	long long sw = 0, diff = 0, ret = 0;
	if (cost3 > tot2) {
		sw = 1;
		ret = max(0ll, cost3 - tot2);
		for (int i = st; i <= dr; ++i) {
			if (new_seq_3[i - st] != s[i]) {
				diff = 1;
			}
			s[i] = new_seq_3[i - st];
		}
	}
}


void brut_reord(vector<int>& v, int st, int dr, int maxDist) {
	for (int i = st; i <= dr; ++i) {
		long long castig = 0, best = 0;
		int best_pos = -1;
		for (int j = i - 1; j >= st; --j) {
			if (i - j > maxDist) {
				break;
			}
			castig -= scor[v[i]][v[j]] - scor[v[j]][v[i]];
			if (castig > best) {
				best = castig;
				best_pos = j;
			}
		}
		castig = 0;
		for (int j = i + 1; j <= dr; ++j) {
			if (j - i > maxDist) {
				break;
			}
			castig -= scor[v[j]][v[i]] - scor[v[i]][v[j]];
			if (castig > best) {
				best = castig;
				best_pos = j;
			}
		}
		if (best_pos != -1) {
			if (best_pos > i) {
				int val = v[i];
				for (int j = i; j < best_pos; ++j) {
					v[j] = v[j + 1];
				}
				v[best_pos] = val;
			}
			else
			{
				int val = v[i];
				for (int j = i; j > best_pos; --j) {
					v[j] = v[j - 1];
				}
				v[best_pos] = val;
			}
		}
	}
}

int custom_pop_count(int x) {
	int sum = 0;
	for (int i = 0; i < 30; ++i) {
		if ((1 << i) & x) {
			sum++;
		}
	}
	return sum;
}

bool compAvg(int x, int y)
{
	return (avg[x] < avg[y] || (avg[x] == avg[y] && x <= y));
}

void run_local_search(vector<int>& s, int st, int dr) {

	vector<int> act[3];
	long long best_score = get_brut_score(s, st, dr);
	for (int i = st; i <= dr; ++i) {
		for (int l = 0; l < 3; ++l) {
			act[l].emplace_back(s[i]);
		}
	}
	reverse(act[0].begin(), act[0].end());
	sort(act[1].begin(), act[1].end(), compAvg);
	reverse(act[2].begin(), act[2].end());
	sort(act[2].begin(), act[2].end(), compAvg);
	for (int i = 0; i < 3; ++i) {
		try_optimize(act[i], 0, ((int)act[i].size()) - 1);
		long long act_score = get_brut_score(act[i], 0, ((int)act[i].size()) - 1);
		if (act_score < best_score) {
			best_score = act_score;
			for (auto l = st; l <= dr; ++l) {
				s[l] = act[i][l - st];
			}
		}
		act[i].clear();
	}
}


pair <int, int> get_hash(vector<int>& val) {
	vector<int> sequence;
	for (auto it : val) {
		if (isUsed[it]) {
			sequence.emplace_back(it);
		}
	}
	pair <int, int> ret = make_pair(0, 0);
	sort(sequence.begin(), sequence.end());
	for (int i = 0; i < sequence.size(); ++i) {
		ret.first = 1ll * (1ll * ret.first + 1ll * sequence[i] * hashes[i].first) % MOD1;
		ret.second = 1ll * (1ll * ret.second + 1ll * sequence[i] * hashes[i].second) % MOD2;
	}
	return ret;
}

void solve_brance_and_bound(vector <int>& s) {
	run_heuristic(s);
	if (s.size() > 160) {
		for (int i = 0; i < s.size(); i++) {
			dp_pref[i] = 1e18;
			inv[s[i]] = i;
			ansFinal[i] = s[i];
		}
		bestKnown = get_brut_score(s, 0, s.size() - 1);
		long long lower_bound;
		long long upper_bound;
		preprocess_branch_and_bound(s, lower_bound, upper_bound);
		run_branch_and_bound(0, 0, lower_bound, lower_bound, upper_bound, s);
		for (auto it : s) {
			must_before[it] = vector<int>();
			isUsed[it] = 0;
		}
		hash_to_index.clear();
		for (int i = 0; i < s.size(); ++i) {
			s[i] = ansFinal[i];
		}
	}
	else {
		vector<int> result, s2;
		vector<vector<int>> small_score(s.size(), vector<int>(s.size(), 0));
		for (int i = 0; i < s.size(); ++i) {
			for (int j = 0; j < s.size(); ++j) {
				small_score[i][j] = scor[s[i]][s[j]];
				small_score[j][i] = scor[s[j]][s[i]];
			}
		}
		preprocess_ilp(s);
		for (auto it : s) {
			for (auto it2 : must_before[it]) {
				pairs.insert(make_pair(it2, it));
			}
		}
		result = run_ilp(s.size(), small_score);
		for (int i = 0; i < result.size(); ++i) {
			s2.emplace_back(s[result[i]]);
		}
		s = s2;
		pairs.clear();
		for (int it = 0; it < s.size(); ++it) {
			must_before[it] = vector<int>();
		}
	}
}

long long get_minimal_lowerbound(vector<int>& act, int st, int dr) {
	long long ret = 0;
	for (int i = st; i <= dr; ++i) {
		for (int j = i + 1; j <= dr; ++j) {
			ret += min(scor[act[i]][act[j]], scor[act[j]][act[i]]);
		}
	}
	return ret;
}

long long get_extra_segment(vector<int>& act) {
	long long before = get_minimal_lowerbound(act, 0, act.size() - 1);
	calc_dp_andrei(0, vector<int>() = { (int)act.size() }, vector<int>(), act);
	long long after = get_brut_score(act, 0, act.size() - 1);
	return  after - before;
}

long long get_extra_lower_bound(vector<int>& val, vector<int>& lb) {
	vector<int> nodes;
	vector<pair<pair<int, int>, long long>> temp;

	for (auto it : val) {
		if (!isUsed[it]) {
			nodes.emplace_back(it);
		}
	}
	if (nodes.size() < 6) {
		long long ret = get_extra_segment(nodes);
		lb = nodes;
		return ret;
	}
	sort(nodes.begin(), nodes.end(), [](int i, int j) {return inv[i] < inv[j]; });
	lb = nodes;
	int tot = 0, bun = 0;
	for (int i = 0; i < nodes.size(); ++i) {
		for (int j = i + 2; j < min(i + 40, (int)nodes.size()); ++j) {
			if (scor[nodes[i]][nodes[j]] > scor[nodes[j]][nodes[i]]) {
				long long contrib_ = 0;
				for (int l = i + 1; l < j; ++l) {
					long long good = 1, left_ = 0, right_ = 0;
					if (scor[nodes[i]][nodes[l]] >= scor[nodes[l]][nodes[i]]) {
						good = 0;
					}
					else {
						left_ = scor[nodes[l]][nodes[i]] - scor[nodes[i]][nodes[l]];
					}
					if (scor[nodes[l]][nodes[j]] >= scor[nodes[j]][nodes[l]]) {
						good = 0;
					}
					else {
						right_ = scor[nodes[j]][nodes[l]] - scor[nodes[l]][nodes[j]];
					}
					if (good) {
						contrib_ += min(left_, right_);
					}
				}
				if (contrib_ >= scor[nodes[i]][nodes[j]] - scor[nodes[j]][nodes[i]]) {
					temp.emplace_back(make_pair(make_pair(j + 1, i + 1), scor[nodes[i]][nodes[j]] - scor[nodes[j]][nodes[i]]));
				}
			}
		}
	}
	sort(temp.begin(), temp.end(), [](pair<pair<int, int>, long long>i, pair<pair<int, int>, long long> j) {return i.first.first - i.first.second < j.first.first - j.first.second; });

	for (int i = 0; i < temp.size(); ++i) {
		dp_lb_in[i] = 0;
		for (int j = 0; j < i; ++j) {
			if (temp[i].first.first > temp[j].first.first && temp[i].first.second < temp[j].first.second) {
				dp_lb_in[i] = max(dp_lb_in[i], temp[j].second);
			}
		}
	}

	sort(temp.begin(), temp.end());

	dp_lb[0] = 0;
	int p = 0;

	for (int i = 1; i <= nodes.size(); ++i) {
		dp_lb[i] = dp_lb[i - 1];
		while (p < temp.size() && temp[p].first.first == i) {
			dp_lb[temp[p].first.first] = max(dp_lb[temp[p].first.first], dp_lb[temp[p].first.second] + temp[p].second + dp_lb_in[p]);
			++p;
		}
	}
	return dp_lb[nodes.size()];
}

bool check_hash(vector<int>& val, long long cost) {
	pair <int, int> currHash = get_hash(val);
	if (!hash_to_index.count(currHash)) {
		if (hash_to_index.size() == 2000000) {
			return true;
		}
		bkt_hashes[hash_to_index.size()] = cost;
		hash_to_index[currHash] = hash_to_index.size();
		return true;
	}
	else {
		if (bkt_hashes[hash_to_index[currHash]] > cost) {
			bkt_hashes[hash_to_index[currHash]] = cost;
			return true;
		}
		return false;
	}
}
