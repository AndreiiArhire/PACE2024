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
using namespace std;
#define ever (;;)
#define SECONDS 280
#define NMAX 2000000


int na, n, m;

std::chrono::time_point<std::chrono::high_resolution_clock> beginTime;

vector<int> mobile_edges[NMAX];
vector<int> fixed_edges[NMAX];
vector<pair<int, int>> input;
set <int> fixed_set, mobile_set;
vector<int> fixed_vec, mobile_vec, fixed_nodes, mobile_nodes;
map <int, int> fixed_pos, mobile_pos;
vector<int> mobile_isolated;
vector<vector<int>> bb_comps;
vector< pair <vector<int>, int> > mobile_nodes_lists;
vector <pair< pair <int, int>, int >> mobile_ends;

vector<int> freq;
int bb_root;
int test;
int curComp;
long long cost_overall, bestKnown;

const int oo = ((int)1e9);
int last_a[NMAX];
long long dp_a[NMAX];

std::mt19937 initialRng(123);


struct component {
	vector<int> nodes, freq, original_nodes, avg, best_heuristic, compressed_ind;
	vector<vector<long long>> scor;
	vector<vector<int>> compressed;
};

vector<component>components;

vector<vector<int>>perms_chunks[10], perms_gaps[10];
vector < pair < vector<vector<int>>, vector<vector<int>> > > move_rules[2];

long long cntCross(vector<int>& a, vector<int>& b);

void get_score_table(int comp);

long long get_brut_score(vector<int>& perm, int st, int dr);

bool cmpList(pair <vector<int>, int >& a, pair <vector<int>, int>& b);

bool egal(vector<int>& a, vector<int>& b);

void delete_nodes(vector<int>& v, int& comp);

void eliminate_mobile_duplicates(int comp);

void clear_data();

bool cmpEnds(pair <pair <int, int>, int> i, pair <pair<int, int>, int> j);

void preprocess();

bool compAvg(int x, int y);

int custom_pop_count(int x);

void brut_reord(vector<int>& v, int st, int dr, int maxDist);

bool calc_dp_andrei(int start_pos, vector<int>szChunks, vector<int> szGaps, vector<int>& s);

void apply_just_dp(int st, int dr, vector<int>& s, int search_type = 0);

void try_optimize(vector<int>& s, int st, int dr);

void run_local_search();

void print_result();

double check_time();

void reord_sub_seq(vector<int>& s, int st, int dr);

void get_initial_heuristic();

void try_optimize_big_test(int sz);



int main() {
	beginTime = std::chrono::high_resolution_clock::now();

	for (int t = 2; t <= 2; ++t) {
		test = t;
		string filename = "tiny//" + to_string(t) + ".gr";
		ios_base::sync_with_stdio(false);
		cin.tie(0);
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

		preprocess();

		int sz = 0;
		for (auto it : components) {
			sz += it.nodes.size();
		}

		for (curComp = 0; curComp < components.size(); ++curComp) {
			get_initial_heuristic();
		}

		run_local_search();

	}
	return 0;
}


void try_optimize_big_test(int sz) {
	vector<vector<long long>> next_scor;
	for (int i = 0; i + sz < components[curComp].best_heuristic.size(); ++i) {
		check_time();
		vector<int> pos;
		for (int l = 0; l < sz; ++l) {
			pos.emplace_back(l);
		}
		components[curComp].scor = vector<vector<long long>>(sz, vector<long long>(sz, 0));
		if (next_scor.empty()) {
			for (int l = 0; l < sz; ++l) {
				int x = components[curComp].original_nodes[components[curComp].nodes[components[curComp].best_heuristic[i + l]]];
				for (int p = l + 1; p < sz; ++p) {
					int y = components[curComp].original_nodes[components[curComp].nodes[components[curComp].best_heuristic[i + p]]];
					components[curComp].scor[l][p] = cntCross(mobile_edges[x], mobile_edges[y]);
					components[curComp].scor[p][l] = cntCross(mobile_edges[y], mobile_edges[x]);
				}
			}
		}
		else {
			components[curComp].scor = next_scor;
			int y = components[curComp].original_nodes[components[curComp].nodes[components[curComp].best_heuristic[i + sz - 1]]];
			for (int l = 0; l + 1 < sz; ++l) {
				int x = components[curComp].original_nodes[components[curComp].nodes[components[curComp].best_heuristic[i + l]]];
				components[curComp].scor[l][sz - 1] = cntCross(mobile_edges[x], mobile_edges[y]);
				components[curComp].scor[sz - 1][l] = cntCross(mobile_edges[y], mobile_edges[x]);
			}
		}

		calc_dp_andrei(0, vector<int>() = { sz }, vector<int>(), pos);

		next_scor = vector<vector<long long>>(sz, vector<long long>(sz, 0));
		for (int l = 1; l < sz; ++l) {
			for (int p = l + 1; p < sz; ++p) {
				next_scor[l - 1][p - 1] = components[curComp].scor[pos[l]][pos[p]];
				next_scor[p - 1][l - 1] = components[curComp].scor[pos[p]][pos[l]];
			}
		}

		for (int l = 0; l < pos.size(); ++l) {
			pos[l] = components[curComp].best_heuristic[i + pos[l]];
		}
		for (int l = 0; l < pos.size(); ++l) {
			components[curComp].best_heuristic[i + l] = pos[l];
		}
		components[curComp].scor = vector<vector<long long>>();
	}
}


vector<int> reord_sub_seq_act[4];

void reord_sub_seq(vector<int>& s, int st, int dr) {
	check_time();
	long long best_score = get_brut_score(s, st, dr);
	for (int i = st; i <= dr; ++i) {
		for (int l = 0; l < 4; ++l) {
			reord_sub_seq_act[l].emplace_back(s[i]);
		}
	}
	std::reverse(reord_sub_seq_act[0].begin(), reord_sub_seq_act[0].end());
	std::sort(reord_sub_seq_act[1].begin(), reord_sub_seq_act[1].end(), compAvg);
	std::reverse(reord_sub_seq_act[2].begin(), reord_sub_seq_act[2].end());
	std::sort(reord_sub_seq_act[2].begin(), reord_sub_seq_act[2].end(), compAvg);
	std::mt19937 rng(initialRng());
	std::shuffle(reord_sub_seq_act[3].begin(), reord_sub_seq_act[3].end(), rng);


	check_time();
	for (int i = 0; i < 4; ++i) {
		check_time();
		try_optimize(reord_sub_seq_act[i], 0, ((int)reord_sub_seq_act[i].size()) - 1);
		long long act_score = get_brut_score(reord_sub_seq_act[i], 0, ((int)reord_sub_seq_act[i].size()) - 1);
		if (act_score < best_score) {
			best_score = act_score;
			for (auto l = st; l <= dr; ++l) {
				s[l] = reord_sub_seq_act[i][l - st];
			}
		}
		reord_sub_seq_act[i].clear();
	}
}




void get_initial_heuristic() {
	for (int i = 0; i < components[curComp].nodes.size(); ++i) {
		components[curComp].best_heuristic.emplace_back(i);
	}

	sort(components[curComp].best_heuristic.begin(), components[curComp].best_heuristic.end(), compAvg);

	if (!components[curComp].scor.empty()) {
		try_optimize(components[curComp].best_heuristic, 0, components[curComp].best_heuristic.size() - 1);
	}
	else {
		try_optimize_big_test(9);
	}
}





void print_result() {

	for (auto it : mobile_isolated) {
		std::cout << it + na << '\n';
	}
	for (curComp = 0; curComp < components.size(); ++curComp) {
		int p = 0;
		for (int i = 0; i < components[curComp].best_heuristic.size(); ++i) {
			int node = components[curComp].nodes[components[curComp].best_heuristic[i]];
			std::cout << mobile_vec[components[curComp].original_nodes[node] - 1] + na << '\n';
			int ind = components[curComp].compressed_ind[node];
			if (ind == -1) {
				continue;
			}
			for (auto it : components[curComp].compressed[ind]) {
				std::cout << mobile_vec[components[curComp].original_nodes[it] - 1] + na << '\n';
			}
		}
	}
}

void get_isolated_nodes() {
	for (int i = 1; i <= n; ++i) {
		if (!mobile_set.count(i)) {
			mobile_isolated.emplace_back(i);
		}
	}
}

vector <int> act_comp;
void get_components(vector< vector<int>>& comps) {

	for (auto it : mobile_nodes) {
		mobile_ends.emplace_back(make_pair(make_pair(mobile_edges[it][0], mobile_edges[it].back()), it));
	}
	sort(mobile_ends.begin(), mobile_ends.end(), cmpEnds);

	int last_right_end = -1;
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
			comps.emplace_back(act_comp);
			last_right_end = i.first.second;
			act_comp = vector<int>() = { i.second };
		}
	}
	comps.emplace_back(act_comp);
	act_comp.clear();
}

void get_average(int comp) {
	components[comp].avg.resize(components[comp].nodes.size(), 0);

	for (int i = 0; i < components[comp].nodes.size(); ++i) {
		int node = components[comp].nodes[i];
		for (int it : mobile_edges[components[comp].original_nodes[node]])
			components[comp].avg[i] += it;
		components[comp].avg[i] /= (long double)mobile_edges[components[comp].original_nodes[node]].size();
	}

}

void add_component(vector<int>& s) {
	int comp = components.size();
	components.emplace_back(component());
	components[comp].original_nodes = s;
	sort(components[comp].original_nodes.begin(), components[comp].original_nodes.end());
	for (int i = 0; i < components[comp].original_nodes.size(); ++i) {
		components[comp].nodes.emplace_back(i);
	}
	components[comp].freq.resize(s.size(), 0);
	components[comp].compressed_ind.resize(s.size(), -1);
	eliminate_mobile_duplicates(comp);

	if (components[comp].nodes.size() < 20000) {
		get_score_table(comp);
	}

	get_average(comp);

}

void preprocess() {

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
	std::sort(fixed_nodes.begin(), fixed_nodes.end());
	std::sort(mobile_nodes.begin(), mobile_nodes.end());

	for (auto edge : input) {
		int fixed_node = fixed_pos[edge.first];
		int mobile_node = mobile_pos[edge.second];
		fixed_edges[fixed_node].emplace_back(mobile_node);
		mobile_edges[mobile_node].emplace_back(fixed_node);
	}

	for (auto node : mobile_nodes) {
		std::sort(mobile_edges[node].begin(), mobile_edges[node].end());
	}
	for (auto node : fixed_nodes) {
		std::sort(fixed_edges[node].begin(), fixed_edges[node].end());
	}

	get_isolated_nodes();

	get_components(bb_comps);
	int cnt = 0;
	for (auto& it : bb_comps) {
		add_component(it);
	}


	for (auto it : components) {
		int left_ = 1e9;
		int right_ = -1;
		for (auto it2 : it.nodes) {
			left_ = min(left_, mobile_edges[it.original_nodes[it2]][0]);
			right_ = max(right_, mobile_edges[it.original_nodes[it2]].back());
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


void clear_data() {
	cost_overall = 0;
	curComp = 0;
	for (int i = 0; i <= n; ++i) {
		mobile_edges[i] = vector<int>();
	}
	for (int i = 0; i <= m; ++i) {
		fixed_edges[i] = vector<int>();
	}
	input = vector<pair<int, int>>();
	fixed_set = set <int>(), mobile_set = set <int>();
	fixed_vec = vector<int>(), mobile_vec = vector<int>(), fixed_nodes = vector<int>(), mobile_nodes = vector<int>();
	fixed_pos = map <int, int>(), mobile_pos = map <int, int>();
	mobile_isolated = vector<int>();
	bb_comps = vector<vector<int>>();
	mobile_nodes_lists = vector< pair <vector<int>, int> >();
	mobile_ends = vector <pair< pair <int, int>, int >>();
	move_rules[0] = vector < pair < vector<vector<int>>, vector<vector<int>> > >();
	move_rules[1] = vector < pair < vector<vector<int>>, vector<vector<int>> > >();
	for (int i = 0; i < 10; ++i) {
		perms_chunks[i] = vector<vector<int>>();
		perms_gaps[i] = vector<vector<int>>();
	}
	components = vector<component>();
}

bool cmpEnds(pair <pair <int, int>, int> i, pair <pair<int, int>, int> j) {
	if (i.first.first == j.first.first) {
		return i.first.second > j.first.second;
	}
	return i.first.first < j.first.first;
}


long long get_brut_score(vector<int>& perm, int st, int dr) {
	check_time();
	long long ret = 0;
	for (int i = st; i <= dr; ++i) {
		for (int j = i + 1; j <= dr; ++j) {
			ret += components[curComp].scor[perm[i]][perm[j]];
		}
	}
	return ret;
}

long long cntCross(vector<int>& a, vector<int>& b)
{
	check_time();
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

void get_score_table(int comp) {
	components[comp].scor.resize(components[comp].nodes.size(), vector<long long>(components[comp].nodes.size(), 0));
	for (int i = 0; i < components[comp].nodes.size(); ++i) {
		for (int j = i + 1; j < components[comp].nodes.size(); ++j) {
			int x = components[comp].original_nodes[components[comp].nodes[i]];
			int y = components[comp].original_nodes[components[comp].nodes[j]];
			long long multiplication_factor = components[comp].freq[components[comp].nodes[j]] * components[comp].freq[components[comp].nodes[i]];
			components[comp].scor[i][j] = cntCross(mobile_edges[x], mobile_edges[y]) * multiplication_factor;
			components[comp].scor[j][i] = cntCross(mobile_edges[y], mobile_edges[x]) * multiplication_factor;
		}
	}
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

void eliminate_mobile_duplicates(int comp) {
	for (auto i : components[comp].nodes) {
		mobile_nodes_lists.emplace_back(make_pair(mobile_edges[components[comp].original_nodes[i]], i));
	}

	std::sort(mobile_nodes_lists.begin(), mobile_nodes_lists.end(), cmpList);

	for (int i = 0; i < mobile_nodes_lists.size(); ++i) {
		vector<int> act;
		int j = i + 1;
		for (; j < mobile_nodes_lists.size(); ++j) {
			if (!egal(mobile_nodes_lists[i].first, mobile_nodes_lists[j].first)) {
				break;
			}
			act.emplace_back(mobile_nodes_lists[j].second);
		}
		components[comp].compressed_ind[mobile_nodes_lists[i].second] = components[comp].compressed.size();
		components[comp].compressed.emplace_back(act);
		components[comp].freq[mobile_nodes_lists[i].second] = 1 + act.size();
		i = j - 1;
	}


	vector<int> to_be_deleted;
	for (auto it : components[comp].nodes) {
		if (!components[comp].freq[it]) {
			to_be_deleted.emplace_back(it);
		}
	}

	delete_nodes(to_be_deleted, comp);

	mobile_nodes_lists = vector< pair <vector<int>, int> >();

}

set <int> delete_nodes_set;
vector<int> delete_nodes_vec;
void delete_nodes(vector<int>& v, int& comp) {

	for (auto it : v) {
		delete_nodes_set.insert(components[comp].original_nodes[it]);
	}
	for (auto it : components[comp].nodes) {
		if (!delete_nodes_set.count(components[comp].original_nodes[it])) {
			delete_nodes_vec.emplace_back(it);
		}
	}
	components[comp].nodes = delete_nodes_vec;
	delete_nodes_set = set <int>();
	delete_nodes_vec = vector<int>();
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

bool calc_dp_andrei(int start_pos, vector<int>szChunks, vector<int> szGaps, vector<int>& s) {
	check_time();
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
					bitmask_cost[i][j] += components[curComp].scor[s[gap]][s[element]];
				}
				else {
					bitmask_cost[i][j] += components[curComp].scor[s[element]][s[gap]];
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
				cost += components[curComp].scor[s[vals[j]]][s[vals[i]]];
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
		check_time();
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
			cost3 += components[curComp].scor[s[i]][s[j]];

		}
	}

	long long tot2 = 0;
	for (int i = 0; i < new_seq_3.size(); ++i) {
		for (int j = i + 1; j < new_seq_3.size(); ++j) {
			tot2 += components[curComp].scor[new_seq_3[i]][new_seq_3[j]];
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
		check_time();
		long long castig = 0, best = 0;
		int best_pos = -1;
		for (int j = i - 1; j >= st; --j) {
			if (i - j > maxDist) {
				break;
			}
			castig -= components[curComp].scor[v[i]][v[j]] - components[curComp].scor[v[j]][v[i]];
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
			castig -= components[curComp].scor[v[j]][v[i]] - components[curComp].scor[v[i]][v[j]];
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
	return (components[curComp].avg[x] < components[curComp].avg[y] || (components[curComp].avg[x] == components[curComp].avg[y] && x <= y));
}

void run_local_search() {

	for (curComp = 0; curComp < components.size(); ++curComp) {
		if (components[curComp].best_heuristic.empty()) {
			reverse(components[curComp].best_heuristic.begin(), components[curComp].best_heuristic.end());
		}
	}

	for ever{
		for (int sz = 20; sz <= 500; sz += 20) {
			for (curComp = 0; curComp < components.size(); ++curComp) {
				check_time();
				if (components[curComp].best_heuristic.empty()) {
					continue;
				}
				if (!components[curComp].scor.empty()) {
					for (int i = 0; i + sz < components[curComp].best_heuristic.size(); i += sz / 2) {
						reord_sub_seq(components[curComp].best_heuristic, i, i + sz);
					}
					try_optimize(components[curComp].best_heuristic, 0, ((int)components[curComp].best_heuristic.size()) - 1);
				}
				else {
					try_optimize_big_test(10);
				}
			}
		}
	}
}


double check_time() {
	auto curTime = std::chrono::high_resolution_clock::now();
	auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(curTime - beginTime);
	double sec = elapsed.count() * 1e-9;
	if (sec > SECONDS) {
		print_result();
		exit(0);
	}
	return sec;
}