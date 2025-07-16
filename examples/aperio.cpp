#include <cassert>
#include <vector>
#include <map>
#include <set>
#include <format>
#include <numeric>
#include <ranges>
#include <random>
#include <iterator>
#include <chrono>
#include <thread>
#include <execution>
#include <fstream>


#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/breadth_first_search.hpp>

#include "Highs.h"

using std::cout;
using std::endl;

/**
 * A simple timer class.
 **/
class Timer {
  public:
    // Stores a start time and returns the id.
    size_t start() {
        start_times.push_back(std::chrono::high_resolution_clock::now());
        return start_times.size() - 1;
    };

    // @returns time in milliseconds since start point
    unsigned int stop(size_t id, bool print_time = true) {
        const auto         end   = std::chrono::high_resolution_clock::now();
        const auto         start = start_times[id];
        const unsigned int dt =
            std::chrono::duration_cast<std::chrono::microseconds>(end - start)
                .count();

        if (print_time) {
            if (dt < 10'000)
                printf("\ttook %.2fms\n", dt / 1'000.);
            else if (dt < 10'000'000)
                printf("\ttook %ums\n", dt / 1'000);
            else
                printf("\ttook %.2fs\n", dt / 1'000'000.);
        }
        return std::chrono::duration_cast<std::chrono::milliseconds>(end - start)
                .count();
    }

  private:
    std::vector<std::chrono::time_point<std::chrono::high_resolution_clock>>
        start_times;
};


// A custom visitor to stop the search once the target is found
template <class T>
class bfs_visitor_found : public boost::default_bfs_visitor {
public:
    bfs_visitor_found(T& target) : m_target(target), m_found(false) {}

    template <class Vertex, class Graph>
    void examine_vertex(Vertex u, const Graph& g) {
        if (u == m_target) {
            m_found = true;
        }
    }

    bool found() const { return m_found; }

private:
    T& m_target;
    bool m_found;
};

unsigned int create_LP(HighsLp& LP, const int num_intermediates=160, const bool use_int=true, const bool multithreading = true, const int num_sinks=10, const int num_sources=10, const int num_source_connections=60, const int num_commodities = 100, const int seed=42) {
	std::random_device rd; // ignore
	std::srand(seed);
	auto gen = std::mt19937{seed};
	Timer timer;

	const float max_ub = 1.0e30;

	int num_nodes = num_sinks + num_sources + num_intermediates;


	cout << "Init problem\n";
	auto t_init_problem = timer.start();


	std::vector<int> nodes(num_nodes);
	std::iota(nodes.begin(), nodes.end(), 0);

	auto sources = nodes | std::views::reverse | std::views::drop(num_sinks + num_intermediates) | std::views::reverse;
	auto sinks = nodes | std::views::drop(num_sources) | std::views::reverse | std::views::drop(num_intermediates) | std::views::reverse;
	auto intermediates = nodes | std::views::drop(num_sinks + num_sources);

	std::map<std::pair<int,int>, int> edges;
	std::map<std::pair<int,int>, int> cost;
	std::uniform_int_distribution<> cost_distrib(1, 5);

	// sources to intermediates
	for (auto s : sources) {
		std::vector<int> samples;
		std::ranges::sample(intermediates, std::back_inserter(samples), num_source_connections, gen);
		for (auto n : samples) {
			edges.insert({{s, n}, cost_distrib(gen) + 4}); // [5, 10]
			cost.insert({{s,n}, cost_distrib(gen)});
		}
	}

	// Intermediate to intermediate
	int idx = 0;
	for (auto i : intermediates) {
		auto sample_list = intermediates | std::views::drop(++idx);
		int sample_size = std::min(3ul, sample_list.size());
		std::vector<int> samples;
		std::ranges::sample(sample_list, std::back_inserter(samples), sample_size, gen);
		for (auto j : samples) {
			edges.insert({{i, j}, cost_distrib(gen) + 4});
			cost.insert({{i, j}, cost_distrib(gen)});
		}
	}


	// intermediate to sinks (randomly assign edges to some sinks only, not all reachable
	for (auto n : intermediates) {
		std::vector<int> reachable_sinks;
		std::uniform_int_distribution<> distrib(1, sinks.size());
		std::ranges::sample(sinks, std::back_inserter(reachable_sinks), distrib(gen), gen); 
		for (auto t : reachable_sinks) {
			edges.insert({{n, t}, cost_distrib(gen) + 4});
			cost.insert({{n, t}, cost_distrib(gen)});
		}
	}

	auto t_graph = timer.start();
	// Find reachable sinks for each node using boost graph and BFS
	std::vector<std::vector<int>> source_to_reachable_sinks(sources.size()); 	
	auto edges_keys = std::views::keys(edges);
	{ // scope to help compiler decide to throw the graph datastructure away
		using Graph = boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS>;
		using Vertex = boost::graph_traits<Graph>::vertex_descriptor;
		Graph g(edges_keys.begin(), edges_keys.end(), nodes.size());

		for (int i = 0; i < sources.size(); i++) {
			int s = sources[i];
			Vertex start = boost::vertex(s, g);
			std::vector<int> reachables;
			for (auto t : sinks) {
				Vertex end = boost::vertex(t, g);
				bfs_visitor_found<Vertex> visitor(end);
				boost::breadth_first_search(g, start, boost::visitor(visitor));
				if (visitor.found()) {
					reachables.push_back(t);
				}
			}
			// works since sources are always nubmered 0 to num_sources in this demo
			source_to_reachable_sinks[i] = reachables;
		}
	}
	cout << "path cheching:";
	timer.stop(t_graph, true);
	cout << "\n";

	// commodities with reachable sinks only
	std::vector<std::pair<int, int>> commodities;
	std::uniform_int_distribution<> source_choice(0, sources.size()-1);
	std::uniform_int_distribution<> sink_choice(0, sinks.size()-1);
	for (int i = 0; i < num_commodities; i++) {
		int src = sources[source_choice(gen)];
		auto& reachable_sinks = source_to_reachable_sinks[src];
		int tgt;
		if (reachable_sinks.size() == 0) {
			tgt = sinks[source_choice(gen)];	
		} else {
			std::uniform_int_distribution<> reachable_choice(0, reachable_sinks.size()-1);
			tgt = reachable_sinks[reachable_choice(gen)];
		}
		commodities.emplace_back(src,tgt);
	}
	std::vector<int> demand(commodities.size());
	std::generate(demand.begin(), demand.end(), [&]() { return cost_distrib(gen) + 4;});

	timer.stop(t_init_problem, true);

	// Build HiGHS LP
	//
	auto t_init_LP = timer.start();
	float alpha = 1.f;

	// gather variables
	// std::map<std::tuple<int, int, int>, int> flow;
	std::map<std::pair<int, int>, std::vector<int>> flow;
	std::map<std::pair<int, int>, int> activations;
	int var_idx = 0;

	bool t_init_vars = timer.start();
	// binary vars for each edge 
	std::vector<double> col_lower, col_upper, col_costs;
	for (auto& edge : edges_keys) {
		activations.insert({edge, col_costs.size()});
		col_lower.push_back(0.f);
		col_upper.push_back(1.f);
		col_costs.push_back(0.f);
	}
	
	// intermediate node activation
	std::map<int, int> intermediate_active;
	for (auto n : intermediates) {
		intermediate_active.insert({n, col_costs.size()});
		col_lower.push_back(0.f);
		col_upper.push_back(1.f);
		col_costs.push_back(alpha);
	}

	// flow continuous vars for each commodity and edge
	for (auto &edge : edges_keys) {
		std::vector<int> edge_flows;
		for (int k = 0; k < commodities.size(); k++) {
			edge_flows.push_back(col_costs.size());
			col_lower.push_back(0.f);
			col_upper.push_back(max_ub);
			col_costs.push_back(cost.at(edge));
			// flow.insert({{edge.first, edge.second, k}, idx++});	
		}
		flow.insert({edge, edge_flows});
	}
	cout << "Init variables \n";
	timer.stop(t_init_vars, true);

	LP.sense_ = ObjSense::kMinimize;
	LP.offset_ = 0;
	LP.num_col_ = col_costs.size();
	LP.col_lower_ = col_lower;
	LP.col_upper_ = col_upper;
	LP.col_cost_ = col_costs;

	// const int num_constraints = edges.size() + intermediates.size,
	std::vector<int> row_start = {0};
	std::vector<int> col_idx;
	std::vector<double> col_value;
	std::vector<double> row_ub;
	std::vector<double> row_lb;

	auto t_init_constraint = timer.start();
	// Capacity constraints with activation: sum of flows <= capacity * activation
	// ==> capacity * activation - sum of flows >= 0
	for (auto& edge : edges_keys) {
		auto& edge_flow = flow.at(edge);
		col_idx.push_back(activations.at(edge));
		col_value.push_back(edges.at(edge));
		for (auto k : flow.at(edge)) {
			col_value.push_back(-1.f);
			col_idx.push_back(k);
		}
		// start new row
		row_start.push_back(col_idx.size());
		row_ub.push_back(max_ub);
		row_lb.push_back(0.f);
	}
	cout << "capacity constraints\n";
	timer.stop(t_init_constraint, true);
	
	t_init_constraint = timer.start();
	// Node activation links: if a node is inactive, edges in/out of it cannot be active
	// intermediate_active - activation[u,v] >= 0
	for (auto n : intermediates) {
		auto node_edges = edges_keys | std::views::filter([n] (std::pair<int, int> edge) {return edge.second == n || edge.first == n;});
		for (auto &edge : node_edges) {
			col_value.push_back(-1.f);
			col_idx.push_back(activations.at(edge));
			col_value.push_back(1.f);
			col_idx.push_back(intermediate_active.at(n));

			// each of these is just one constraint!
			row_start.push_back(col_idx.size());
			row_ub.push_back(max_ub);
			row_lb.push_back(0.f);
		}
	}

	cout << "Node activation links constraints\n";
	timer.stop(t_init_constraint, true);
	
	t_init_constraint = timer.start();
	cout << "Flow conservation constraint\n";
	// flow conservation constraints for each commodity
	// sum outflow - sum inflow >= demand
	// 
	// Temporary structures to avoid multithreading problems when working on the main ones
	if (multithreading) {
		cout << "Adding flow conservation with multithreading activated." << endl;
		std::vector<std::map<int, float>> all_cols(commodities.size() * nodes.size());
		std::vector<double> demands(commodities.size() * nodes.size());
		std::vector<int> k_counter(commodities.size());
		std::iota(k_counter.begin(), k_counter.end(), 0);
		std::for_each(std::execution::par_unseq, k_counter.begin(), k_counter.end(), [&] (int k) {
			auto [src, tgt] = commodities.at(k);
			for (int node_idx = 0; node_idx < nodes.size(); node_idx++) {
				auto n = nodes.at(node_idx);
				std::map<int, float> cols; // we need to sort this for proper mem access
				// inflow
				auto incoming = flow | std::views::filter([n] (const auto& tmp) {return tmp.first.second == n;});
				auto outgoing = flow | std::views::filter([n] (const auto& tmp) {return tmp.first.first == n;});

				const double in_mod = n == src ? -1.f : 1.f;
				const double out_mod = in_mod * -1.f;
				const double demand_mod = n == src || n == tgt ? demand[k] : 0.f;

				for (auto x : incoming) {
					cols.insert({x.second.at(k), in_mod});
				}
				for (auto x : outgoing) {
					cols.insert({x.second.at(k), out_mod});
				}

				all_cols.at(k*nodes.size() + node_idx) = cols;
				demands.at(k * nodes.size() + node_idx) = demand_mod;
			}
		});
		// Now gather all partial results into the main datastructure
		for (int i = 0; i < all_cols.size(); i++) {
			const auto& cols = all_cols.at(i);
			const auto demand_mod = demands.at(i);

			for (auto& col : cols) {
				col_value.push_back(col.second);
				col_idx.push_back(col.first);
			}
			row_ub.push_back(max_ub); // maybe 0 is fine as well?
			row_lb.push_back(static_cast<double>(demand_mod));
			row_start.push_back(col_idx.size());
		}
	// single threaded version
	} else {
		cout << "Adding flow conservation." << endl;
		for (int k = 0; k < commodities.size(); k++) {
			auto [src, tgt] = commodities.at(k);
			for (auto n : nodes) {
				std::map<int, float> cols; // we need to sort this for proper mem access
				// inflow
				auto incoming = flow | std::views::filter([n] (const auto& tmp) {return tmp.first.second == n;});
				auto outgoing = flow | std::views::filter([n] (const auto& tmp) {return tmp.first.first == n;});

				const double in_mod = n == src ? -1.f : 1.f;
				const double out_mod = in_mod * -1.f;
				const double demand_mod = n == src || n == tgt ? demand[k] : 0.f;

				for (auto x : incoming) {
					cols.insert({x.second.at(k), in_mod});
				}
				for (auto x : outgoing) {
					cols.insert({x.second.at(k), out_mod});
				}

				for (auto col : cols) {
					col_value.push_back(col.second);
					col_idx.push_back(col.first);
				}

				row_ub.push_back(max_ub); // maybe 0 is fine as well?
				row_lb.push_back(static_cast<double>(demand_mod));
				row_start.push_back(col_idx.size());
			}
		}
	}
	timer.stop(t_init_constraint, true);
	
  LP.a_matrix_.format_ = MatrixFormat::kRowwise;
	LP.num_row_ = row_start.size() - 1;
	LP.row_lower_ = row_lb;
	LP.row_upper_ = row_ub;
	LP.a_matrix_.start_ = row_start;
	LP.a_matrix_.index_ = col_idx;
	LP.a_matrix_.value_ = col_value;

	cout << "Init LP\n";
	t_init_LP = timer.stop(t_init_LP, true);

	if (use_int) {
		LP.integrality_.resize(LP.num_col_);
		for (int i = 0; i < edges.size() + intermediates.size(); i++)
				LP.integrality_[i] = HighsVarType::kInteger;
	}
	return t_init_LP;
}

int main(int argc, char *argv[]) {

	std::ofstream f_out;
	f_out.open("benchs_with_cutting.csv", std::ios::app);
	f_out << "t_init,t_solve,objective value,num_intermediates,use ints,multithreading\n";
	f_out.flush();
	for (int j = 7; j < 15; j++) {
	// 	for (int i = 1; i < 2; i++) {
			HighsModel model;
			auto& LP = model.lp_;
			Timer timer;

			// for (int i = 7; i < 15; i++) {
			// 	create_LP(LP, 1<<i);
			// }
			// return 1;
			bool multithreading = 1;
			bool use_int = 1;
			// int num_intermediates = 160;
			int num_intermediates = 1<<j;

			cout << "--------  --------\n";
			cout << "-------- --------\n";
			cout << "-------- creating LP with " << num_intermediates << "intermediates --------\n";

			auto t_init_LP = create_LP(LP, num_intermediates, use_int, multithreading);

			multithreading=false;
			Highs highs;
			HighsStatus return_status;

			//
			// Pass the model to HiGHS
			return_status = highs.passModel(model);
			const HighsLp& lp = highs.getLp();
			assert(return_status == HighsStatus::kOk);
			std::string options_file = "highs_options";
			highs.readOptions(options_file);

			// if (multithreading)
			// 	highs.setOptionValue("parallel", "on");
			//
			// highs.setOptionValue("solver", "ipm");
			auto t_solve = timer.start();
			cout << "Solving..." << endl;

			return_status = highs.run();
			assert(return_status == HighsStatus::kOk);

			t_solve = timer.stop(t_solve, true);

			const HighsModelStatus& model_status = highs.getModelStatus();
			assert(model_status == HighsModelStatus::kOptimal);
			cout << "Model status: " << highs.modelStatusToString(model_status) << endl;
			//
			// Get the solution information
			const HighsInfo& info = highs.getInfo();
			cout << "Simplex iteration count: " << info.simplex_iteration_count << endl;
			cout << "Objective function value: " << info.objective_function_value << endl;
			cout << "Primal  solution status: "
					 << highs.solutionStatusToString(info.primal_solution_status) << endl;
			cout << "Dual    solution status: "
					 << highs.solutionStatusToString(info.dual_solution_status) << endl;
			cout << "Basis: " << highs.basisValidityToString(info.basis_validity) << endl;


			const bool has_values = info.primal_solution_status;
			const bool has_duals = info.dual_solution_status;
			const bool has_basis = info.basis_validity;
			//
			// Get the solution values and basis
			const HighsSolution& solution = highs.getSolution();
			const HighsBasis& basis = highs.getBasis();
			//
			// Report the primal and solution values and basis
			for (int col = 0; col < 100; col++) {
			// for (int col = 0; col < edges.size() + intermediates.size(); col++) {
				if (has_values) {
					auto val = solution.col_value[col];
					if (!((val > (1.f - 1e-3f) && val <= 1.f) || (std::abs(val) >= 0.f && std::abs(val) <= 1e-3f))) {
						cout << "Column " << col;
						if (has_values) cout << "; value = " << solution.col_value[col];
						if (has_duals) cout << "; dual = " << solution.col_dual[col];
						if (has_basis)
							cout << "; status: " << highs.basisStatusToString(basis.col_status[col]);
						cout << endl;
					}
				}
			 }
			f_out << t_init_LP << ",";
			f_out << t_solve << ",";
			f_out << info.objective_function_value << ",";
			f_out << num_intermediates << "," << use_int << "," << multithreading << "\n";
			f_out.flush();
			
	// 	}
	}
	f_out.close();
	return 0;
}
