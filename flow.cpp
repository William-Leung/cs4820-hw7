/*
g++ -std=c++17 -O2 -o a.out flow.cpp; ./a.out
 */

#ifndef ALGO_CPP_FLOWNETWORK_H
#define ALGO_CPP_FLOWNETWORK_H

#include <cstdint>
#include <limits>
#include <limits.h>
#include <vector>
#include <unordered_set>
#include <utility>
#include <queue>
#include <stack>
#include <iostream>
#include <fstream>
#include <unordered_map>

namespace flow_network
{
  class Arc
  {
  public:
    uint64_t u;
    uint64_t v;
    uint64_t c;

    Arc(uint64_t u, uint64_t v, uint64_t c);
    Arc();
  };

  class FlowResults
  {
  public:
    FlowResults(std::vector<std::vector<uint64_t>> graph, std::vector<uint64_t> dest);
    uint64_t max_flow;
    std::vector<uint64_t> res_cap;
    const std::vector<std::vector<uint64_t>> graph;
    const std::vector<uint64_t> dest;
  };

  class FlowNetwork
  {

  public:
    FlowNetwork(uint64_t m, uint64_t n, uint64_t s, uint64_t t, const std::vector<Arc> &arcs);
    FlowResults dinic();

  private:
    std::vector<std::vector<uint64_t>> graph;
    uint64_t s;
    uint64_t t;
    uint64_t m;
    uint64_t n;
    std::vector<uint64_t> cap;
    std::vector<uint64_t> dest;
  };

}

#endif // ALGO_CPP_FLOWNETWORK_H

flow_network::Arc::Arc(uint64_t u, uint64_t v, uint64_t c) : u(u), v(v), c(c){};

flow_network::Arc::Arc() = default;

flow_network::FlowResults::FlowResults(std::vector<std::vector<uint64_t>> graph, std::vector<uint64_t> dest) : graph(
                                                                                                                   std::move(graph)),
                                                                                                               dest(std::move(dest)) {}

flow_network::FlowNetwork::FlowNetwork(uint64_t m, uint64_t n, uint64_t s, uint64_t t, const std::vector<Arc> &arcs)
    : m(m), n(n), s(s), t(t)
{
  cap = std::vector<uint64_t>(2 * m, 0);
  graph = std::vector<std::vector<uint64_t>>(n);
  uint64_t edge_idx = 0;
  for (auto &arc : arcs)
  {
    cap[edge_idx] = arc.c;
    graph[arc.u].push_back(edge_idx++);
    graph[arc.v].push_back(edge_idx++);
    dest.push_back(arc.v);
    dest.push_back(arc.u);
  }
}

void compute_distances_faster(std::vector<uint64_t> &distances, std::vector<uint64_t> &q, const std::vector<uint64_t> &rescap,
                              const std::vector<std::vector<uint64_t>> &graph, const std::vector<uint64_t> &dest, uint64_t s,
                              uint64_t t)
{
  std::fill(distances.begin(), distances.end(), -1);
  uint64_t n = graph.size();

  distances[s] = 0;
  uint64_t qs = 0;
  uint64_t qe = 1;
  q[0] = s;

  while (qs < qe && distances[t] == -1)
  {
    uint64_t v = q[qs];
    qs++;
    if (distances[t] != -1 && distances[v] >= distances[t])
      break;
    for (uint64_t idx : graph[v])
    {
      uint64_t w = dest[idx];
      if (rescap[idx] > 0 && distances[w] == uint64_t(-1))
      {
        distances[w] = distances[v] + 1;
        q[qe] = w;
        qe++;
      }
    }
  }
}

// use some tricks to augment by a blocking flow in O(mn) time
uint64_t dinic_augment(std::vector<uint64_t> &rescap, const std::vector<uint64_t> &cap, std::vector<uint64_t> &ptrs,
                       const std::vector<uint64_t> &distances, const std::vector<std::vector<uint64_t>> &graph,
                       const std::vector<uint64_t> &dest, uint64_t s, uint64_t t)
{

  const uint64_t s_size = graph[s].size();

  uint64_t ans = 0;
  // each record [u, bottleneck_cap, bottleneck_start] means that there's a path from s to u with bottleneck edge leaving bottleneck_start of capacity bottleneck_cap
  std::stack<std::tuple<uint64_t, uint64_t, uint64_t>> vertices;

  // state of search
  uint64_t curr;
  uint64_t bottleneck;
  uint64_t bottleneck_start;

  // fix ptr for s, init first search
  {
    uint64_t idx = graph[s][ptrs[s]];
    while (ptrs[s] < graph[s].size() && (distances[dest[idx]] != distances[s] + 1 || rescap[idx] == 0))
    {
      ptrs[s]++;
      idx = graph[s][ptrs[s]];
    }

    bottleneck = std::numeric_limits<uint64_t>::max();
    bottleneck_start = -1;
    curr = s;
  }

  // while there's an edge leaving s in level graph
  while (ptrs[s] < s_size)
  {
    // basic invariant that I spammed everywhere

    // stop whenever we find t or a dead end (and don't put them on the stack, instead store using 3 state vars)
    while (curr != t && ptrs[curr] < graph[curr].size())
    {
      vertices.emplace(curr, bottleneck, bottleneck_start);

      uint64_t idx = graph[curr][ptrs[curr]];

      if (rescap[idx] < bottleneck)
      {
        bottleneck = rescap[idx];
        bottleneck_start = curr;
      }
      uint64_t next = dest[idx];

      // fix ptr for next (to check if it's a dead end)
      {
        uint64_t idx = graph[next][ptrs[next]];
        while (ptrs[next] < graph[next].size() &&
               (distances[dest[idx]] != distances[next] + 1 || rescap[idx] == 0))
        {
          ptrs[next]++;
          idx = graph[next][ptrs[next]];
        }
      }

      curr = next;

      {
        auto tup = vertices.top();
        uint64_t curr2 = std::get<0>(tup);
        uint64_t idx = graph[curr2][ptrs[curr2]];
        uint64_t revIdx = (cap[idx] == 0) ? idx - 1 : idx + 1;
      }
    }

    if (curr == t)
    {
      //            fprintf(stderr, "augmenting\n");
      uint64_t curr2;
      while (!vertices.empty())
      {
        auto tup = vertices.top();
        curr2 = std::get<0>(tup);

        // graph formation invariant: forward edges precede their neighboring backward edges
        uint64_t idx = graph[curr2][ptrs[curr2]];
        uint64_t revIdx = (cap[idx] == 0) ? idx - 1 : idx + 1;

        rescap[idx] -= bottleneck;
        rescap[revIdx] += bottleneck;

        while (ptrs[curr2] < graph[curr2].size() &&
               (distances[dest[idx]] != distances[curr2] + 1 || rescap[idx] == 0))
        {
          ptrs[curr2]++;
          idx = graph[curr2][ptrs[curr2]];
        }
        vertices.pop();
      }
      ans += bottleneck;

      // do another search
      bottleneck = std::numeric_limits<uint64_t>::max();
      bottleneck_start = -1;
      curr = s;
    }
    else
    {
      // delete edges leading to dead-end vertices

      uint64_t pred = std::get<0>(vertices.top()); // direct predecessor of node with outdegree 0

      while (ptrs[curr] == graph[curr].size() && !vertices.empty())
      { // curr has out-degree 0 in level graph

        auto tup = vertices.top();
        curr = std::get<0>(tup);
        bottleneck = std::get<1>(tup);
        bottleneck_start = std::get<2>(tup);

        vertices.pop();

        ptrs[curr]++; // discard the edge that led to the dead end

        { // discard other edges
          uint64_t idx = graph[curr][ptrs[curr]];
          while (ptrs[curr] < graph[curr].size() &&
                 (distances[dest[idx]] != distances[curr] + 1 || rescap[idx] == 0))
          {
            ptrs[curr]++;
            idx = graph[curr][ptrs[curr]];
          }
        }
      }

      // check that some pointer went up but not uselessly

      if (!vertices.empty())
      {
        bottleneck = bottleneck;
        bottleneck_start = bottleneck_start;
        curr = curr;
      }
      else
      {
        bottleneck = std::numeric_limits<uint64_t>::max();
        bottleneck_start = -1;
        curr = s;
      }
    }
  }

  return ans;
}

flow_network::FlowResults flow_network::FlowNetwork::dinic()
{
  uint64_t ans = 0;
  std::vector<uint64_t> rescap(cap);
  std::vector<uint64_t> q(2 * n);

  // result of BFS (to avoid actually manifesting the edges of the level graph)
  std::vector<uint64_t> distances(n, -1);
  std::vector<uint64_t> ptrs(n, 0); // ptr[u] == k  <==>  the first k neighbors of u are not in the level graph
                                    //    compute_distances(distances, rescap, graph, dest, s, t);
  compute_distances_faster(distances, q, rescap, graph, dest, s, t);

  while (distances[t] != uint64_t(-1))
  {
    //        fprintf(stderr, "t dist: %lld\n", distances[t]);
    ans += dinic_augment(rescap, cap, ptrs, distances, graph, dest, s, t);
    compute_distances_faster(distances, q, rescap, graph, dest, s, t);

    std::fill(ptrs.begin(), ptrs.end(), 0); // reset ptrs
  }

  FlowResults fr(graph, dest);
  fr.res_cap = rescap;
  fr.max_flow = ans;

  return fr;
}

using namespace flow_network;
using namespace std;

void DFS(uint64_t v, FlowResults net, unordered_map<int, bool> &visited)
{
  visited[v] = true;
  for (int i = 0; i < net.graph[v].size(); i++)
  {
    uint64_t idx = net.graph[v][i];
    uint64_t w = net.dest[idx];
    if (!visited[w] && net.res_cap[idx] > 0)
    {
      DFS(w, net, visited);
    }
  }
}

#include <chrono>
using namespace std::chrono;

int main()
{
  bool debug = true;

  auto start = high_resolution_clock::now();

  ifstream infile("zeroprofit.txt");

  int n, m, p;

  if (debug)
    infile >> n >> m >> p;
  else
    cin >> n >> m >> p;

  const uint64_t infinity = numeric_limits<uint64_t>::max();

  vector<Arc> edges;
  if (debug)
  {
    /** n inputs: s_v corresponds to stall i
        effect: creates n edges (0,i,p*s_v) from s(node 0) to stalls */
    for (int i = 1; i <= n; i++)
    {
      int sales_volume = 0;
      infile >> sales_volume;
      edges.push_back(Arc(0, i, p * sales_volume));
      // cout << "s-stall edge: (0, " << i << ", " << p * sales_volume << ")" << endl;
    }
    /** m inputs: u v c corresponds to street i
        effect: creates m edges (u,i,inf) from stall u to street i
        effect: creates m edges (v,i,inf) from stall v to street i
        effect: creates m edges (i,n+m+1,c) from street i to t(node n+m+1) */
    for (int i = n + 1; i <= n + m; i++)
    {
      int u, v, cleaning_cost;
      infile >> u >> v >> cleaning_cost;
      edges.push_back(Arc(u, i, infinity));
      edges.push_back(Arc(v, i, infinity));
      edges.push_back(Arc(i, n + m + 1, cleaning_cost));

      /**cout << "stall-street edge: (" << u << ", " << i << ", " << infinity << ")" << endl;
      cout << "stall-street edge: (" << v << ", " << i << ", " << infinity << ")" << endl;
      cout << "street-t edge: (" << i << ", " << (n + m + 1) << ", " << cleaning_cost << ")" << endl;*/
    }
  }
  else
  {
    for (int i = 1; i <= n; i++)
    {
      int sales_volume = 0;
      cin >> sales_volume;
      edges.push_back(Arc(0, i, p * sales_volume));
    }
    for (int i = n + 1; i <= n + m; i++)
    {
      int u, v, cleaning_cost;
      cin >> u >> v >> cleaning_cost;
      edges.push_back(Arc(u, i, infinity));
      edges.push_back(Arc(v, i, infinity));
      edges.push_back(Arc(i, n + m + 1, cleaning_cost));
    }
  }
  infile.close();

  FlowNetwork network(3 * m + n, n + m + 2, 0, n + m + 1, edges);
  FlowResults flow = network.dinic();

  // hash map between vertices and their visited status
  unordered_map<int, bool> visited;
  // initialize everyone visited to false
  for (int i = 0; i < n + m + 2; i++)
  {
    visited[i] = false;
  }
  // DFS from source
  DFS(0, flow, visited);

  // source node should not be part of minimum cut
  visited[0] = false;
  int profit = 0;
  int num_visited = 0;
  // iterate through edges to find profit
  for (int i = 0; i < edges.size(); i++)
  {
    if (edges[i].u == 0 && visited[edges[i].v])
    {
      profit += edges[i].c;
      num_visited++;
    }
    else if (edges[i].v == n + m + 1 && visited[edges[i].u])
    {
      profit -= edges[i].c;
    }
  }

  bool first = true;
  if (profit > 0)
  {
    cout << profit << " " << num_visited << endl;
    for (int i = 0; i < visited.size() && i <= n; i++)
    {
      if (visited[i])
      {
        if (first)
        {
          cout << i;
          first = false;
        }
        else
          cout << " " << i;
      }
    }
  }
  else
    cout << "0" << endl
         << endl;

  auto stop = high_resolution_clock::now();
  auto duration = duration_cast<microseconds>(stop - start);
  cout << "Time taken by function: "
       << duration.count() / 1000000.0 << " seconds" << endl;

  return 0;
}