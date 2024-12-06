#include "markedCS.h"
#include <queue>
#include <unordered_set>
#include <unordered_map>
#include <stack>
#include <set>

#define MAX_LABEL 10000000

using namespace std;

#ifdef COREBASED
int core_edge_idx;
#endif

pair<unordered_set<int>, unordered_set<int>> *edge_mni_count;

class HeapElement
{
public:
  int ub;
  int nv;
  int is_backward;
  Graph *graph;
  CandidateSpace *CS;

  HeapElement()
  {
    ub = 0;
    graph = NULL;
    CS = NULL;
  }

  HeapElement(int iub, int iis_backward, Graph *igraph) : ub(iub), is_backward(iis_backward), graph(igraph), CS(NULL) {}
  HeapElement(int iub, int inv, int iis_backward, Graph *igraph, CandidateSpace *iCS) : ub(iub), nv(inv), is_backward(iis_backward), graph(igraph), CS(iCS) {}

  bool operator<(const HeapElement rhs) const
  {
    if (this->ub != rhs.ub)
      return this->ub < rhs.ub;
	else if(this->nv != rhs.nv)
		return this->nv > rhs.nv;
	else
    return this->is_backward < rhs.is_backward;
  }
};

class AnswerElement
{
public:
  int mni;
  Graph *graph;

  AnswerElement(int imni, Graph *igraph) : mni(imni), graph(igraph) {}

  bool operator<(const AnswerElement rhs) const
  {
    return this->mni > rhs.mni;
  }
};

void build_right_most_path(const DfsCodes &dfs_codes, Graph *graph)
{
  int prev_id = -1;
  for (auto i = dfs_codes.size(); i > 0; --i)
  {
    if (dfs_codes[i - 1].from < dfs_codes[i - 1].to &&
        (graph->rmpSize == 0 || prev_id == dfs_codes[i - 1].to))
    {
      prev_id = dfs_codes[i - 1].from;
      graph->right_most_path[++graph->rmpSize - 1] = dfs_codes[i - 1].to;
    }
  }
  graph->right_most_path[graph->rmpSize++] = 0;
}


bool is_min(Graph *graph);

inline void createSubgraph(Graph *&graph, Graph *parent_graph, bool forward_edge, int new_label, int edge_label, int fst, int snd)
{
  vector<pair<int, int>> edges;

  number_type numVertex, numEdge;
  number_type pnumVertex = parent_graph->nVertex;

  numVertex = pnumVertex + (forward_edge ? 1 : 0);
  graph = new Graph();
  graph->initVertex(numVertex);

  copy(parent_graph->label, parent_graph->label + pnumVertex, graph->label);
  if (forward_edge)
    graph->label[numVertex - 1] = new_label;

  numEdge = parent_graph->nEdge + 1;
  graph->initEdge(numEdge);

  copy(parent_graph->degree, parent_graph->degree + pnumVertex, graph->degree);
  graph->degree[fst]++;
  graph->degree[snd]++;

  graph->DfsCode = parent_graph->DfsCode;
  if (forward_edge)
  {
    dfs_code_t dfs_code(fst, snd, graph->label[fst], edge_label, new_label);
    graph->DfsCode.emplace_back(dfs_code);
  }
  else
  {
    dfs_code_t dfs_code(fst, snd, graph->label[fst], edge_label, graph->label[snd]);
    graph->DfsCode.emplace_back(dfs_code);
  }

  build_right_most_path(graph->DfsCode, graph);

  number_type pos = 0;
  for (int i = 0; i < graph->nVertex; ++i)
  {
    graph->nbrOffset[i] = pos;
    pos += (number_type)graph->degree[i];
    graph->core[i] = graph->degree[i];
    if (graph->degree[i] > graph->maxDegree)
      graph->maxDegree = graph->degree[i];
  }
  graph->nbrOffset[graph->nVertex] = pos;

  pos = 0;
  for (int i = 0; i < pnumVertex; ++i)
  {
    copy(parent_graph->nbr.arr + parent_graph->nbrOffset[i], parent_graph->nbr.arr + parent_graph->nbrOffset[i + 1], graph->nbr.arr + pos);
    pos += (parent_graph->nbrOffset[i + 1] - parent_graph->nbrOffset[i]);
    if (i == fst)
    {
      graph->nbr.set(pos++, snd, edge_label);
    }
    else if (i == snd)
    {
      graph->nbr.set(pos++, fst, edge_label);
    }
  }
  if (forward_edge)
  {
    assert(fst < snd);
    graph->nbr.set(pos, fst, edge_label);
  }


  for(int i = 0; i < graph->nVertex; ++i)
  {
    graph->nbrToPos[i] = new int[graph->nVertex];
    memset(graph->nbrToPos[i],  -1, sizeof(int) * graph->nVertex);
    for (int j = graph->nbrOffset[i]; j < graph->nbrOffset[i + 1]; ++j)
    {
      int un = graph->nbr[j];
      graph->nbrToPos[i][un] = j - graph->nbrOffset[i];
    }
  }

}

inline void createSubgraphEdge(Graph *&graph, int l1, int edge_label, int l2)
{
  vector<pair<int, int>> edges;

  number_type numVertex, numEdge;

  numVertex = 2;
  graph = new Graph();
  graph->initVertex(numVertex);

  graph->label[0] = l1;
  graph->label[1] = l2;

  numEdge = 1;
  graph->initEdge(numEdge);

  graph->degree[0] = 1;
  graph->degree[1] = 1;

  dfs_code_t dfs_code(0, 1, l1, edge_label, l2);
  graph->DfsCode.emplace_back(dfs_code);

  graph->right_most_path[graph->rmpSize++] = 1;
  graph->right_most_path[graph->rmpSize++] = 0;

  number_type pos = 0;
  for (int i = 0; i < graph->nVertex; ++i)
  {
    graph->nbrOffset[i] = pos;
    pos += (number_type)graph->degree[i];
    graph->core[i] = graph->degree[i];
    if (graph->degree[i] > graph->maxDegree)
      graph->maxDegree = graph->degree[i];
  }
  graph->nbrOffset[graph->nVertex] = pos;
  graph->nbr.set(0, 1, edge_label);
  graph->nbr.set(1, 0, edge_label);
  nQueryVertex = 2;
}

#ifdef COREBASED
int findCoreEdge(){
	int l1 = coreGraph[0]->label[0];
	int l2 = coreGraph[0]->label[1];
	if (l1 > l2){
		swap(l1, l2);
	}
	int el = coreGraph[0]->nbr.arr[0].second;
	cout<<"edge "<<l1<<" "<<l2<<" "<<el<<endl;
	
	int fel1, fel2, feel, femni;
	for(int i = 0; i < freq_edge_set.size(); ++i){
		tie(femni, fel1, feel, fel2) = freq_edge_set[i];
		if(fel1 > fel2){
			swap(fel1, fel2);
		}
		if(l1==fel1 && l2 == fel2 && el == feel){
			return i;
		}
	}
	cerr<<"this edge is not in the graph"<<endl;
	assert(0);
	return -1;
}
#endif

void computeFrequentEdge(Graph *graph, int K, priority_queue<HeapElement> &cand_graph_set)
{

	edge_mni_count = new pair<unordered_set<int>, unordered_set<int>>[edge_list_num];

  int d1 = graph->maxEdgeLabel;
  int d2 = d1 * nUniqueLabel;
  for (int i = 0; i < graph->nVertex; i++)
  {
    for (int j = graph->nbrOffset[i]; j < graph->nbrOffset[i + 1]; j++)
    {
      int v = graph->nbr.arr[j].first;
      int vl = graph->label[v];
      int el = graph->nbr.arr[j].second;
      if(graph->label[i] <= vl){
        int eid = edge_list[{graph->label[i], vl, el}];
        edge_mni_count[eid].first.insert(i);
        edge_mni_count[eid].second.insert(v);
      }
    }
  }

  for(auto e : edge_list)
  {
    int i, j, k;
    tie(i, j, k) = e.first;

    int mni = min(edge_mni_count[e.second].first.size(), edge_mni_count[e.second].second.size());
    if (mni > 0)
    {
      freq_edge_set.push_back(make_tuple(mni, i, k, j));
    }
  }

  sort(freq_edge_set.begin(), freq_edge_set.end(),
       [](tuple<int, int, int, int> x, tuple<int, int, int, int> y) -> bool
       {
         return get<0>(x) > get<0>(y);
       });

#ifdef COREBASED

  core_edge_idx = findCoreEdge();
  if (freq_edge_set.size() > K+1+core_edge_idx){
    int kmni = get<0>(freq_edge_set[K+core_edge_idx]);
    int endpos = K+core_edge_idx+1;
    for(; endpos < freq_edge_set.size(); ++endpos){
      if( kmni != get<0>(freq_edge_set[endpos]))
        break;
    }
    freq_edge_set.resize(endpos);
  }
#else
  if (freq_edge_set.size() > K){
    int kmni = get<0>(freq_edge_set[K-1]);
    int endpos = K;
    for(; endpos < freq_edge_set.size(); ++endpos){
      if( kmni != get<0>(freq_edge_set[endpos]))
        break;
    }
    freq_edge_set.resize(endpos);
  }
#endif

  int label_freq[MAX_NUM_LABEL];
  freq_edge_offset = new int[nUniqueLabel + 1];
  freq_edge = new tuple<int, int, int>[freq_edge_set.size() * 2 + 1];
  memset(label_freq, 0, sizeof(label_freq));

  for (auto t : freq_edge_set)
  {
    auto m = get<0>(t);
    auto x = get<1>(t);
    auto l = get<2>(t);
    auto y = get<3>(t);
    ++label_freq[x];
    if (x != y)
      ++label_freq[y];
  }

  int temp = 0;
  for (int i = 0; i < nUniqueLabel; ++i)
  {
    freq_edge_offset[i] = temp;
    temp += label_freq[i];
  }
  freq_edge_offset[nUniqueLabel] = temp;

  for (auto t : freq_edge_set)
  {
    auto m = get<0>(t);
    auto x = get<1>(t);
    auto l = get<2>(t);
    auto y = get<3>(t);

    freq_edge[freq_edge_offset[x]++] = make_tuple(m, l, y);
    if (x != y)
      freq_edge[freq_edge_offset[y]++] = make_tuple(m, l, x);
  }
  for (int i = nUniqueLabel - 1; i >= 0; --i)
  {
    freq_edge_offset[i + 1] = freq_edge_offset[i];
  }
  freq_edge_offset[0] = 0;
}

inline void createSubgraphAddtoAnswer(vector<pair<Graph *, int>>& freq_edge_graph,priority_queue<AnswerElement>& answer_set, int K ){
#ifdef COREBASED
  {
    int mni, l1, edge_label, l2;
    tie(mni, l1, edge_label, l2) = freq_edge_set[core_edge_idx];
    Graph *edge_graph;
    createSubgraphEdge(edge_graph, l1, edge_label, l2);
    answer_set.push(AnswerElement(mni, edge_graph));

    freq_edge_graph.push_back(make_pair(edge_graph, mni));
  }
#else // COREBASED
  for (int i=0; i< min(K, (int)freq_edge_set.size()); ++i)
  {
		  auto e = freq_edge_set[i];
    int mni, l1, edge_label, l2;
    tie(mni, l1, edge_label, l2) = e;
    Graph *edge_graph;
    createSubgraphEdge(edge_graph, l1, edge_label, l2);
    answer_set.push(AnswerElement(mni, edge_graph));

    freq_edge_graph.push_back(make_pair(edge_graph, mni));
  }
#endif // COREBASED
}

inline bool buildCSEdge(const Graph &query, const Graph &data, CandidateSpace *candSpace)
{  
  int u1 = query.DfsCode.front().from;
  int u2 = query.DfsCode.front().to;
  int lu1 = query.DfsCode.front().from_label;
  int lu2 = query.DfsCode.front().to_label;
  int el = query.DfsCode.front().edge_label;

  int a = min(lu1, lu2);
  int b = max(lu1, lu2);
  int eid = edge_list[{a, b, el}];
  unordered_set<int> &u0set = edge_mni_count[eid].first;
  CandidateSpace &currSet1 = candSpace[u1];
  
  int start = data.vertexOffset[lu1];
  int end = data.vertexOffset[lu1 + 1];
  while (start < end && 1 > data.degree[data.vertex[start]])
    start++;

  for (int j = start; j < end; j++)
  {
    int v = data.vertex[j]; 
    if (u0set.find(v) != u0set.end())
    {
      currSet1.candidates[currSet1.size++] = v;
    }
  }

  unordered_set<int> &u1set = edge_mni_count[eid].second;
  CandidateSpace &currSet2 = candSpace[u2];
  
  start = data.vertexOffset[lu2];
  end = data.vertexOffset[lu2 + 1];
  
  while (start < end && 1 > data.degree[data.vertex[start]])
    start++;

  for (int j = start; j < end; j++)
  {
    int v = data.vertex[j]; 
    if (u1set.find(v) != u1set.end())
    {
      currSet2.candidates[currSet2.size++] = v;
    }
  }

  unordered_map<pair<int, int>, pair<number_type, number_type>, pairHash>::const_iterator iter;

  int currVertex = query.nVertex - 1; 
  int currLabel = query.label[currVertex];
  char checkVal = 0; 


  int nbr = query.DfsCode.back().from;
  CandidateSpace &nbrUnit = candSpace[nbr];
  for (int y = 0; y < nbrUnit.size; y++)
  {
    int parentCand = nbrUnit.candidates[y]; 

    iter = currG->labelToNbrOffset.find(make_pair(parentCand, currLabel));
    if (iter == currG->labelToNbrOffset.end())
      continue;
    for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
    {
      int canID = currG->nbr[z];
      if (isVisited[canID] == checkVal)
      {
        isVisited[canID]++; 
        if (checkVal == 0)
          arrayToClean[toCleanIndex++] = canID;
      }
    }
  }
  checkVal++; 

  CandidateSpace &currSet = candSpace[currVertex];
  int candIndex = 0;
  for (int checkIndex = 0; checkIndex < toCleanIndex; checkIndex++)
  {
    int canID = arrayToClean[checkIndex]; 
    if (isVisited[canID] == checkVal)
    {
      if (currG->degree[canID] < query.degree[currVertex] || currG->core[canID] < query.core[currVertex] || currG->maxNbrDegree[canID] < query.maxNbrDegree[currVertex])
        continue;
      char isAdded = 1;

      for (int pos = NLFSize - 1; pos >= 0; pos--)
      {
        if (currG->NLF[canID * NLFSize + pos] != (query.NLF[currVertex * NLFSize + pos] | currG->NLF[canID * NLFSize + pos]))
        {
          isAdded = 0;
          break;
        }
      }
      if (isAdded)
      {
        currSet.candidates[candIndex] = canID;
        candIndex++;
      }
    }
  }
  currSet.size = candIndex;
  while (toCleanIndex != 0)
    isVisited[arrayToClean[--toCleanIndex]] = 0;
  if (currSet.size <= tau)
    return false;

  return true;
}

inline void copyCSFromParentBackward(Graph *graph, CandidateSpace *cand_sapce, Graph *parent_graph, CandidateSpace *parent_cand_space)
{
  int8_t *pnbrsetcnt ;
  if(use_filter){
    graph->nbrsetcntpptr = (int8_t*)nbrsetcntPool.alloc();
    pnbrsetcnt = graph->nbrsetcntpptr;
  }
  
  for (int i = 0; i < graph->nVertex; ++i)
  {
    CandidateSpace &dst = cand_sapce[i];
    CandidateSpace &src = parent_cand_space[i];

    dst.size = 0;
    for (int j = 0; j < src.size; ++j)
    {
      if (src.marked[j] >= 0)
      {
        dst.candidates[dst.size] = src.candidates[j];
        dst.vertexToPos[src.candidates[j]] = dst.size;
        if(use_filter){
          copy(src.nbrcnt[j], src.nbrcnt[j] + parent_graph->degree[i], dst.nbrcnt[dst.size]);
          int v = src.candidates[j];
          dst.nbrsetcnt[dst.size] = pnbrsetcnt;
          pnbrsetcnt += currG->degree[v];
          copy(src.nbrsetcnt[j], src.nbrsetcnt[j] + currG->degree[v], dst.nbrsetcnt[dst.size]);
          copy(src.nbrsafety[j], src.nbrsafety[j] + parent_graph->degree[i], dst.nbrsafety[dst.size]);
        }
        dst.size++;        
      }
    }
  }
  if(use_filter){
    int u1 = graph->DfsCode.back().from;
    int u2 = graph->DfsCode.back().to;
    int lu1 = graph->DfsCode.back().from_label;
    int lu2 = graph->DfsCode.back().to_label;
    int qel = graph->DfsCode.back().edge_label;
    int u2pos = graph->nbrToPos[u1][u2];
    int u1pos = graph->nbrToPos[u2][u1];

    CandidateSpace &Cu1 = cand_sapce[u1];
    CandidateSpace &Cu2 = cand_sapce[u2];
    for(int j = 0; j < Cu1.size; ++j)
    {
      int v = Cu1.candidates[j];
      auto iter = currG->labelToNbrOffset.find(make_pair(v, lu2));
      if (iter == currG->labelToNbrOffset.end())
        continue;
      
      for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
      {
        int vn = currG->nbr.arr[z].first;
        int el = currG->nbr.arr[z].second;
        if (Cu2.vertexToPos[vn] != -1){
          int vnpos = Cu2.vertexToPos[vn];
          if(qel != el) continue;

          Cu2.nbrcnt[vnpos][u1pos]++;

          int idx = z - currG->nbrOffset[v];
          Cu1.nbrsetcnt[j][idx]++;
          if (Cu1.nbrsetcnt[j][idx] == 1)
          {
            Cu1.nbrsafety[j][graph->compLabelIdx[u1][u2]]++;
          }
        }
      }
      Cu1.nbrsafety[j][graph->compLabelIdx[u1][u2]] -= 1; 
    }
    for(int j = 0; j < Cu2.size; ++j)
    {
      int v = Cu2.candidates[j];
      auto iter = currG->labelToNbrOffset.find(make_pair(v, lu1));
      if (iter == currG->labelToNbrOffset.end())
        continue;
      
      for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
      {
        int vn = currG->nbr.arr[z].first;
        int el = currG->nbr.arr[z].second;
        if (Cu1.vertexToPos[vn] != -1)
        {
          int vnpos = Cu1.vertexToPos[vn];

          if(qel != el) continue;
          Cu1.nbrcnt[Cu1.vertexToPos[vn]][u2pos]++;

          int idx = z - currG->nbrOffset[v];
          Cu2.nbrsetcnt[j][idx]++;
          if (Cu2.nbrsetcnt[j][idx] == 1)
          {
            Cu2.nbrsafety[j][graph->compLabelIdx[u2][u1]]++;
          }
        }
      }
      Cu2.nbrsafety[j][graph->compLabelIdx[u2][u1]] -= 1; 
    }
  }
}

inline bool copyCSFromParentForward(Graph *graph, CandidateSpace *candSpace, Graph *parent_graph, CandidateSpace *parent_cand_space)
{  
  int8_t *pnbrsetcnt ;
  if(use_filter){
    graph->nbrsetcntpptr = (int8_t*)nbrsetcntPool.alloc();
    pnbrsetcnt = graph->nbrsetcntpptr;
  }

  for (int i = 0; i < graph->nVertex - 1; ++i)
  {
    CandidateSpace &dst = candSpace[i];
    CandidateSpace &src = parent_cand_space[i];

    for (int j = 0; j < src.size; ++j)
    {
      if (src.marked[j] >= 0)
      {
        dst.candidates[dst.size] = src.candidates[j];
        dst.vertexToPos[src.candidates[j]] = dst.size;
        if(use_filter){
          copy(src.nbrcnt[j], src.nbrcnt[j] + parent_graph->degree[i], dst.nbrcnt[dst.size]);
          int v = src.candidates[j];
          dst.nbrsetcnt[dst.size] = pnbrsetcnt;
          pnbrsetcnt += currG->degree[v];
          copy(src.nbrsetcnt[j], src.nbrsetcnt[j] + currG->degree[v], dst.nbrsetcnt[dst.size]);
          copy(src.nbrsafety[j], src.nbrsafety[j] + parent_graph->degree[i], dst.nbrsafety[dst.size]);
        }
        dst.size++;
      }
    }
  }
  unordered_map<pair<int, int>, pair<number_type, number_type>, pairHash>::const_iterator iter;

  int currVertex = graph->nVertex - 1; 
  int currLabel = graph->label[currVertex];
  char checkVal = 0; 

  int nbr = graph->DfsCode.back().from;
  CandidateSpace &nbrUnit = candSpace[nbr];
  for (int y = 0; y < nbrUnit.size; y++)
  {
    int parentCand = nbrUnit.candidates[y]; 

    iter = currG->labelToNbrOffset.find(make_pair(parentCand, currLabel));
    if (iter == currG->labelToNbrOffset.end())
      continue;
    for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
    {
      int canID = currG->nbr[z];
      if (isVisited[canID] == checkVal)
      {
        isVisited[canID]++; 
        if (checkVal == 0)
          arrayToClean[toCleanIndex++] = canID;
      }
    }
  }
  checkVal++; 

  CandidateSpace &currSet = candSpace[currVertex];
  int candIndex = 0;
  for (int checkIndex = 0; checkIndex < toCleanIndex; checkIndex++)
  {
    int canID = arrayToClean[checkIndex]; 
    if (isVisited[canID] == checkVal)
    {
      if (currG->degree[canID] < graph->degree[currVertex] || currG->core[canID] < graph->core[currVertex] || currG->maxNbrDegree[canID] < graph->maxNbrDegree[currVertex])
        continue;
      char isAdded = 1;

      for (int pos = NLFSize - 1; pos >= 0; pos--)
      {
        if (currG->NLF[canID * NLFSize + pos] != (graph->NLF[currVertex * NLFSize + pos] | currG->NLF[canID * NLFSize + pos]))
        {
          isAdded = 0;
          break;
        }
      }
      if (isAdded)
      {
        currSet.candidates[candIndex] = canID;
        candIndex++;
      }
    }
  }
  currSet.size = candIndex;
  while (toCleanIndex != 0)
    isVisited[arrayToClean[--toCleanIndex]] = 0;
  if (currSet.size <= tau)
    return false;


  if(use_filter){
    int u1 = graph->DfsCode.back().from;
    int u2 = graph->DfsCode.back().to;
    int lu1 = graph->DfsCode.back().from_label;
    int lu2 = graph->DfsCode.back().to_label;
    int qel = graph->DfsCode.back().edge_label;
    int u2pos = graph->nbrToPos[u1][u2];
    int u1pos = graph->nbrToPos[u2][u1];

    CandidateSpace &Cu1 = candSpace[u1];
    CandidateSpace &Cu2 = candSpace[u2];

    for(int j = 0; j < Cu2.size; ++j)
    {
      int v = Cu2.candidates[j];    
      Cu2.vertexToPos[v] = j;
      Cu2.nbrsetcnt[j] = pnbrsetcnt;
      pnbrsetcnt += currG->degree[v];
      memset(Cu2.nbrsetcnt[j], 0, sizeof(int8_t) * currG->degree[v]);
    }

    for(int j = 0; j < Cu1.size; ++j)
    {
      int v = Cu1.candidates[j];
      auto iter = currG->labelToNbrOffset.find(make_pair(v, lu2));
      if (iter == currG->labelToNbrOffset.end())
        continue;
      
      for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
      {
        int vn = currG->nbr.arr[z].first;
        int el = currG->nbr.arr[z].second;
        if (Cu2.vertexToPos[vn] != -1){
          int vnpos = Cu2.vertexToPos[vn];
          if(qel != el) continue;
          Cu2.nbrcnt[vnpos][u1pos]++;

          int idx = z - currG->nbrOffset[v];
          Cu1.nbrsetcnt[j][idx]++;
          if (Cu1.nbrsetcnt[j][idx] == 1)
          {
            Cu1.nbrsafety[j][graph->compLabelIdx[u1][u2]]++;
          }
        }
      }
      Cu1.nbrsafety[j][graph->compLabelIdx[u1][u2]] -= 1; 
    }
    for(int j = 0; j < Cu2.size; ++j)
    {
      int v = Cu2.candidates[j];
      auto iter = currG->labelToNbrOffset.find(make_pair(v, lu1));
      if (iter == currG->labelToNbrOffset.end())
        continue;
      
      for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
      {
        int vn = currG->nbr.arr[z].first;
        int el = currG->nbr.arr[z].second;
        if (Cu1.vertexToPos[vn] != -1)
        {
          int vnpos = Cu1.vertexToPos[vn];
          if(qel != el) continue;

          Cu1.nbrcnt[Cu1.vertexToPos[vn]][u2pos]++;

          int idx = z - currG->nbrOffset[v];
          Cu2.nbrsetcnt[j][idx]++;
          if (Cu2.nbrsetcnt[j][idx] == 1)
          {
            Cu2.nbrsafety[j][graph->compLabelIdx[u2][u1]]++;
          }
        }
      }
      Cu2.nbrsafety[j][graph->compLabelIdx[u2][u1]] -= 1; 
    }
  }
  return true;
}

inline bool BuildCSFromEdge(Graph *graph, CandidateSpace *&cand_space)
{
  if (!FilterByCount(*graph, *currG))
    return false;
    graph->nNonLeaf = graph->nVertex;

  AllocateForCandidateSet(*graph, cand_space);

  if (!buildCSEdge(*graph, *currG, cand_space))
    return false;

  if(use_filter){
    BuildNbrCnt(*graph, *currG, cand_space);

    if (!CSnodeFiltering(*graph, *currG, cand_space))
		  return false;
  }
  return true;
}
inline bool BuildCSForward(Graph *graph, CandidateSpace *&cand_space, Graph *parent_graph, CandidateSpace *parent_cand_space)
{
  if (!FilterByCount(*graph, *currG))
    return false;

  graph->nNonLeaf = graph->nVertex;

  AllocateForCandidateSet(*graph, cand_space);

  if (!copyCSFromParentForward(graph, cand_space, parent_graph, parent_cand_space)){
    return false;
  }  
  
  if(use_filter){
    if (!CSnodeFiltering(*graph, *currG, cand_space))
      return false;
  }
  return true;
}

inline bool BuildCSBackward(Graph *graph, CandidateSpace *&cand_space, Graph *parent_graph, CandidateSpace *parent_cand_space)
{
  if (!FilterByCount(*graph, *currG))
    return false; 

  graph->nNonLeaf = graph->nVertex;

  AllocateForCandidateSet(*graph, cand_space);
  copyCSFromParentBackward(graph, cand_space, parent_graph, parent_cand_space);

  if(use_filter){
    if (!CSnodeFiltering(*graph, *currG, cand_space))
      return false;
  }
  return true;
}

int computeUB(Graph *graph, CandidateSpace *candSpace)
{
  int mni = maxNumDataVertex;

  for (int u = 0; u < graph->nVertex; ++u)
  {    
    int image_size = 0;
    CandidateSpace &currSet = candSpace[u];

    image_size = currSet.size;
    mni = min(mni, image_size);
  }
  return mni;
}

inline bool isInFreqEdge(int l1, int edge_label, int l2)
{
  for (int i = freq_edge_offset[l1]; i < freq_edge_offset[l1 + 1]; ++i)
  {
    if (get<1>(freq_edge[i]) == edge_label && get<2>(freq_edge[i]) == l2)
    {
      if(get<0>(freq_edge[i]) <= tau)
        return false;
      return true;
    }
  }
  return false;
}

void Extension(priority_queue<HeapElement> &graph_set, Graph *parent_graph, CandidateSpace *parent_candSpace, int parent_mni)
{
  Graph *graph;
  for (int rmpnode = 0; rmpnode < parent_graph->rmpSize; ++rmpnode)
  {
    int node = parent_graph->right_most_path[rmpnode];
    int min_label = parent_graph->label[parent_graph->right_most_path[parent_graph->rmpSize - 1]];

    for (int fidx = freq_edge_offset[parent_graph->label[node]]; fidx < freq_edge_offset[parent_graph->label[node] + 1]; ++fidx)
    {
      int edge_mni = get<0>(freq_edge[fidx]);
      int edge_label = get<1>(freq_edge[fidx]);
      int new_label = get<2>(freq_edge[fidx]);
      if (new_label < min_label)
        continue;

      if(edge_mni <= tau)
        break;
      createSubgraph(graph, parent_graph, true, new_label, edge_label, node, parent_graph->nVertex);
      if (!is_min(graph))
      {
        delete graph;
        continue;
      }

      CandidateSpace *cand_space = NULL;
      currQ = graph;

      AllocateForSubgraph(*graph);
      GetQueryDataStructure(*graph);

      cand_space = NULL;
      bool isCandidate = BuildCSForward(graph, cand_space, parent_graph, parent_candSpace);
      
      if (!isCandidate)
      {
        if (cand_space != NULL)
        {
          DeallocateCS(*graph, cand_space);
          delete[] cand_space;
        }
        Deallocate(*graph);
        delete graph;
        continue;
      }

      int ub = computeUB(graph, cand_space);

      if (ub <= tau)
      {
        DeallocateCS(*graph, cand_space);
        Deallocate(*graph);
        delete[] cand_space;
        delete graph;
        continue;
      }

      graph_set.push(HeapElement(ub, graph->nVertex, false, graph, cand_space));
    }
  }

  for (int rmpnode = parent_graph->rmpSize - 1; rmpnode > 0; --rmpnode)
  {
	bool avail = true;
	int first = parent_graph->right_most_path[0];
	int second = parent_graph->right_most_path[rmpnode];
	for (int i = parent_graph->nbrOffset[second]; i < parent_graph->nbrOffset[second + 1]; ++i)
	{
    if (first == parent_graph->nbr[i])
    {
      avail = false;
      break;
    }
	}
	if(!avail)
			continue;

  for (int edge_label = 0; edge_label < nUniqueEdgeLabel; edge_label++)
  {
    if (!isInFreqEdge(parent_graph->label[first], edge_label, parent_graph->label[second]))
      continue;

      createSubgraph(graph, parent_graph, false, 0, edge_label, first, second);
      if (!is_min(graph))
      {
        delete graph;
        continue;
      }
      CandidateSpace *cand_space = NULL;

      currQ = graph;

      AllocateForSubgraph(*graph);
      GetQueryDataStructure(*graph);

      cand_space = NULL;
      bool isCandidate = BuildCSBackward(graph, cand_space, parent_graph, parent_candSpace);

      if (!isCandidate)
      {
        if (cand_space != NULL)
        {
          DeallocateCS(*graph, cand_space);
          delete[] cand_space;
        }
        Deallocate(*graph);
        delete graph;
        continue;
      }

      int ub = computeUB(graph, cand_space);


      if (ub <= tau)
      {
        DeallocateCS(*graph, cand_space);
        Deallocate(*graph);
        delete[] cand_space;
        delete graph;
        continue;
      }
      graph_set.push(HeapElement(ub, graph->nVertex, true, graph, cand_space));
    }

  }
}

void ExtensionEdge(priority_queue<HeapElement> &graph_set, Graph *parent_graph, int parent_mni)
{
  Graph *graph;
  // Forward Edge
  for (int rmpnode = 0; rmpnode < parent_graph->rmpSize; ++rmpnode)
  {
    int node = parent_graph->right_most_path[rmpnode];
    int min_label = parent_graph->label[parent_graph->right_most_path[parent_graph->rmpSize - 1]];
    for (int fidx = freq_edge_offset[parent_graph->label[node]]; fidx < freq_edge_offset[parent_graph->label[node] + 1]; ++fidx)
    {
      int new_label = get<2>(freq_edge[fidx]);
      int edge_label = get<1>(freq_edge[fidx]);
      if (new_label < min_label)
        continue;
      createSubgraph(graph, parent_graph, true, new_label, edge_label, node, parent_graph->nVertex);
      if (!is_min(graph))
      {
        delete graph;
        continue;
      }
      CandidateSpace *cand_space = NULL;

      currQ = graph;

      AllocateForSubgraph(*graph);
      GetQueryDataStructure(*graph);

      cand_space = NULL;

      bool isCandidate = BuildCSFromEdge(graph, cand_space);

      if (!isCandidate)
      {
        if (cand_space != NULL)
        {
          DeallocateCS(*graph, cand_space);
          delete[] cand_space;
        }
        Deallocate(*graph);
        delete graph;
        continue;
      }

      int ub = computeUB(graph, cand_space);
      if (ub <= tau)
      {
        DeallocateCS(*graph, cand_space);
        Deallocate(*graph);
        delete[] cand_space;
        delete graph;
        continue;
      }

      graph_set.push(HeapElement(ub, graph->nVertex, false, graph, cand_space));
    }
  }
}


bool build_and_compare_dfs_code(const Graph *graph, int *renumbering, int *renumbering_inverse, int cur_node_num, int cur_dfs_code_length, std::stack<int> s)
{
  if (s.empty())
  {
    return true;
  }

  int node = s.top();
  bool onlyleaf = true;
  int samelable[MAX_NUM_VERTEX];

  pair<int, int> minLabel = make_pair(MAX_LABEL, MAX_LABEL); // (edge_label, to_label)

  for (int i = graph->nbrOffset[node]; i < graph->nbrOffset[node + 1]; ++i)
  {
    if (renumbering[graph->nbr.arr[i].first] == -1)
    {
      pair<int, int> p = make_pair(graph->nbr.arr[i].second, graph->label[graph->nbr.arr[i].first]);
      if (minLabel > p){
        minLabel = p;
        onlyleaf = true;
        if (graph->degree[graph->nbr.arr[i].first] != 1)
          onlyleaf = false;
      }
      else if (minLabel == p){
        if (graph->degree[graph->nbr.arr[i].first] != 1)
          onlyleaf = false;
      }
    }
  }
  if (minLabel == make_pair(MAX_LABEL, MAX_LABEL))
  {
    s.pop();
    return build_and_compare_dfs_code(graph, renumbering, renumbering_inverse, cur_node_num, cur_dfs_code_length, s);
  }

  bool ret = true;
  int _renumbering[MAX_NUM_VERTEX]; 
  int _renumbering_inverse[MAX_NUM_VERTEX];
  int _cur_node_num, _cur_dfs_code_length;
  std::stack<int> _s;
  copy(renumbering, renumbering + graph->nVertex, _renumbering);
  copy(renumbering_inverse, renumbering_inverse + graph->nVertex, _renumbering_inverse);
  _cur_node_num = cur_node_num;
  _cur_dfs_code_length = cur_dfs_code_length;
  _s = s;
  
  if (onlyleaf)
  {
    int num_leaf = 0;
    for (int i = graph->nbrOffset[node]; i < graph->nbrOffset[node + 1]; ++i)
    {
      if (renumbering[graph->nbr.arr[i].first] == -1)
      {
        pair<int, int> p = make_pair(graph->nbr.arr[i].second, graph->label[graph->nbr.arr[i].first]);     
        if (minLabel == p){
          if (graph->degree[graph->nbr.arr[i].first] == 1){          
            samelable[num_leaf] = graph->nbr.arr[i].first;
            ++num_leaf;
          }
        }        
      }
    }  

    for (int i = 0; i < num_leaf; ++i)
    {
      int neighbor = samelable[i];
      _renumbering[neighbor] = _cur_node_num;
      _renumbering_inverse[_cur_node_num] = neighbor;
      _cur_node_num++;
      vector<dfs_code_t> codes;
      int edge_label = minLabel.first;
      dfs_code_t forward_code(_renumbering[node], _renumbering[neighbor], graph->label[node], edge_label, graph->label[neighbor]);

      if ((graph->DfsCode[_cur_dfs_code_length]) < forward_code)
      {
        return true;
      }
      else if (forward_code < (graph->DfsCode[_cur_dfs_code_length]))
      {
        return false;
      }
      else
        ++_cur_dfs_code_length;
    }
        
    if (!build_and_compare_dfs_code(graph, _renumbering, _renumbering_inverse, _cur_node_num, _cur_dfs_code_length, _s))
      return false;

    for (int i = 0; i < num_leaf; ++i)
    {
      int neighbor = samelable[i];
      _renumbering[neighbor] = -1;
      _renumbering_inverse[_cur_node_num] = -1;
      --_cur_node_num;
      --_cur_dfs_code_length;
    }
    return true;
  }

  for (int i = graph->nbrOffset[node]; i < graph->nbrOffset[node + 1]; ++i)
  {
    int neighbor = graph->nbr.arr[i].first;
    int edge_label = graph->nbr.arr[i].second;

    if (edge_label == minLabel.first && graph->label[neighbor] == minLabel.second && _renumbering[neighbor] == -1)
    {

      _renumbering[neighbor] = _cur_node_num;
      _renumbering_inverse[_cur_node_num] = neighbor;
      _cur_node_num++;
      vector<dfs_code_t> codes;
      dfs_code_t forward_code(_renumbering[node], _renumbering[neighbor], graph->label[node], edge_label, graph->label[neighbor]);
      
      codes.emplace_back(forward_code);
      for (int i = 0; i < _cur_node_num; i++)
      {
        if (_renumbering_inverse[i] != -1 && _renumbering_inverse[i] != node)
        {
          int n = _renumbering_inverse[i];
          for (int j = graph->nbrOffset[n]; j < graph->nbrOffset[n + 1]; ++j)
          {
            if (graph->nbr.arr[j].first == neighbor)
            {
              dfs_code_t backward_code(_renumbering[neighbor], _renumbering[n], graph->label[neighbor], graph->nbr.arr[j].second, graph->label[n]);
              
              codes.emplace_back(backward_code);
              break;
            }
          }
        }
      }

      for (const auto c : codes)
      { 

        if ((graph->DfsCode[_cur_dfs_code_length]) < c)
        {
          return true;
        }
        else if (c < (graph->DfsCode[_cur_dfs_code_length]))
        {
          return false;
        }
        else
          _cur_dfs_code_length++;
      }
      _s.push(neighbor);
      if (!build_and_compare_dfs_code(graph, _renumbering, _renumbering_inverse, _cur_node_num, _cur_dfs_code_length, _s))
        return false;

      _s.pop();
      _renumbering[neighbor] = -1;
      _renumbering_inverse[_cur_node_num] = -1;
      --_cur_node_num;
      _cur_dfs_code_length = cur_dfs_code_length;
    }
  }
  return ret;
}

bool is_min(Graph *graph)
{
  int minLabel = MAX_LABEL;
  for (int i = 0; i < graph->nVertex; i++)
  {
    minLabel = min(minLabel, graph->label[i]);
  }
  for (int i = 0; i < graph->nVertex; i++)
  {
    if (graph->label[i] == minLabel)
    {
      int renumbering[graph->nVertex];
      int renumbering_inverse[graph->nVertex];
      memset(renumbering, -1, sizeof(renumbering));
      memset(renumbering_inverse, -1, sizeof(renumbering_inverse));
      renumbering[i] = 0;
      renumbering_inverse[0] = i;
      std::stack<int> s;
      s.push(i);
      if (!build_and_compare_dfs_code(graph, renumbering, renumbering_inverse, 1, 0, s))
        return false;
    }
  }
  return true;
}

