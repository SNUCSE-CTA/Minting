#include <iostream>
#include <fstream>
#include <chrono>
#include <tuple>
#include <unordered_map>
#include "graph.h"
using namespace std;

Graph *currG;
int nGraph;
int maxNumCandidate = 0;
int maxDegree = 0;
int maxNumDataVertex = 0;

struct tupleHash
{
	size_t operator()(const tuple<int, int, int> &x) const
	{
		return get<0>(x) * (1<<18) + get<1>(x) * (1<<6) + get<2>(x);
	}
};
int edge_list_num = 0;
unordered_map<tuple<int, int, int>, int , tupleHash> edge_list;
vector<Graph *> dataGraph;
#ifdef COREBASED
vector<Graph *> coreGraph;
#endif
unordered_map<string, int> labelMap; 
unordered_map<int, string> labelMap_inverse;
unordered_map<int, int> edgelabelMap; 
unordered_map<int, int> edgelabelMap_inverse;

Graph *currQ;
int nQueryVertex = 0;
vector<Graph *> queryGraph;
int *mapTo;
bool isMapped[MAX_NUM_VERTEX];
int extendable[MAX_NUM_VERTEX];
int arrForQuery[MAX_NUM_VERTEX];
int binQuery[MAX_NUM_VERTEX];
int posQuery[MAX_NUM_VERTEX];
int vertQuery[MAX_NUM_VERTEX];

chrono::high_resolution_clock::time_point GetClock()
{
  return chrono::high_resolution_clock::now();
}
double TimeDiffInMilliseconds(const chrono::high_resolution_clock::time_point start, const chrono::high_resolution_clock::time_point end)
{
  chrono::duration<double> durationDiff = end - start;
  return durationDiff.count() * 1000;
}

inline void ReadGFUFormat(const string &graphFile, vector<Graph *> &graphList)
{
  ifstream inFile(graphFile);
  if (!inFile)
  {
    cout << "Failed to open a data graph file " << graphFile << endl;
    exit(1);
  }

  Graph *graph = NULL;
  vector<tuple<int, int, int>> edges;
  string line;
  number_type pos, numVertex, numEdge;
  int fst, snd, labelID;
  int cntVertex = 0, state = Start;
  unordered_map<string, int>::const_iterator sIter;
  unordered_map<int, int>::const_iterator iIter;
  while (!inFile.eof())
  {
    switch (state)
    {
    case Start:
    {
      inFile >> line;
      if (inFile.eof())
        break;
      graph = new Graph();
      graphList.push_back(graph);
      cntVertex = 0;
      edges.clear();
      state = LoadNumVertex;
      break;
    }
    case LoadNumVertex:
    {
      inFile >> numVertex;
      graph->initVertex(numVertex);  
      state = LoadVertex;
      break;
    }
    case LoadVertex:
    {
      inFile >> line;
      sIter = labelMap.find(line);
      if (sIter != labelMap.end())
      {
        labelID = sIter->second;
      }
      else
      {
        labelID = labelMap.size();
        labelMap[line] = labelID;
        labelMap_inverse[labelID] = line;
      }
      iIter = graph->labelFrequency.find(labelID);
      if (iIter != graph->labelFrequency.end())
      {
        graph->labelFrequency[labelID] += 1;
      }
      else
      {
        graph->labelFrequency[labelID] = 1;
      }
      graph->label[cntVertex] = labelID;
      ++cntVertex;
      if (cntVertex >= graph->nVertex)
        state = LoadNumEdge;
      break;
    }
    case LoadNumEdge:
    {
      inFile >> numEdge;
      graph->initEdge(numEdge); 
      graph->nLabel = labelMap.size();
      edges.reserve(numEdge);
      state = LoadEdge;
      break;
    }
    case LoadEdge:
    {
      int edgelabelID;
      unordered_map<int, int>::const_iterator sIter;
      inFile >> fst >> snd >> labelID;
      sIter = edgelabelMap.find(labelID);
      if (sIter != edgelabelMap.end())
      {
        edgelabelID = sIter->second;
      }
      else
      {
        edgelabelID = edgelabelMap.size();
        edgelabelMap[labelID] = edgelabelID;
        edgelabelMap_inverse[edgelabelID] = labelID;
      }
      edges.push_back(make_tuple(fst, snd, edgelabelID));
      int a = min(graph->label[fst], graph->label[snd]);
      int b = max(graph->label[fst], graph->label[snd]);
      if(edge_list.find({a, b, edgelabelID}) == edge_list.end()){
	      edge_list[{a, b, edgelabelID}] = edge_list_num++;
      }
	
      graph->maxEdgeLabel = std::max(graph->maxEdgeLabel, edgelabelID+1);

      graph->degree[fst] += 1;
      graph->degree[snd] += 1;
      if (edges.size() >= graph->nEdge)
      {
        pos = 0;
        for (int i = 0; i < graph->nVertex; ++i)
        {
          graph->nbrOffset[i] = pos;
          pos += (number_type)graph->degree[i];
          graph->core[i] = graph->degree[i];
          if (graph->degree[i] > graph->maxDegree)
            graph->maxDegree = graph->degree[i];
        }
        graph->nbrOffset[graph->nVertex] = pos;
        memset(graph->degree, 0, sizeof(int) * graph->nVertex);
        for (int i = 0; i < edges.size(); ++i)
        {
          fst = std::get<0>(edges[i]);
          snd = std::get<1>(edges[i]);
          labelID = std::get<2>(edges[i]);
          graph->nbr.set(graph->nbrOffset[fst] + graph->degree[fst], snd, labelID);
          graph->nbr.set(graph->nbrOffset[snd] + graph->degree[snd], fst, labelID);
          graph->degree[fst] += 1;
          graph->degree[snd] += 1;
        }
        state = Start;
      }
      break;
    }
    default:
    {
      exit(1);
    }
    }
  }
  inFile.close();
  edges.clear();
}


inline void ProcessDataGraphs()
{
  int start, num, maxValue;
  unordered_map<int, int>::const_iterator lit;
  nGraph = dataGraph.size();
  nUniqueLabel = labelMap.size();
  nUniqueEdgeLabel = edgelabelMap.size();

  use_filter = (double)dataGraph[0]->nEdge / (double)dataGraph[0]->nVertex >= filter_th;
  NLFSize = (BITS_PER_LABEL * nUniqueLabel - 1) / UINT64_SIZE + 1;

  for (int i = 0; i < dataGraph.size(); ++i)
  {
    Graph &g = *dataGraph[i];
    if (g.maxDegree > maxDegree)
      maxDegree = g.maxDegree;
    if (g.nVertex > maxNumDataVertex)
      maxNumDataVertex = g.nVertex;
  }
  positiveLabel = new int[nUniqueLabel];
  cntLabel = new int[nUniqueLabel]();
  int *bin = new int[maxDegree + 1];
  int *pos = new int[maxNumDataVertex];
  int *vert = new int[maxNumDataVertex];

  for (int i = 0; i < dataGraph.size(); ++i)
  {
    start = 0;
    maxValue = 0;
    memset(bin, 0, sizeof(int) * (maxDegree + 1));
    Graph &g = *dataGraph[i];
    for (lit = g.labelFrequency.begin(); lit != g.labelFrequency.end(); ++lit)
    {
      if (lit->second > maxValue)
      {
        g.mostFrequentLabelID = lit->first;
        maxValue = lit->second;
      }
    }
    g.maxNumSameLabelVertex = maxValue;
    if (maxValue > maxNumCandidate)
      maxNumCandidate = maxValue;

    for (int i = 0; i < g.nVertex; i++)
      bin[g.core[i]]++;

    for (int d = 0; d <= g.maxDegree; d++)
    {
      num = bin[d];
      bin[d] = start;
      start += num;
    }
    for (int i = 0; i < g.nVertex; i++)
    {
      pos[i] = bin[g.core[i]];
      vert[pos[i]] = i;
      bin[g.core[i]]++;
    }
    for (int d = g.maxDegree; d > 0; d--)
      bin[d] = bin[d - 1];
    bin[0] = 0;

    for (int i = 0; i < g.nVertex; i++)
    {
      int v = vert[i];
      for (number_type j = g.nbrOffset[v]; j < g.nbrOffset[v + 1]; j++)
      {
        int u = g.nbr[j];
        if (g.core[u] > g.core[v])
        {
          int du = g.core[u];
          int pu = pos[u];
          int pw = bin[du];
          int w = vert[pw];
          if (u != w)
          {  
            pos[u] = pw;
            pos[w] = pu;
            vert[pu] = w;
            vert[pw] = u;
          }
          bin[du]++;
          g.core[u]--;
        }
      }
    }
    g.sortNeighbors();
    g.computeNLF();
  }
  delete[] bin;
  delete[] pos;
  delete[] vert;
  
  Graph &g = *dataGraph[0];
  invnbr = new int *[maxNumDataVertex];
  for (int i = 0; i < maxNumDataVertex; ++i){
    invnbr[i] = new int[g.degree[i]];
  }
  int *curridx = new int[maxNumDataVertex];
  memset(curridx, 0, sizeof(int)*maxNumDataVertex);
  for (int i = 0; i < g.nVertex; i++)
  {    
    int v = g.vertex[i];
    for (number_type j = g.nbrOffset[v]; j < g.nbrOffset[v + 1]; j++)
    {
      int vn = g.nbr[j];
      int jdx = j - g.nbrOffset[v];
      invnbr[v][jdx] = curridx[vn];
      curridx[vn]++;
    }
  }    
}

inline void GetQueryDataStructure(Graph &query)
{
  int *pos = posQuery;    
  int *vert = vertQuery; 
  int *bin = binQuery;   
  memset(bin, 0, sizeof(int) * (query.maxDegree + 1));
  for (int i = 0; i < nQueryVertex; i++)
    bin[query.core[i]]++;

  int num, start = 0;
  for (int d = 0; d <= query.maxDegree; d++)
  {
    num = bin[d];
    bin[d] = start;
    start += num;
  }
  for (int i = 0; i < nQueryVertex; i++)
  {
    pos[i] = bin[query.core[i]];
    vert[pos[i]] = i;
    bin[query.core[i]]++;
  }

  for (int d = query.maxDegree; d > 0; d--)
    bin[d] = bin[d - 1];
  bin[0] = 0;


  for (int i = 0; i < nQueryVertex; i++)
  {
    int v = vert[i];
    for (number_type j = query.nbrOffset[v]; j < query.nbrOffset[v + 1]; j++)
    {
      int u = query.nbr[j];
      if (query.core[u] > query.core[v])
      {
        int du = query.core[u];
        int pu = pos[u];
        int pw = bin[du];
        int w = vert[pw];
        if (u != w)
        {
          pos[u] = pw;
          pos[w] = pu;
          vert[pu] = w;
          vert[pw] = u;
        }
        bin[du]++;
        query.core[u]--;
      }
    }
  }
  query.computeNLF();
  query.computeNbrSafety();
}


