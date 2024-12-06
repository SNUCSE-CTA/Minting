#include <utility>
#include <cstring>
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <iostream>
#include <map>
#include "config.h"

using namespace std;

int *cntLabel;
int *positiveLabel;

vector<tuple<int, int, int, int>> freq_edge_set;
tuple<int, int, int> *freq_edge;

int *freq_edge_offset;
bool use_filter;

struct pairHash
{
  size_t operator()(const pair<int, int> &p) const
  {
    return p.first ^ p.second;
  }
};

struct uvHash
{
	size_t operator()(const pair<int, int> &p) const
	{
		return p.first * (1 << 24) + p.second;
	}
};

class PairArray
{
public:
  pair<int, int> *arr;
  PairArray() {}
  PairArray(int size) { arr = new pair<int, int>[size]; }
  inline int operator[](const int idx) const
  {
    return arr[idx].first;
  }
  inline pair<int, int> &get(const int idx)
  {
    return arr[idx];
  }
  inline void set(int idx, int fst, int snd)
  {
    arr[idx] = make_pair(fst, snd);
  }
  inline void set(int idx, int fst)
  {
    arr[idx].first = fst;
  }
};

// dfs codes forward and backward compare
struct dfs_code_t
{
  dfs_code_t() : from(0), to(0), from_label(0), edge_label(0), to_label(0)
  {
  }


  dfs_code_t(int from, int to, int from_label, int edge_label, int to_label) : from(from), to(to),
                                                                               from_label(from_label), edge_label(edge_label), to_label(to_label)
  {
  }


  dfs_code_t(const dfs_code_t &other)
  {
    this->from = other.from;
    this->to = other.to;
    this->from_label = other.from_label;
    this->edge_label = other.edge_label;
    this->to_label = other.to_label;
  }

  bool operator!=(const dfs_code_t &t) const
  {
    return (from != t.from) || (to != t.to) ||
           (from_label != t.from_label) || (to_label != t.to_label) || (edge_label != t.edge_label);
  }

  bool operator==(const dfs_code_t &t) const
  {
    return (from == t.from) && (to == t.to) &&
           (from_label == t.from_label) && (to_label == t.to_label) && (edge_label == t.edge_label);
  }

  bool operator<(const dfs_code_t &t) const
  {
    bool forward_first = from < to;
    bool forward_second = t.from < t.to;
    if (!forward_first && forward_second)
      return true;
    if (forward_first && !forward_second)
      return false;
    if (forward_first && forward_second)
    {
      if (from != t.from)
      {
        return from > t.from;
      }
      else
      {
        if (from_label != t.from_label)
        {
          return from_label < t.from_label;
        }
        else
        {
          if (edge_label != t.edge_label)
          {
            return edge_label < t.edge_label;
          }
        }
      }
      return to_label < t.to_label;
    }
    if (!forward_first && !forward_second)
    {
      if (to != t.to)
      {
        return to < t.to;
      }
      else
      {
        if (edge_label != t.edge_label)
        {
          return edge_label < t.edge_label;
        }
      }
    }
    return false;
  }


  void printEdge(unordered_map<int, string> labelMap_inverse, unordered_map<int, int> edgelabelMap_inverse, ostream &os = cout) const

  {
    os << "( " << from << ", " << to << ", " << labelMap_inverse.find(from_label)->second << ", " << edgelabelMap_inverse.find(edge_label)->second << ", " << labelMap_inverse.find(to_label)->second << " )" << endl;
  }

  int from;
  int to;
  int from_label;
  int edge_label;
  int to_label;
};
typedef vector<dfs_code_t> DfsCodes;


int **invnbr;
class Graph
{
public:
  number_type nVertex;
  number_type nEdge;
  int nLabel;
  int maxDegree;
  int *label;
  PairArray nbr;
  int maxEdgeLabel;

  number_type *nbrOffset;
  int *degree;
  int *vertex; 
  int *vertexOffset;
  int *maxNbrDegree;

  uint64_t *NLF;
  unordered_map<int, int> labelFrequency; 

  unordered_map<pair<int, int>, pair<number_type, number_type>, pairHash> labelToNbrOffset; 

  int mostFrequentLabelID;
  int maxNumSameLabelVertex;

  int nNonLeaf;
  int *core;
  bool *isProblemLeaf;
  int **nbrqsafety;
  int **compLabelIdx;
  int **nbrToPos;
  
  int *nbrcntpptr = NULL;
  int8_t *nbrsetcntpptr = NULL;
  int *nbrsafetypptr = NULL;

  int *right_most_path; // Right Most Path
  int rmpSize;          // Length of right-most path
#ifdef AUTOMORPHISM
  vector<vector<int>> classes;
  vector<int> classes_mapping;
#endif
  DfsCodes DfsCode;

  Graph()
  {
    nVertex = 0;
    nEdge = 0;
    nLabel = 0;
    maxDegree = 0;

    label = NULL;
    maxEdgeLabel = 0;
    nbrOffset = NULL;
    core = NULL;
    degree = NULL;
    vertex = NULL;       
    vertexOffset = NULL; 
    maxNbrDegree = NULL;
    NLF = NULL;

    right_most_path = NULL;
    rmpSize = 0;
  }

  ~Graph()
  {
    delete[] label;
    delete[] degree;
    delete[] vertex;
    delete[] vertexOffset;
    delete[] maxNbrDegree;
    delete[] NLF;
    delete[] nbrOffset;
    labelFrequency.clear();

    delete[] right_most_path;

    delete[] core;
    DfsCode.clear();
  }

  inline void initVertex(const number_type n)
  {
    nVertex = n;
    label = new int[nVertex];
    nbrOffset = new number_type[nVertex + 1];
    core = new int[nVertex];
    degree = new int[nVertex]();
    vertex = new int[nVertex];
    maxNbrDegree = new int[nVertex]();

    right_most_path = new int[nVertex];
    nbrToPos = new int*[nVertex];
  }

  inline void initEdge(const number_type n)
  {
    nEdge = n;
    nbr = PairArray(nEdge * 2);
  }

  inline void sortNeighbors()
  {
    int prev, curr;
    number_type currCnt, currIndex;
 
    vertexOffset = new int[nUniqueLabel + 1](); 

    for (int i = 0; i < nVertex; ++i)
    {
      ++vertexOffset[label[i]];
      if (degree[i] == 0)
        continue;

      sort(
          nbr.arr + nbrOffset[i],
          nbr.arr + nbrOffset[i + 1],
          [this](const pair<int, int> &p1, const pair<int, int> &p2) -> bool
          {
            if (label[p1.first] == label[p2.first])
              if (degree[p1.first] == degree[p2.first])
                return p1.first < p2.first;
              else
                return (degree[p1.first] < degree[p2.first]);
            else
              return (label[p1.first] < label[p2.first]);
          }
      );
      currCnt = 1;
      currIndex = nbrOffset[i];
      prev = label[nbr[currIndex]];
      if (degree[i] > 1)
      {
        number_type j = nbrOffset[i];
        for (j = nbrOffset[i] + 1; j < nbrOffset[i + 1]; ++j)
        {
          curr = label[nbr[j]];
          if (prev == curr)
          {
            ++currCnt;
            continue;
          }
          else
          {
            labelToNbrOffset[make_pair(i, prev)] = make_pair(currIndex, currCnt);
            currIndex += currCnt;
            prev = curr;
            currCnt = 1;
          }
        }
        labelToNbrOffset[make_pair(i, prev)] = make_pair(currIndex, currCnt);
        continue;
      }
      else
      {
        labelToNbrOffset[make_pair(i, prev)] = make_pair(currIndex, currCnt);
      }
    }

    curr = vertexOffset[0];
    vertexOffset[0] = 0;
    for (int i = 1; i <= nUniqueLabel; ++i)
    {
      prev = vertexOffset[i];
      vertexOffset[i] = vertexOffset[i - 1] + curr;
      curr = prev;
    }
    for (int i = 0; i < nVertex; ++i)
    {
      vertex[vertexOffset[label[i]]++] = i;
    }
    for (int i = nUniqueLabel; i >= 1; --i)
    {
      vertexOffset[i] = vertexOffset[i - 1];
    }
    vertexOffset[0] = 0;
    for (int i = 0; i < nUniqueLabel; ++i)
    {
      sort(
          vertex + vertexOffset[i],
          vertex + vertexOffset[i + 1],
          [this](const int &v1, const int &v2) -> bool
          {
            if (degree[v1] == degree[v2])
              return v1 < v2;
            else
              return (degree[v1] < degree[v2]);
          });
    }
  }

  inline void computeNLF()
  {
    int lid, nPositive = 0;

    NLF = new uint64_t[(long long)nVertex * (long long)NLFSize]();
    memset(cntLabel, 0, sizeof(int) * nUniqueLabel);
    for (int j = 0; j < nVertex; ++j)
    {
      if (degree[j] == 0)
        continue;
      for (number_type k = nbrOffset[j]; k < nbrOffset[j + 1]; ++k)
      {
        int neighbor = nbr[k];

        if (degree[neighbor] > maxNbrDegree[j])
          maxNbrDegree[j] = degree[neighbor];

        lid = label[neighbor];

        if (cntLabel[lid] == 0)
          positiveLabel[nPositive++] = lid;
        if (cntLabel[lid] < BITS_PER_LABEL)
        {
          int start = lid * BITS_PER_LABEL;
          int idx = NLFSize - 1 - (start + cntLabel[lid]) / UINT64_SIZE;
          int pos = (start + cntLabel[lid]) % UINT64_SIZE;

          NLF[j * NLFSize + idx] |= (1ULL << pos);
          ++cntLabel[lid];
        }
      }

      while (nPositive > 0)
        cntLabel[positiveLabel[--nPositive]] = 0;
    }
  }

  void printGraph(unordered_map<int, string> m, unordered_map<int, int> em, ostream &os = cout)  
  {
    for (int i = 0; i < nVertex; ++i)
    {
      assert(nbrOffset[i] < nbrOffset[i + 1]);
      os << i << " [" << m.find(label[i])->second << "] ";
      for (int j = nbrOffset[i]; j < nbrOffset[i + 1]; ++j)
      {
        os << nbr.arr[j].first << " ";
      }
      os << endl;
    }
    for (auto p : DfsCode)
    {
      p.printEdge(m, em, os);
    }
  }

  inline void computeNbrSafety()
  {
    map<pair<int, int>, int> vis;
    for(int u = 0; u < nVertex; ++u)
    {
      vis.clear();
      for (int j = nbrOffset[u]; j < nbrOffset[u + 1]; ++j)
      {
        int un = nbr.arr[j].first;
        int qel = nbr.arr[j].second;

        int lun = label[un];
        if (vis.find(make_pair(lun, qel)) == vis.end())
        {
          vis[make_pair(lun, qel)] = vis.size();
        }
        compLabelIdx[u][un] = vis[make_pair(lun, qel)];
        nbrqsafety[u][compLabelIdx[u][un]]++;

      }
    }
  }

};
