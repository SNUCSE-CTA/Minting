#include <vector>
#include <cfloat>
#include <cassert>
#include <climits>
#include <bitset>
#include "process.h"
#include "mempool.h"
#include <iomanip>
#include <unordered_set>

#ifdef AUTOMORPHISM
#include "traces/nauty2_8_6/nauty.h"
#include "traces/nauty2_8_6/naugroup.h"
#include "traces/nauty2_8_6/naututil.h"
#endif
// for using Automorphism:
// 1. Requires the nauty&Traces.
// 2. Add the -DAUTOMORPHISM option when compiling.

using namespace std;

int tau;
int* mark1_vertex;




long long failed_cnt, total_cnt;

int CS_M[MAX_NUM_VERTEX];
int CS_C[MAX_NUM_VERTEX];
int CS_CIDX[MAX_NUM_VERTEX];

bool *answer;
int nCandidate = 0;

long long int recursiveCallCount = 0;
long long int recursiveCallCountPerGraph;
bool exceedTimeLimit;
chrono::high_resolution_clock::time_point startPoint, endPoint;

long long int quotient, lastQuotient;
double elapsedTime;
const double timeLimit = 600000;

string dataGraphFile;
string queryGraphFile;
string answerFile;
#ifdef COREBASED
string coreGraphFile;
#endif

inline void swapValue(int &v1, int &v2)
{
  int temp = v1;
  v1 = v2;
  v2 = temp;
}

inline void swapValue(pair<int, int> &v1, pair<int, int> &v2)
{
  pair<int, int> temp = v1;
  v1 = v2;
  v2 = temp;
}


struct CandidateSpace
{
  int size;               
  int *candidates;        
  int ***adjacent = NULL; 
  int **nAdjacent = NULL; 
  
  int **nbrcnt = NULL; 
  int8_t **nbrsetcnt = NULL; 
  int **nbrsafety = NULL; 

  int8_t *marked;           
  int *vertexToPos = NULL; 

  int **capacity = NULL;
  int **capacityNgb = NULL;

  long long *weight = NULL;
};


int *arrayToClean;
int toCleanIndex = 0;
char *isVisited; 
int *candToPos;  

int uCurr;
int labelID = -1;

int candPos[MAX_NUM_VERTEX];
int currMapping[MAX_NUM_VERTEX];
int nMappedParent[MAX_NUM_VERTEX];

weight_type WEIGHT_MAX = LLONG_MAX;
int *iec[MAX_NUM_VERTEX][MAX_QUERY_DEGREE];
int iecSize[MAX_NUM_VERTEX][MAX_QUERY_DEGREE];

MemPool nbrsetcntPool;
MemPool nbrsafetyPool;
MemPool nbrcntPool;
MemPool MCPool1B;
MemPool MCPool4B;
MemPool MCPool8B;
MemPool VGPool;
int*** adjacent_d1;
int** nAdjacent_d1, **adjacent_d2, **capacity_d1;
int* nAdjacent_d2, *capacity_d2;
int* CSadjacent;
int** CSadjacentAddr;

struct Stack
{
  int *address = NULL;
  int addressSize;
  int addressPos;
  int vertex;
  uint64_t *failingSet;
};
Stack element[MAX_NUM_VERTEX];
Stack *currE;

inline long long getWeightExtendable(int u)
{
  return iecSize[u][nMappedParent[u] - 1];
}

inline void addInFailingSet(
    int u,
    uint64_t *failingSet)
{
  failingSet[u >> 6] |= (1ULL << (u & 0x3f));
}

struct Queue
{
private:
  int posExtendable = 0;
  int minPosition = -1;
  long long optWeight = LLONG_MAX;
  int extendable[MAX_NUM_VERTEX] = {
      0,
  };
  int positions[MAX_NUM_VERTEX] = {
      0,
  };
  int nInserted[MAX_NUM_VERTEX] = {
      0,
  };

public:
  Queue()
  {
    this->posExtendable = 0;
  }

  inline void reinsertToQueue(int u, int depth)
  {
    int position = positions[depth];

    extendable[posExtendable] = extendable[position];
    posExtendable++;

    extendable[position] = u;

  }

  inline void insertToQueue(int u)
  {
    extendable[posExtendable] = u;
    posExtendable++;

  }

  inline void popFromQueue(int &current, int depth)
  {
    int optPos = -1;

    weight_type optWeight = WEIGHT_MAX;

    for (int i = 0; i < posExtendable; i++)
    {
      if (getWeightExtendable(extendable[i]) < optWeight)
      {

        optPos = i;
        optWeight = getWeightExtendable(extendable[i]);
      }
    }

    current = extendable[optPos];
    positions[depth] = optPos;
    extendable[optPos] = extendable[posExtendable - 1];
    posExtendable--;


  }

  inline void removeFromQueue(int depth)
  {
    posExtendable -= nInserted[depth];
  }

  inline void clearQueue()
  {
    memset(nInserted, 0, sizeof(int) * nQueryVertex);
    posExtendable = 0;
  }

  void clear_nInserted(int depth)
  {
    this->nInserted[depth] = 0;
  }

  void add_nInserted(int depth)
  {
    this->nInserted[depth]++;
  }

  int set_optWeight(int optWeight)
  {
    this->optWeight = optWeight;
  }

  int set_minPosition(int minPosition)
  {
    this->minPosition = minPosition;
  }
};

Queue queueFllExt;

int FAILING_SET_SIZE = ((MAX_NUM_VERTEX + 63) >> 6);
uint64_t *ancestors[MAX_NUM_VERTEX];
bool isRedundant;

uint64_t *b;
#ifdef AUTOMORPHISM
void CalculateAutomorphism(Graph *new_graph)
{
  DYNALLSTAT(graph,g,g_sz);
  DYNALLSTAT(int,lab,lab_sz);
  DYNALLSTAT(int,ptn,ptn_sz);
  DYNALLSTAT(int,orbits,orbits_sz);
  static DEFAULTOPTIONS_GRAPH(options);
  statsblk stats;

  int n,m,v;
  grouprec *group;

  options.userautomproc = groupautomproc;
  options.userlevelproc = grouplevelproc;

  n = new_graph->nVertex;
  m = SETWORDSNEEDED(n);

  DYNALLOC2(graph,g,g_sz,m,n,"malloc");
  DYNALLOC1(int,lab,lab_sz,n,"malloc");
  DYNALLOC1(int,ptn,ptn_sz,n,"malloc");
  DYNALLOC1(int,orbits,orbits_sz,n,"malloc");

  EMPTYGRAPH(g,m,n);
  
  for(auto &p: new_graph->DfsCode)
  {
    int from, to;
    from = p.from;
    to = p.to;
    ADDONEEDGE(g, from, to, m);
  }

  std::map<int, vector<int>> partition;
  for (int i = 0; i < new_graph->nVertex; i++)
  {
      partition[new_graph->label[i]].push_back(i);
  }
  ostringstream f;   
  f << "=[";
  int cnt = 0;
  for (auto &p : partition)
  {
    cnt++;
    int lcount = 0;
    for (auto &i : p.second)
    {
      lcount++;
      f << i;
      if (lcount < p.second.size())
        f << ", ";
    }
    if (cnt < partition.size())
      f << "|";
    else
      f << "]\n";
  }
  f <<"\0";

  char buffer[1024];
  FILE* instream = fmemopen(buffer, sizeof(buffer), "w+");
  strcpy(buffer, f.str().c_str());
  boolean prompt = FALSE;
  int numcells = 0;
  
  readptn(instream,lab,ptn,&numcells,prompt,n);
  options.defaultptn = FALSE;

  densenauty(g,lab,ptn,orbits,&options,&stats,m,n,NULL);

  char* buffer2;
  size_t bufsize;
  FILE* stream = open_memstream(&buffer2, &bufsize);

  putorbits(stream, orbits, 0, n);  

  string s = "";
  
  new_graph->classes_mapping.resize(new_graph->nVertex);
  string line;
  bool start = false;
  char readBuffer[100] = {0};
  fgets(readBuffer, sizeof(readBuffer), stream);

  std::istringstream iss(std::string(readBuffer, 100));
  while (getline(iss, line))
  {    
    if (line.size() >= 3 && line.substr(0, 3) == "   ")
      s += line.substr(3);
    else
      s += line;    
  }
  
  stringstream ss(s);
  string temp;
  while (getline(ss, temp, ';'))
  {
    stringstream sss(temp);
    string temp1;
    vector<int> v;
    while (getline(sss, temp1, ' '))
    {
      if (temp1.length() == 0)
        continue;
      if ((temp1.find_first_not_of("0123456789") == std::string::npos))
      {
        v.push_back(stoi(temp1));
        new_graph->classes_mapping[stoi(temp1)] = new_graph->classes.size();
      }
      else
      {
        size_t delim = temp1.find(':');
        if (delim == std::string::npos)
          continue;
        int start = stoi(temp1.substr(0, delim));
        int end = stoi(temp1.substr(delim + 1));
        for (int i = start; i <= end; i++)
        {
          v.push_back(i);
          new_graph->classes_mapping[i] = new_graph->classes.size();
        }
      }
    }
    new_graph->classes.push_back(v);
  }  
  fclose(instream);
  fclose(stream);
  free(buffer2);
}
#endif


void initPool(int k)
{
  if(use_filter){
    nbrcntPool.init(2 * maxNumCandidate * (k+1) * sizeof(int));
    nbrsafetyPool.init(2 * maxNumCandidate * (k+1) * sizeof(int));
    nbrsetcntPool.init(2LL * (k+1) * dataGraph[0]->nEdge * sizeof(int8_t));
  }
  MCPool1B.init(maxNumCandidate);
  MCPool4B.init(maxNumCandidate * sizeof(int));
  MCPool8B.init(maxNumCandidate * sizeof(long long));
  VGPool.init(dataGraph[0]->nVertex * sizeof(int));
  nAdjacent_d1 = new int*[(k+1)*k];
  adjacent_d1 = new int**[(k+1)*k];
  capacity_d1 = new int*[(k+1)*k];
  nAdjacent_d2 = new int[(long long)(k+1)*k*maxNumCandidate];
  adjacent_d2 = new int*[(long long)(k+1)*k*maxNumCandidate];
  capacity_d2 = new int[(long long)(k+1)*k*maxNumCandidate];

  CSadjacent = new int[(long long)k * (long long)dataGraph[0]->nEdge * 4LL];
  CSadjacentAddr = new int*[k+1];
}

inline void AllocateForDataGraph()
{
  mapTo = new int[maxNumDataVertex];
  memset(mapTo, -1, sizeof(int) * maxNumDataVertex);

  arrayToClean = new int[maxNumDataVertex];
  isVisited = new char[maxNumDataVertex];
  memset(isVisited, 0, sizeof(char) * maxNumDataVertex);
  candToPos = new int[maxNumDataVertex];
  memset(candToPos, -1, sizeof(int) * maxNumDataVertex);

  answer = new bool[nGraph];
  memset(answer, false, sizeof(bool) * nGraph);

  mark1_vertex = new int[maxNumCandidate];
}


inline void AllocateForFailingSet()
{
  FAILING_SET_SIZE = (MAX_NUM_VERTEX + 63) >> 6;

  for (int i = 0; i < MAX_NUM_VERTEX; i++)
  {
    element[i].failingSet = new uint64_t[FAILING_SET_SIZE];

    for (int j = 0; j < MAX_QUERY_DEGREE; j++)
      iec[i][j] = new int[maxDegree];
    if (useFailingSet)
      ancestors[i] = new uint64_t[FAILING_SET_SIZE];
  }  
}

inline void AllocateForSubgraph(Graph &query)
{
  nQueryVertex = query.nVertex;

  FAILING_SET_SIZE = (nQueryVertex + 63) >> 6;

  query.nbrqsafety = new int*[nQueryVertex];
  query.compLabelIdx = new int*[nQueryVertex];
  for (int i = 0; i < nQueryVertex; i++)
  {
    query.nbrqsafety[i] = new int[query.degree[i]]; 
    memset(query.nbrqsafety[i], 0, sizeof(int) * query.degree[i]);

    query.compLabelIdx[i] = new int[nQueryVertex];
    memset(query.compLabelIdx[i], 0, sizeof(int) * nQueryVertex);
  }
}

inline void Deallocate(Graph &query)
{
  if(query.nVertex > 2){
    for(int i=0; i<query.nVertex; ++i){
      
      delete[] query.nbrToPos[i];
      delete[] query.nbrqsafety[i];
      delete[] query.compLabelIdx[i];
    }
    delete[] query.compLabelIdx;
    delete[] query.nbrqsafety;
    delete[] query.nbrToPos;
  }
}

inline void DeallocateCS(Graph &query, CandidateSpace *candSpace)
{
  if(use_filter){
    nbrcntPool.free((void*)query.nbrcntpptr);
    if(query.nbrsetcntpptr != NULL)
      nbrsetcntPool.free((void*)query.nbrsetcntpptr);
    nbrsafetyPool.free((void*)query.nbrsafetypptr);
  }

  for (int u = 0; u < query.nVertex; ++u)
  {
    CandidateSpace &currSet = candSpace[u];

    if(use_filter){
      delete[] currSet.nbrsafety;
      delete[] currSet.nbrsetcnt;
      delete[] currSet.nbrcnt;
    }

    VGPool.free(currSet.vertexToPos);
    MCPool8B.free(currSet.weight);
    MCPool1B.free(currSet.marked);
    MCPool4B.free(currSet.candidates);
  }
}

inline void DeallocateGraph(Graph* new_graph, CandidateSpace* cand_space)
{
	if (cand_space != NULL)
	{
		DeallocateCS(*new_graph, cand_space);
		delete[] cand_space;
	}
	Deallocate(*new_graph);
	delete new_graph;
}

inline void AllocateForCandidateSet(Graph &query, CandidateSpace *&cand_space)
{
  cand_space = new CandidateSpace[nQueryVertex];
  assert(query.nVertex == nQueryVertex);

  int* pnbrcnt ;
  int* pnbrsafety ;
  if(use_filter){
    pnbrcnt = (int*)nbrcntPool.alloc();
    pnbrsafety = (int*)nbrsafetyPool.alloc();
    query.nbrcntpptr = pnbrcnt;
    query.nbrsafetypptr = pnbrsafety;
  }

  for (int u = 0; u < nQueryVertex; ++u)
  {
    CandidateSpace &currSet = cand_space[u];
    currSet.candidates = (int*)MCPool4B.alloc();
    currSet.marked = (int8_t*)MCPool1B.alloc();
    currSet.weight = (long long*)MCPool8B.alloc();
    currSet.vertexToPos = (int*)VGPool.alloc();
    if(use_filter){
      currSet.nbrcnt = new int *[maxNumCandidate];
      currSet.nbrsetcnt = new int8_t *[maxNumCandidate];
      currSet.nbrsafety = new int *[maxNumCandidate];
    

      for (int k = 0; k < maxNumCandidate; ++k)
      {
        currSet.nbrcnt[k] = pnbrcnt;
        pnbrcnt += query.degree[u];
        memset(currSet.nbrcnt[k], 0, sizeof(int) * query.degree[u]);
        currSet.nbrsafety[k] = pnbrsafety;
        pnbrsafety += query.degree[u];
        memset(currSet.nbrsafety[k], 0, sizeof(int) * query.degree[u]);
      }
      memset(currSet.nbrsetcnt, 0, sizeof(int8_t*) * maxNumCandidate);
    }
  }

  for (int u = 0; u < nQueryVertex; ++u)
  {
    CandidateSpace &currSet = cand_space[u];

    memset(currSet.marked, 0, sizeof(bool) * maxNumCandidate);
    currSet.size = 0;

    memset(currSet.vertexToPos, -1, sizeof(int) * currG->nVertex);
  }
}



inline bool FilterByCount(const Graph &query, const Graph &data)
{
  if (query.nVertex > data.nVertex || query.nEdge > data.nEdge || query.maxDegree > data.maxDegree || query.labelFrequency.size() > data.labelFrequency.size())
    return false;
  unordered_map<int, int>::const_iterator qIter, dIter;
  for (qIter = query.labelFrequency.begin(); qIter != query.labelFrequency.end(); ++qIter)
  {
    dIter = data.labelFrequency.find(qIter->first);
    if (dIter == data.labelFrequency.end())
      return false;
    else if (qIter->second > dIter->second)
      return false;
  }
  return true;
}


inline void BuildNbrCnt(Graph &query, const Graph &data, CandidateSpace *candSpace)
{
  int8_t* pnbrsetcnt = (int8_t*)nbrsetcntPool.alloc();
  query.nbrsetcntpptr = pnbrsetcnt;
  for (int u = 0; u < query.nVertex; ++u)
  {
    CandidateSpace &currSet = candSpace[u];

    for(int j = 0; j < currSet.size; ++j)
    {
      currSet.vertexToPos[ currSet.candidates[j] ] = j;
      int v = currSet.candidates[j];
      currSet.nbrsetcnt[j] = pnbrsetcnt;
      pnbrsetcnt += data.degree[v];
      memset(currSet.nbrsetcnt[j], 0, sizeof(int8_t) * data.degree[v]);      
    }
  }

  for (int u = 0; u < query.nVertex; ++u)
  {
    CandidateSpace &currSet = candSpace[u];

    for (int j = query.nbrOffset[u]; j < query.nbrOffset[u + 1]; ++j)
    {
      int child = query.nbr.arr[j].first;
      int qel = query.nbr.arr[j].second;
      for (int v = 0; v < currSet.size; ++v)
      {
        auto iter = data.labelToNbrOffset.find(make_pair(currSet.candidates[v], query.label[child]));
        if (iter == data.labelToNbrOffset.end())
          continue;
        
        for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
        {
          int vn = data.nbr.arr[z].first;
          int el = data.nbr.arr[z].second;
          if (candSpace[child].vertexToPos[vn] != -1){
            int vv = currSet.candidates[v];
            if(el != qel) continue;

            currSet.nbrcnt[v][j - query.nbrOffset[u]]++;
            int idx = z - data.nbrOffset[vv];
            
            currSet.nbrsetcnt[v][idx]++;
            if (currSet.nbrsetcnt[v][idx] == 1)
            {
              int lvn = data.label[vn];
              ++currSet.nbrsafety[v][query.compLabelIdx[u][child]];
            }            
          }
        }
        currSet.nbrsafety[v][query.compLabelIdx[u][child]] -= 1;        
      }
    }    
  }
}

inline int computeNbrCnt(Graph* graph, CandidateSpace *candSpace, int u, int v, int un)
{
  int ret = 0;
  CandidateSpace &currSet = candSpace[u];
  CandidateSpace &nbrSet = candSpace[un];
  int qel = -1;
  for(int z = graph->nbrOffset[u]; z < graph->nbrOffset[u + 1]; ++z)
  {
    if(un == graph->nbr.arr[z].first){
      qel = graph->nbr.arr[z].second;
    }
  }
  assert(qel != -1);

  auto iter = currG->labelToNbrOffset.find(make_pair(v, graph->label[un]));
  if (iter == currG->labelToNbrOffset.end())
    return 0;
  
  for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
  {
    int canID = currG->nbr[z];
    int el = currG->nbr.arr[z].second;
    if(el != qel) continue;
    int vnpos = nbrSet.vertexToPos[canID];
    if (nbrSet.vertexToPos[canID] != -1)
    {
      if(nbrSet.marked[vnpos] >= 0)
      {
        ++ret;
      }
    }
  }
  return ret;
}

inline int computeNbrSafety(Graph* graph, CandidateSpace *candSpace, int u, int v, int lun, int qel)
{
  int ret = 0;
  CandidateSpace &currSet = candSpace[u];
  bool* isS;
  isS = new bool[currG->nVertex];
  memset(isS, false, sizeof(bool) * currG->nVertex);

  for(int i = graph->nbrOffset[u]; i < graph->nbrOffset[u + 1]; ++i)
  {
    int un = graph->nbr[i];
    if(graph->label[un] != lun || graph->nbr.arr[i].second != qel)
      continue;

    CandidateSpace &nbrSet = candSpace[un];

    auto iter = currG->labelToNbrOffset.find(make_pair(v, graph->label[un]));
    if (iter == currG->labelToNbrOffset.end())
      return 0;
    
    for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
    {
      int canID = currG->nbr[z];
      int el = currG->nbr.arr[z].second;

      if(qel != el) continue;

      int vnpos = nbrSet.vertexToPos[canID];
      if (nbrSet.vertexToPos[canID] != -1)
      {
        if(nbrSet.marked[vnpos] >= 0)
        {
          if(!isS[canID])
          {
            ++ret;
            isS[canID] = true;;
          }
        }        
      }
    } 
  }
  delete[] isS;

  return ret;
}


inline bool CSnodeFiltering2(const Graph &query, const Graph &data, CandidateSpace * candSpace, int iu, int iv)
{
  queue<pair<int, int>> deadnodes;
#ifdef AUTOMORPHISM
  for (auto &e : query.classes[query.classes_mapping[iu]]){
    int vpos = candSpace[e].vertexToPos[iv];
    if (vpos == -1)
      continue;
		if (candSpace[e].marked[vpos] >= 0){
      candSpace[e].marked[vpos] = -1;
      CS_C[e]--;
      if (CS_C[e] <= tau)
        return false;
		}
		deadnodes.push(make_pair(e, iv));
  }
#else
  deadnodes.push(make_pair(iu, iv));
#endif

  while(!deadnodes.empty())
  {
    int u = deadnodes.front().first;
    int v = deadnodes.front().second;
    deadnodes.pop();

    for (int j = query.nbrOffset[u]; j < query.nbrOffset[u + 1]; ++j)
    {
      int un = query.nbr.arr[j].first;
      int qel = query.nbr.arr[j].second;
      
      auto iter = data.labelToNbrOffset.find(make_pair(v, query.label[un]));
      if (iter == data.labelToNbrOffset.end())
        continue;
      
      for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
      {
        int vn = data.nbr.arr[z].first;
        int el = data.nbr.arr[z].second;
        CandidateSpace &nbrSet = candSpace[un];
        int vnpos = nbrSet.vertexToPos[vn];

        if (el != qel) continue;

        if (vnpos != -1)
        {          
          if (nbrSet.marked[vnpos] < 0)
            continue;

          int unpos = query.nbrToPos[un][u];
        
          nbrSet.nbrcnt[vnpos][unpos]--;
          if(nbrSet.nbrcnt[vnpos][unpos] == 0)
          {
#ifdef AUTOMORPHISM
            nbrSet.marked[vnpos] = -1;
            CS_C[un]--;
            if(CS_C[un] <= tau)
                return false;

            deadnodes.push(make_pair(un, vn));
#else
            nbrSet.marked[vnpos] = -1;
            CS_C[un]--;
            if(CS_C[un] <= tau)
              return false;
            
            deadnodes.push(make_pair(un, vn));
#endif
          }
          else
          {
            int jdx = z - data.nbrOffset[v];
            int nbridx = invnbr[v][jdx];
            nbrSet.nbrsetcnt[vnpos][nbridx]--;
            if (nbrSet.nbrsetcnt[vnpos][nbridx] == 0)
            {
              int lv = data.label[vn];
              nbrSet.nbrsafety[vnpos][query.compLabelIdx[un][u]]--;
              if (nbrSet.nbrsafety[vnpos][query.compLabelIdx[un][u]] < 0)
              {
#ifdef AUTOMORPHISM

                nbrSet.marked[vnpos] = -1;
                CS_C[un]--;
                if(CS_C[un] <= tau)
                  return false;

                deadnodes.push(make_pair(un, vn));
#else
                nbrSet.marked[vnpos] = -1;
                CS_C[un]--;
                if(CS_C[un] <= tau)
                  return false;
            
                deadnodes.push(make_pair(un, vn));
#endif
              }
            }
          }          
        }
      }
    } 
  } 
  return true;
}



inline void removeNode(int u, int v, CandidateSpace *candSpace, const Graph &query, const Graph &data, int un)
{
  CandidateSpace &currSet = candSpace[u];
   
  int vpos = currSet.vertexToPos[v];
  int y = currSet.candidates[currSet.size - 1];
  currSet.candidates[vpos] = y;
  
  if(vpos != currSet.size - 1){
    int* pp = currSet.nbrcnt[vpos];
    currSet.nbrcnt[vpos] = currSet.nbrcnt[currSet.size - 1];
    currSet.nbrcnt[currSet.size - 1] = pp; 

    int8_t* pq = currSet.nbrsetcnt[vpos];
    currSet.nbrsetcnt[vpos] = currSet.nbrsetcnt[currSet.size - 1];
    currSet.nbrsetcnt[currSet.size - 1] = pq;

    int* p = currSet.nbrsafety[vpos];
    currSet.nbrsafety[vpos] = currSet.nbrsafety[currSet.size - 1];
    currSet.nbrsafety[currSet.size - 1] = p;

    currSet.vertexToPos[y] = vpos;
  }  
  currSet.vertexToPos[v] = -1; 
  
  --currSet.size;
}

inline bool CSnodeFiltering(const Graph &query, const Graph &data, CandidateSpace *candSpace)
{
  queue<pair<int, int>> deadnodes;
  int CS_BC[100];
  int u1 = query.DfsCode.back().from;
  int u2 = query.DfsCode.back().to;
  int lu1 = query.DfsCode.back().from_label;
  int lu2 = query.DfsCode.back().to_label;

  for (int i = 0; i < query.nVertex; ++i)
  {
    CS_BC[i] = candSpace[i].size;
  }

  for (int j = 0; j < candSpace[u1].size; ++j)
  {
    int v = candSpace[u1].candidates[j];
    for (int k = query.nbrOffset[u1]; k < query.nbrOffset[u1 + 1]; ++k)
    {
      int un = query.nbr.arr[k].first;
      if (candSpace[u1].nbrcnt[j][k - query.nbrOffset[u1]] == 0 || candSpace[u1].nbrsafety[j][query.compLabelIdx[u1][un]] < 0){
        removeNode(u1, v, candSpace, query, data, un);
        CS_BC[u1]--;
        if(CS_BC[u1] <= tau){
          return false;
        }
        deadnodes.push(make_pair(u1, v));
        --j;
        break;
      }
    }
  }

  for (int j = 0; j < candSpace[u2].size; ++j)
  {
    int v = candSpace[u2].candidates[j];
    for (int k = query.nbrOffset[u2]; k < query.nbrOffset[u2 + 1]; ++k)
    {
      int un = query.nbr.arr[k].first;
      if (candSpace[u2].nbrcnt[j][k - query.nbrOffset[u2]] == 0 || candSpace[u2].nbrsafety[j][query.compLabelIdx[u2][un]] < 0){

        removeNode(u2, v, candSpace, query, data, un);
        CS_BC[u2]--;
        if(CS_BC[u2] <= tau){
          return false;
        }
        deadnodes.push(make_pair(u2, v));
        --j;
        break;
      }
    }
  }

  while(!deadnodes.empty())
  {
    int u = deadnodes.front().first;
    int v = deadnodes.front().second;
    deadnodes.pop();
    
    for (int j = query.nbrOffset[u]; j < query.nbrOffset[u + 1]; ++j)
    {
      int un = query.nbr.arr[j].first;
      int qel = query.nbr.arr[j].second;
      
      auto iter = data.labelToNbrOffset.find(make_pair(v, query.label[un]));
      if (iter == data.labelToNbrOffset.end())
        continue;
      
      for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
      {
        int vn = data.nbr.arr[z].first;
        int el = data.nbr.arr[z].second;
        CandidateSpace &nbrSet = candSpace[un];
        int vnpos = nbrSet.vertexToPos[vn];
        
        if(el != qel) continue;

        if (vnpos != -1)
        {
          int unpos = query.nbrToPos[un][u];
          nbrSet.nbrcnt[vnpos][unpos]--;
          if(nbrSet.nbrcnt[vnpos][unpos] == 0)
          {     
            removeNode(un, vn, candSpace, query, data, u);
            CS_BC[un]--;
            
            if(CS_BC[un] <= tau){
              return false;
            }                
            deadnodes.push(make_pair(un, vn));
          }    
          else
          {
            int jdx = z - data.nbrOffset[v];
            int nbridx = invnbr[v][jdx];
            nbrSet.nbrsetcnt[vnpos][nbridx]--;
            if (nbrSet.nbrsetcnt[vnpos][nbridx] == 0)
            {
              int lv = data.label[vn];
              nbrSet.nbrsafety[vnpos][query.compLabelIdx[un][u]]--;
              if (nbrSet.nbrsafety[vnpos][query.compLabelIdx[un][u]] < 0)
              {
                removeNode(un, vn, candSpace, query, data, u);
                CS_BC[un]--;
                
                if(CS_BC[un] <= tau){
                  return false;
                }

                deadnodes.push(make_pair(un, vn));
              }
            }
          }              
        }
      }
    } 
  }
  return true; 
}

inline bool ConstructAdjacencyList(const Graph &query, const Graph &data, bool filter, CandidateSpace *candSpace)
{
  int*** ad1;
  int** nd1, **ad2, **cd1;
  int* nd2, *cd2;
  ad1 = adjacent_d1;
  nd1 = nAdjacent_d1;
  ad2 = adjacent_d2;
  cd1 = capacity_d1;
  nd2 = nAdjacent_d2;
  cd2 = capacity_d2;

  for (int u = 0; u < query.nVertex; ++u)
  {
    CandidateSpace &currSet = candSpace[u];
    currSet.nAdjacent = nd1;
    nd1 += query.maxDegree;
    currSet.adjacent = ad1;
    ad1 += query.maxDegree;
    currSet.capacity = cd1;
    cd1 += query.maxDegree;
    for (int k = 0; k < query.maxDegree; ++k)
    {
      currSet.nAdjacent[k] = nd2;
      nd2 += maxNumCandidate;
      currSet.adjacent[k] = ad2;
      ad2 += maxNumCandidate;
      currSet.capacity[k] = cd2;
      cd2 += maxNumCandidate;
      memset(currSet.capacity[k], 0, sizeof(int) * maxNumCandidate);
      memset(currSet.adjacent[k], 0, sizeof(int *) * maxNumCandidate);
    }
  }

  int* p = CSadjacent;
  for(int i=0; i<query.nVertex; ++i){
    CSadjacentAddr[i] = p;
    p += (query.degree[i]*data.nEdge*2LL);
  }

  unordered_map<pair<int, int>, pair<number_type, number_type>, pairHash>::const_iterator iter;
  for (int i = query.nVertex - 1; i >= 0; --i)
  {
    int u = i;
    int currLabel = query.label[u];
    CandidateSpace &currSet = candSpace[u];
    if (filter)
    {
      for (int vPos = 0; vPos < currSet.size; ++vPos)
      {
        int currCand = currSet.candidates[vPos];
        if (isVisited[currCand] == 0)
        {
          isVisited[currCand] = 1;
          arrayToClean[toCleanIndex++] = currCand;
          ++cntLabel[currLabel];
        }
      }
    }

    for (int vPos = 0; vPos < currSet.size; ++vPos)
    {
      candToPos[currSet.candidates[vPos]] = vPos;
    }
    for (int j = query.nbrOffset[u]; j < query.nbrOffset[u + 1]; ++j)
    {
      int unPos = j - query.nbrOffset[u];

      int un = query.nbr.arr[j].first;
      int query_edgeLabel = query.nbr.arr[j].second;
      CandidateSpace &nbrSet = candSpace[un];
      int uPos = query.nbrToPos[un][u];

      memset(nbrSet.nAdjacent[uPos], 0, sizeof(int) * currSet.size);
      for (int vPos = 0; vPos < currSet.size; ++vPos)
      {
        int currSize = data.degree[currSet.candidates[vPos]];
        if (nbrSet.capacity[uPos][vPos] < currSize)
        {
          nbrSet.capacity[uPos][vPos] = currSize;
          nbrSet.adjacent[uPos][vPos] = CSadjacentAddr[un];
          CSadjacentAddr[un] += currSize;
        }
      }

      for (int vnPos = 0; vnPos < nbrSet.size; ++vnPos)
      {
        int vn = nbrSet.candidates[vnPos];

        iter = data.labelToNbrOffset.find(make_pair(vn, currLabel));
        if (iter == data.labelToNbrOffset.end())
          continue;
        for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
        {
          int v = data.nbr.arr[z].first;
          int edge_label = data.nbr.arr[z].second;
          if (edge_label != query_edgeLabel) continue;
          int vPos = candToPos[v];
          if (vPos < 0)
            continue;
          nbrSet.adjacent[uPos][vPos][nbrSet.nAdjacent[uPos][vPos]++] = vnPos;
        }
      }
    }
    for (int vPos = 0; vPos < currSet.size; ++vPos)
    {
      candToPos[currSet.candidates[vPos]] = -1;
    }
  }
  if (filter)
  {
    while (toCleanIndex != 0)
      isVisited[arrayToClean[--toCleanIndex]] = 0;
    for (unordered_map<int, int>::const_iterator it = query.labelFrequency.begin(); it != query.labelFrequency.end(); ++it)
    {
      if (cntLabel[it->first] < it->second)
        return false;
    }
  }
  return true;
}

inline bool PrepareMNI(Graph *graph, CandidateSpace *&cand_space)
{
#ifdef AUTOMORPHISM
    CalculateAutomorphism(graph);
#endif

  nQueryVertex = graph->nVertex;
  if (!ConstructAdjacencyList(*graph, *currG, true, cand_space))
    return false;
  return true;
}

void conflictClass(
    int uCurr, int uID, int depth)
{
  ancestors[depth][uCurr >> 6] |= (1ULL << (uCurr & 0x3f));

  const uint64_t arr = (1ULL << (uID & 0x3f));
  addInFailingSet(uID, currE->failingSet);
  addInFailingSet(uID, ancestors[depth]);
}

struct dynamicDAG_ancestors
{
private:
  uint64_t dag_ancestors[MAX_NUM_VERTEX][MAX_NUM_VERTEX][MAX_NUM_VERTEX];
public:
  void clear(int root)
  {
    fill(
        dag_ancestors[root][0],
        dag_ancestors[root][0] + FAILING_SET_SIZE,
        0ULL);
  }

  void addAncestor(
      int u, int uP,
      int uNumPar, int uPNumPar)
  {
    if (uNumPar == 1)
    {
      fill(
          dag_ancestors[u][1],
          dag_ancestors[u][1] + FAILING_SET_SIZE,
          0ULL);
    }
    for (int x = 0; x < FAILING_SET_SIZE; x++)
    {
      dag_ancestors[u][uNumPar][x] = dag_ancestors[u][uNumPar - 1][x];
      dag_ancestors[u][uNumPar][x] |= dag_ancestors[uP][uPNumPar][x];
    }
    addInFailingSet(
        uP,
        dag_ancestors[u][uNumPar]);
  }

  uint64_t getSetPartition(
      int u, int uNumPar, int y)
      const
  {
    return dag_ancestors[u][uNumPar][y];
  }
} dyanc;


long long getExtendableCandidates(
    int u, int uIdx,
    int up, int candParentIdx,
    int uNgbIdx,
    int numParentsMapped,
    CandidateSpace *candSpace)
{
  int c;
  CandidateSpace &unit = candSpace[u];
  const int iecPos = numParentsMapped - 1;

  iecSize[u][iecPos] = 0;
  if (numParentsMapped == 1)
  {

    for (int i = 0; i < unit.nAdjacent[uNgbIdx][candParentIdx]; i++)
    {
      const int candIdx = unit.adjacent[uNgbIdx][candParentIdx][i];
      const int vID = unit.candidates[candIdx];
      if (unit.marked[candIdx] >= 0) 
	      iec[u][0][iecSize[u][0]++] = candIdx;
    }	
  }
  else
  {
    int j = 0, k = 0, candIdx, newCandIdx;
    int indexSize = iecSize[u][iecPos - 1];
    int newIndexSize =
        unit.nAdjacent[uNgbIdx][candParentIdx];

    while (j < indexSize and k < newIndexSize)
    {
      candIdx = iec[u][iecPos - 1][j];
      newCandIdx = unit.adjacent[uNgbIdx][candParentIdx][k];
      if (candIdx == newCandIdx)
      {
        const int vID = unit.candidates[candIdx];
        if (useFailingSet)
        {
          iec[u][iecPos][iecSize[u][iecPos]++] = candIdx;

        }
        else
        {
          if (mapTo[vID] < 0 && unit.marked[candIdx] >= 0)
          {
            iec[u][iecPos][iecSize[u][iecPos]++] = candIdx;
          }
        }
        ++j;
        ++k;
      }
      else if (candIdx < newCandIdx)
        ++j;
      else
        ++k;
    }
  }
  return (long long)iecSize[u][iecPos];
}

inline void reset(int depth, int ri, int rootCand, const Graph& query, CandidateSpace *candSpace)
{
  while (depth > 0)
  {
    Stack &tempE = element[depth];
    int uID = tempE.vertex;
    int vID = currMapping[depth];
    isMapped[uID] = false;
    for (int i = query.nbrOffset[uID]; i < query.nbrOffset[uID + 1]; ++i)
    {
      int idx = i - query.nbrOffset[uID];
      --nMappedParent[query.nbr.arr[i].first];
    }
    queueFllExt.clear_nInserted(depth);

    mapTo[vID] = -1;

    tempE.address = NULL;
    --depth;
  }

  mapTo[rootCand] = -1;
  queueFllExt.clearQueue();

  if (useFailingSet)
    isRedundant = false;

}

void updateExtendableRoot(
    const Graph &query,
    int ri, int u,
    CandidateSpace *candSpace,
    int depth = 1)
{
  long long weight;
  for (int j = query.nbrOffset[u]; j < query.nbrOffset[u + 1]; ++j)
  {
    int rc = query.nbr.arr[j].first;
    weight = getExtendableCandidates(
        rc, j,
        u, ri,
        query.nbrToPos[rc][u],
        nMappedParent[rc],
        candSpace);

    if (nMappedParent[rc] == 1)
    {
      queueFllExt.insertToQueue(rc);
    }
  } 
}

bool updateExtendableU(
    const Graph &query,
    int u,
    int depth,
    const int uPos,
    int &uID,
    int &vCID,
    CandidateSpace *candSpace)
{
  bool flag = true;
  long long weight;
  for (int j = query.nbrOffset[uCurr]; j < query.nbrOffset[uCurr + 1]; ++j)
  {
    int uC = query.nbr.arr[j].first;

    if (isMapped[uC])
      continue;
    else
    {
      weight = getExtendableCandidates(
          uC, j,
          uCurr, uPos,
          query.nbrToPos[uC][uCurr],
          nMappedParent[uC],
          candSpace);
    }
    if (weight == 0)
    {
      flag = false;
      if (useFailingSet)
      {
        addInFailingSet(uC, ancestors[depth]);
      }  
      break;
    }

    if (nMappedParent[uC] == 1)
    {
      queueFllExt.insertToQueue(uC);
      queueFllExt.add_nInserted(depth);
    }
  }
  return flag;
}

void updateReleaseCandidate(
    int depth,
    CandidateSpace *candSpace)
{
  Stack &higherE = element[depth];
  Stack &lowerE = element[depth + 1];

  mapTo[currMapping[depth]] = -1;
  queueFllExt.removeFromQueue(depth);
  queueFllExt.clear_nInserted(depth);
}

void updateAncestors(int uCurr, const Graph& query)
{
  for (int i = query.nbrOffset[uCurr]; i < query.nbrOffset[uCurr + 1]; ++i)
  {
    int uC = query.nbr.arr[i].first;
    if (!isMapped[uC])
    {
      ++nMappedParent[uC];
      dyanc.addAncestor(
          uC, uCurr,
          nMappedParent[uC], nMappedParent[uCurr]);
    }
  }
}

int updateMappingQueryVer(
    int uCurr, int depth, int &uPPos,
    const CandidateSpace *currSet,
    const Graph& query)
{
  isMapped[uCurr] = true;

  updateAncestors(uCurr, query);
  if (useFailingSet)
  {
    for (int x = 0; x < FAILING_SET_SIZE; ++x)
    {
      currE->failingSet[x] = 0;
    }
  }
  currE->address = iec[uCurr][nMappedParent[uCurr] - 1];
  currE->addressSize = iecSize[uCurr][nMappedParent[uCurr] - 1];

  return 0; 
}

void updateReleaseQueryVer(
    int uCurr, int depth, const Graph& query)
{
  queueFllExt.reinsertToQueue(uCurr, depth);
  isMapped[uCurr] = false;
  for (int i = query.nbrOffset[uCurr]; i < query.nbrOffset[uCurr + 1]; ++i)
  {
    int uC = query.nbr.arr[i].first;
    if (!isMapped[uC])
    {
      --nMappedParent[uC];
    }
  }
}

int getNextuPosIdx()
{
  weight_type currVal, maxVal;
  int optOffset;
  int uPosIdx;
  uPosIdx = currE->addressPos;
  return uPosIdx;
}

void updateFailingSet(
    int depth,
    bool isRedundant)
{
  for (int x = 0; x < FAILING_SET_SIZE; ++x)
  {
    if (!isRedundant)
    {
      uint64_t arr = ancestors[depth][x];
      while (arr)
      {
        int idx = (x << 6) + __builtin_ctzl(arr);
        for (int y = 0; y < FAILING_SET_SIZE; ++y)
        {
          currE->failingSet[y] |= dyanc.getSetPartition(idx, nMappedParent[idx], y);
        }
        arr ^= (arr & -arr);
      }
    }
    ancestors[depth][x] = 0;
  }

}

void moveUpFailingSet(
    const Stack &higherE,
    int depth)
{
  int uID = higherE.vertex;
  b = currE->failingSet;
  if (depth != 0)
  {
    if ((b[uID >> 6] & (1ULL << (uID & 0x3f))) == 0)
    {
      for (int x = 0; x < FAILING_SET_SIZE; ++x)
        higherE.failingSet[x] = b[x];
      isRedundant = true;
    }
    else
    {
      for (int x = 0; x < FAILING_SET_SIZE; ++x)
        higherE.failingSet[x] |= b[x];
    }
  }
}

inline bool findAllEmbeddings(
    int dataGraphID)
{
  return false;
}
inline bool cannotMap(
    int dataGraphID)
{
  if (currE->addressPos == currE->addressSize || isRedundant)
  {
    return true;
  }
  else
  {
    return false;
  }
}


inline void BacktrackRootInitial(const Graph &query, const Graph &data, CandidateSpace *candSpace, int root_u)
{
  dyanc.clear(root_u);
  queueFllExt.clearQueue();

  memset(isMapped, false, sizeof(bool) * nQueryVertex);
  memset(nMappedParent, 0, sizeof(int) * nQueryVertex);

  isRedundant = false;
  if (useFailingSet)
  {
    for (int i = 0; i < nQueryVertex; ++i)
      memset(ancestors[i], 0, sizeof(uint64_t) * FAILING_SET_SIZE);
  }
  Stack &rootE = element[0];

  isMapped[root_u] = true;

  updateAncestors(root_u, query);

  rootE.vertex = root_u;
  rootE.address = candSpace[root_u].candidates;
  rootE.addressPos = -1;
  rootE.addressSize = candSpace[root_u].size;

  recursiveCallCountPerGraph = 1;
  ++recursiveCallCount;
}

inline void BacktrackOnce(const Graph &query, const Graph &data, CandidateSpace *candSpace, int root_u, int ri)
{
  long long weight;
  int uPPos, uPos, vID, vCID, uID;
  bool flag;
  CandidateSpace *currSet, *childSet;
  bool find_embedding = false;

  BacktrackRootInitial(query, data, candSpace, root_u);

  Stack &rootE = element[0];


  int rootCand = candSpace[root_u].candidates[ri];

  mapTo[rootCand] = root_u;
  currMapping[0] = rootCand; 
  candPos[root_u] = ri;
  char backtrack = 0;

  int depth = 1; 
  updateExtendableRoot(query, ri, root_u, candSpace);
  while (!find_embedding)
  {
    if (depth == 0)
      break; 
    if (depth == query.nNonLeaf)
    {
      find_embedding = true;
      for (int internal_depth = 0; internal_depth < query.nNonLeaf; ++internal_depth)
      {
        Stack *currIE = &element[internal_depth];
#ifdef AUTOMORPHISM
        int ui = currIE->vertex;
        int vi = candSpace[ui].candidates[candPos[ui]];
        for (auto &e : query.classes[query.classes_mapping[ui]]){
          int vpos = candSpace[e].vertexToPos[vi];
          assert(vpos != -1);

          if (candSpace[e].marked[vpos] == 0){
            candSpace[e].marked[vpos] = 1;
            CS_M[e]++;
          }
        }
#else
        if(candSpace[currIE->vertex].marked[candPos[currIE->vertex]] == 0){
          candSpace[currIE->vertex].marked[candPos[currIE->vertex]] = 1;
            
        CS_M[currIE->vertex]++;
      }
#endif
      }      

      if (findAllEmbeddings(0) && find_embedding)
      {
        element[depth].address = NULL;
        --depth;

        reset(depth, ri, rootCand, query, candSpace);
        return;
      }

      --depth;
      updateReleaseCandidate(depth, candSpace);

      if (useFailingSet)
      {
        for (int x = 0; x < FAILING_SET_SIZE; ++x)
          element[depth].failingSet[x] = ~0ULL;
      }
      continue;
    } 
    currE = &element[depth];
    if (currE->address == NULL)
    {
      ++recursiveCallCount;
      ++recursiveCallCountPerGraph;
      queueFllExt.popFromQueue(uCurr, depth);

      currE->vertex = uCurr;
      currSet = &candSpace[uCurr];

      updateMappingQueryVer(uCurr, depth, uPPos, currSet, query);

      if (currE->addressSize == 0)
      {
        currE->address = NULL;
        isRedundant = false;
        if (depth != 0)
        {
          if (useFailingSet)
          {
            updateFailingSet(depth, isRedundant);
          }
          updateReleaseQueryVer(uCurr, depth, query);
        }        
        --depth; 

        continue;
      } 
      currE->addressPos = 0;
      int *ptr = iec[uCurr][nMappedParent[uCurr]];
      int num_mark0 = 0, num_mark1 = 0;
      for (int i = 0; i < currE->addressSize; ++i)
      {
        int pos = currE->address[i];
        if (currSet->marked[pos] == 0){
          ptr[num_mark0] = currE->address[i];
          num_mark0++;
        }
        else{
          mark1_vertex[num_mark1] = currE->address[i];
          num_mark1++;
        }
      }
      for (int i = 0; i < num_mark1; ++i){
        ptr[num_mark0 + i] = mark1_vertex[i];
      }
      currE->address = ptr;
    }
    else 
    {
      uCurr = currE->vertex;
      currSet = &candSpace[uCurr];
      currE->addressPos++; 

      if (cannotMap(0))
      {
        if (useFailingSet)
        {
          updateFailingSet(depth, isRedundant);
          isRedundant = false;
        }
        updateReleaseQueryVer(uCurr, depth, query);

        Stack &higherE = element[depth - 1];
        currE->address = NULL;
        --depth;
        updateReleaseCandidate(depth, candSpace);

        uID = higherE.vertex;
        if (useFailingSet)
        {
          moveUpFailingSet(higherE, depth);
        }
        continue;
      }            
    }              
    backtrack = 0; 
    while (true)
    {


      int uPosIdx = getNextuPosIdx();
      uPos = currE->address[uPosIdx];
      vID = currSet->candidates[uPos];

      if (mapTo[vID] < 0) 
      {
        currMapping[depth] = vID; 
        candPos[uCurr] = uPos;
        mapTo[vID] = uCurr; 

        if (!updateExtendableU(query, uCurr, depth, uPos, uID, vCID, candSpace))
        {
          updateReleaseCandidate(depth, candSpace);

          currE->addressPos++;
          if (currE->addressPos == currE->addressSize)
          {
            backtrack = 1;
            break;
          }
          else
          {
            continue;
          }
        }
        break;
      }
      else 
      {
        uID = mapTo[vID];
        if (useFailingSet)
        {
          conflictClass(uCurr, uID, depth);
        }
        currE->addressPos++; 
        if (currE->addressPos == currE->addressSize)
        { 
          backtrack = 1;
          break;
        }
      }
    } 

    if (backtrack)
    {
      backtrack = 0;
      if (useFailingSet)
      {
        updateFailingSet(depth, isRedundant);
        isRedundant = false;
      }
      updateReleaseQueryVer(uCurr, depth, query);
      currE->address = NULL;
      --depth;

      Stack &higherE = element[depth];
      updateReleaseCandidate(depth, candSpace);

      uID = higherE.vertex;
      if (useFailingSet)
      {
        moveUpFailingSet(higherE, depth);
      }
    }
    else 
    {
      depth++;
    }
  }
  reset(depth, ri, rootCand, query, candSpace);
}

inline bool update_nbr(const Graph &query, const Graph &data, CandidateSpace * candSpace, int u, int v){
	for (int j = query.nbrOffset[u]; j < query.nbrOffset[u + 1]; ++j){
		int un =query.nbr.arr[j].first;
		int qel = query.nbr.arr[j].second;
		auto iter = data.labelToNbrOffset.find(make_pair(v, query.label[un]));
		if (iter == data.labelToNbrOffset.end())
			continue;

		for (int z = iter->second.first; z < iter->second.first + iter->second.second; ++z)
		{
			int vn = data.nbr.arr[z].first;
			int el = data.nbr.arr[z].second;
			CandidateSpace &nbrSet = candSpace[un];
			int vnpos = nbrSet.vertexToPos[vn];

			if (el != qel) continue;

			if (vnpos != -1)
			{          
				if (nbrSet.marked[vnpos] < 0)
					continue;

				int unpos = query.nbrToPos[un][u];

				nbrSet.nbrcnt[vnpos][unpos]--;
				if(nbrSet.nbrcnt[vnpos][unpos] == 0)
				{
					continue;
				}
				else
				{
					int jdx = z - data.nbrOffset[v];
					int nbridx = invnbr[v][jdx];
					nbrSet.nbrsetcnt[vnpos][nbridx]--;
					if (nbrSet.nbrsetcnt[vnpos][nbridx] == 0)
					{
						int lv = data.label[vn];
						nbrSet.nbrsafety[vnpos][query.compLabelIdx[un][u]]--;
					}
				}
			}
		}
	}
}



inline int computeMNI(const Graph &query, const Graph &data, CandidateSpace *candSpace)
{
  int minM=0;
  int minC=1'000'000'000;

  long long total_Cu = 0;
  int curr_u = 0;
  for (int i = 0; i < query.nVertex; ++i) {
    CandidateSpace &currSet = candSpace[i];
    CS_M[i] = 0;
    CS_C[i] = currSet.size;
    CS_CIDX[i] = 0;	
    minC = min(minC, CS_C[i]);
    total_Cu += currSet.size;
  }

  failed_cnt = total_cnt = 0;
  double avg_Ci = (double)total_Cu/(double)query.nVertex;
  double threshold_minMC = (double)(avg_Ci-tau)/(double)avg_Ci;

  while (minM < minC){
	  curr_u = -1;
	  int tmp_minM, tmp_minC;
	  tmp_minM = tmp_minC = 1'000'000'000;
	  double curr_ratio = total_cnt == 0 ? 0: (double)failed_cnt/(double)total_cnt;

	  if( curr_ratio <= threshold_minMC){
		  for (int i=0; i<query.nVertex; ++i){
			  if(CS_M[i] != CS_C[i]){
				  if ( CS_M[i] == tmp_minM ? CS_C[i] < tmp_minC : CS_M[i] < tmp_minM )
				  {
					  curr_u = i;
					  tmp_minM = CS_M[i];
					  tmp_minC = CS_C[i];
				  }
			  }
		  }
	  }
	  else {
		  for (int i=0; i<query.nVertex; ++i){
			  if(CS_M[i] != CS_C[i]){
				  if ( CS_C[i] == tmp_minC ? CS_M[i] < tmp_minM : CS_C[i] < tmp_minC )
				  {
					  curr_u = i;
					  tmp_minM = CS_M[i];
					  tmp_minC = CS_C[i];
				  }
			  }
		  }
	  }
	  CandidateSpace &currSet = candSpace[curr_u];
	  int& cIdx = CS_CIDX[curr_u];
	  while (cIdx < currSet.size){
		  total_cnt++;
      if (currSet.marked[cIdx] == 1 || currSet.marked[cIdx] == -1){
        if (currSet.marked[cIdx] == -1)
          failed_cnt++;
        ++cIdx;
        continue;
      }

      int v = currSet.candidates[cIdx];

      BacktrackOnce(query, data, candSpace, curr_u, cIdx);

      if ( currSet.marked[cIdx] == 1){
        minM = 1'000'000'000;
        for (int i=0; i<query.nVertex; ++i){
          minM = min(minM, CS_M[i]);
        }
      }
      else{
        failed_cnt++;
        currSet.marked[cIdx] = -1;
        --CS_C[curr_u];
        if (CS_C[curr_u] <= tau) {
          return -1;
        }
        if(use_filter){
          if(!CSnodeFiltering2(query, data, candSpace, curr_u, currSet.candidates[cIdx]))
            return -1;
        }
        for (int i=0; i<query.nVertex; ++i){
          minC = min(minC, CS_C[i]);
        }
      }
      cIdx++;
      break;
    }
  } 
  return minM;
}


