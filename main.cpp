#include <queue>
#include <cassert>
#include "extension.h"

priority_queue<AnswerElement> answer_set;

void printAnswer()
{
  cout << "==================" << endl;
  cout << "      Answer            " << endl;
  cout << "==================" << endl;
  cout << "Size of answer set " << answer_set.size() << endl;
  if (!answer_set.empty())
    cout << "Minimum MNI " << answer_set.top().mni << endl;
  
  while (!answer_set.empty())
  {
    cout << "--------" << endl;
    cout << "MNI " << answer_set.top().mni << endl;

    answer_set.top().graph->printGraph(labelMap_inverse, edgelabelMap_inverse);
    cout << endl;    
    
    auto p = answer_set.top().graph;
    Deallocate(*p);
    delete p;
    answer_set.pop();
  }
}

inline void FrequentMining(int K)
{
 
  recursiveCallCount = 0;
  currG = dataGraph[0];
  AllocateForFailingSet();

  priority_queue<HeapElement> cand_graph_set;
  vector<pair<Graph *, int>> freq_edge_graph;
  freq_edge_graph.reserve(K);


  computeFrequentEdge(dataGraph[0], K, cand_graph_set);

  createSubgraphAddtoAnswer(freq_edge_graph, answer_set, K);

  tau = (answer_set.size() == K) ? answer_set.top().mni : 0;

  for (auto e : freq_edge_graph)
  {
    ExtensionEdge(cand_graph_set, e.first, e.second);
  }

  HeapElement helt;
  Graph *new_graph;

  while (!cand_graph_set.empty() && cand_graph_set.top().ub > tau)
  {
    helt = cand_graph_set.top();
    new_graph = helt.graph;
    CandidateSpace *cand_space = helt.CS;
    cand_graph_set.pop();
    currQ = new_graph;

    bool isCandidate = PrepareMNI(new_graph, cand_space);
    if (!isCandidate)
    {
      DeallocateGraph(new_graph, cand_space);
    }
	
    int new_tau = computeMNI(*new_graph, *currG, cand_space);

    if (new_tau > tau)
    {
      if (answer_set.size() < K)
      {
        answer_set.push(AnswerElement(new_tau, new_graph));
      }
      else
      {
        auto p = answer_set.top();
        answer_set.pop();

        nQueryVertex = p.graph->nVertex;
        Deallocate(*p.graph);
        delete p.graph;

        answer_set.push(AnswerElement(new_tau, new_graph));
      }

      if (answer_set.size() == K)
      {
        tau = answer_set.top().mni;
      }

      Extension(cand_graph_set, new_graph, cand_space, new_tau);

      DeallocateCS(*new_graph, cand_space);
      delete[] cand_space;
    }
    else
    {
      DeallocateGraph(new_graph, cand_space);	
    }
  }

}


int main(int argc, char *argv[])
{
  setvbuf(stdout, NULL, _IOLBF, 0);

  int k;
  for (int i = 1; i < argc; ++i)
  {
    if (argv[i][0] == '-')
    {
      switch (argv[i][1])
      {
      case 'd':        
        dataGraphFile = argv[i + 1];
        break;
      case 'q':        
        queryGraphFile = argv[i + 1];
        break;
      case 'k':
        k = atoi(argv[i + 1]);
        break;
#ifdef COREBASED
      case 'c':
        coreGraphFile = argv[i + 1];
      break;
#endif
      }
    }
  }
  cout << "Data file: " << dataGraphFile << endl;

  chrono::high_resolution_clock::time_point startClock, endClock;
  startClock = GetClock();
  ReadGFUFormat(dataGraphFile, dataGraph);
#ifdef COREBASED
  ReadGFUFormat(coreGraphFile, coreGraph);
#endif

  ProcessDataGraphs();
  AllocateForDataGraph();
  initPool(k);
  

  FrequentMining(k);
  endClock = GetClock();

  cout<<"Elapsed Time "<<TimeDiffInMilliseconds(startClock, endClock)/1000<<endl;;


  printAnswer();
  
  return 0;
}
