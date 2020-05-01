# nxg

A graph numbering dozens of trillion of nodes already exceeds the human brain in synapses and the Word Wide Web in URLs. Since there are usually more edges than there are nodes in a graph, that also means hundreds of trillion or even quadrillion edges. And if you add data to those nodes and edges, you may expect hundreds of Petabytes for real applications.. Since the size of the amount of disk memory that a single VM is able to buffer does not exceed dozens of Terabytes, it is unlikely that a graph containing that many nodes and edges and Petabytes of data can be stored on a single machine, notwithstanding the exotic nature of the machine. Instead, expect a distributed database numbering hundreds and thousands of “shards” (partitions of a graph). The challenge of a trillion-node graph is the network. 

The corollary is that the choice of graph engine package that hosts each partitioned graph shard is not as critical a factor, since the major performance bottleneck is crossing shard boundaries across the network. Like the speed of light between stars, that is a bottleneck that cannot be warped over. 

This is a graph partitioning experimentation platform that examines the cost of partitioning a graph across a network for paradigmatic graph queries such as Breadth-First Search (BFS) and benchmarks graph engines such as Neo4j and JanusGraph for this operation. 

The design is a downloadable docker container that can be run on any platform like so: docker run -d -p 5050:5000 dinorows/nxg. You may then open a browser at localhost:5050 on your host and run the benchmark experiments on your own. The experiments are controlled by a flask Web app interface. 

Trillion-node and petabyte-data graphs are eminently possible, using today’s best of breed graph engines. The open source nature of the Neo and Janus graph engines and the expressiveness of their DSLs make them good choices for the task. The main performance bottleneck is the network, thus a fast network is the best guarantee of query performance. The choice of the graph engine is not as relevant to performance. The choice of the graph engine comes down to personal preference and expressiveness of the data mining DSL. CYPHER (Neo4J) and GREMLIN (JanusGraph) are today’s most expressive graph DSLs.

If licenses for enterprise version of graph engines which manage the distribution of graph shards are too expensive, graph shards can easily be hosted by an open source container orchestration framework like Kubernetes or Apache Mesos. Sharding and cross-cuts can then be managed by the orchestration framework, albeit at the price of tailored implementations of graph query primitives (as in this experimentation platform for BFS across Neo and Janus shards). 

