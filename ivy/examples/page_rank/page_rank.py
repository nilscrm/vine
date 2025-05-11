def pagerank(graph, damping=0.85, epsilon=1e-8, max_iterations=100):
    # Number of nodes in the graph
    n = len(graph)
    
    # Initialize PageRank scores equally
    pr = {node: 1/n for node in graph}
    
    # Iterative computation of PageRank
    for iteration in range(max_iterations):
        print(f"Iteration {iteration}")
        for node, score in pr.items():
            print(f"Node {node}: {score:.6f}")
        print("")

        new_pr = {}
        
        # Initialize with the contribution from the random jump
        for node in graph:
            new_pr[node] = (1 - damping) / n
        
        # Add the contribution from incoming links
        for node in graph:
            for neighbor in graph[node]:
                # If the node has outgoing links, divide its PageRank by the number of links
                if graph[node]:
                    new_pr[neighbor] += damping * pr[node] / len(graph[node])
        
        # Check for convergence
        diff = sum(abs(new_pr[node] - pr[node]) for node in graph)
        pr = new_pr
        
        if diff < epsilon:
            break
    
    return pr

# Example usage:
if __name__ == "__main__":
    # Example graph (node: [list of nodes it points to])
    # A simple web graph representation:
    # A -> B, C
    # B -> A, C, D
    # C -> A
    # D -> C
    graph = {
        'A': ['B', 'C'],
        'B': ['A', 'C', 'D'],
        'C': ['A'],
        'D': ['C']
    }
    
    # Calculate PageRank
    result = pagerank(graph)
    
    # Print results in descending order
    sorted_pr = sorted(result.items(), key=lambda x: x[1], reverse=True)
    print("PageRank Results:")
    for node, score in sorted_pr:
        print(f"Node {node}: {score:.6f}")
