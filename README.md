# Full Difference Permutations: A Comprehensive Work-in-Progress Document

By: Charles Norton & o3-mini-high

February 4th, 2025

---

## Table of Contents

1. [Introduction](#introduction)  
   1.1 [Problem Statement](#problem-statement)  
   1.2 [Motivation and Significance](#motivation-and-significance)  

2. [Overview of the Approach](#overview-of-the-approach)  
   2.1 [Base Cases](#base-cases)  
   2.2 [Inductive Step via Patch Extension](#inductive-step-via-patch-extension)  
   2.3 [Structured Backtracking](#structured-backtracking)  

3. [Current Verification Program](#current-verification-program)  
   3.1 [Program Description](#program-description)  
   3.2 [Code Listing](#code-listing)  

4. [Empirical Results and Analysis](#empirical-results-and-analysis)  
   4.1 [Valid Constructions](#valid-constructions)  
   4.2 [Observed Challenges](#observed-challenges)  

5. [Future Directions and Refinement](#future-directions-and-refinement)  
   5.1 [Theoretical Refinements](#theoretical-refinements)  
   5.2 [Algorithmic Enhancements](#algorithmic-enhancements)  

6. [Conclusion](#conclusion)

7. [Appendix](#appendix)  
   7.1 [Glossary](#glossary)  
   7.2 [Detailed Experimental Data](#detailed-experimental-data)  
   7.3 [Additional References and Notes](#additional-references-and-notes)

---

## 1. Introduction

### 1.1 Problem Statement

Let [n] = {1, 2, …, n}. A permutation  
  π : [n] → [n]  
is said to be a full difference permutation if the set of absolute differences

  D(π) = { |π(i) − i| : i ∈ [n] }

equals exactly

  { 0, 1, 2, …, n − 1 }.

The open problem we address is:

For which positive integers n does there exist a full difference permutation?

It is known (via parity and summation arguments) that a necessary condition for the existence of such a permutation is  
  n ≡ 0 or 1 (mod 4).  
Our goal is to prove that a full difference permutation exists if and only if n ≡ 0 or 1 (mod 4). Moreover, we aim to provide an explicit, algorithmic construction for these permutations.

### 1.2 Motivation and Significance

Full difference permutations are intriguing because they enforce a highly regular structure on the differences between each element’s value and its position. Such objects relate to various topics in combinatorial design theory, graceful labelings, and difference set problems. A constructive, inductive proof of their existence for all admissible n would not only resolve a natural combinatorial problem but could also open new avenues for research in both theory and algorithm design.

---

## 2. Overview of the Approach

### 2.1 Base Cases

We begin by directly constructing full difference permutations for small admissible values:

- n = 1:  
  The only permutation is [1], and  
  D([1]) = { |1 − 1| } = { 0 }.

- n = 4:  
  An example is [2, 4, 3, 1]. The differences are:
  
  |2 − 1| = 1, |4 − 2| = 2, |3 − 3| = 0, |1 − 4| = 3,  

  so D([2, 4, 3, 1]) = { 0, 1, 2, 3 }.

- n = 5:  
  An example is [3, 5, 2, 4, 1], which yields
  
  D([3, 5, 2, 4, 1]) = { 2, 3, 1, 0, 4 } = { 0, 1, 2, 3, 4 }.

These serve as our base solutions for the inductive construction.

### 2.2 Inductive Step via Patch Extension

Assume we have a full difference permutation π on [n] such that

  D(π) = { 0, 1, …, n − 1 }.

We wish to extend π to a permutation σ on [n + 4] satisfying

  D(σ) = { 0, 1, …, n + 3 }.

A naïve extension (for example, simply appending 4 new elements) does not guarantee that the new differences will exactly match the missing ones. Instead, we reassign a block—a *patch*—from the tail of the permutation together with the 4 new positions.

Let k be the number of tail positions we choose to reassign along with the new 4 positions. This gives a patch block of length

  L = k + 4.

We leave the first n − k positions unchanged (the fixed part) and reassign positions n − k + 1 through n + 4 (the patch block).

Let  
  D_fixed = { |π(i) − i| : i = 1, …, n − k }  
be the differences contributed by the fixed part. The complete difference set for a permutation of [n + 4] is

  { 0, 1, …, n + 3 }.

Thus, the patch block must produce the missing differences

  M = { 0, 1, …, n + 3 } ∖ D_fixed.

Our task is to assign values to the patch block so that the set of absolute differences in these positions is exactly M.

### 2.3 Structured Backtracking

To solve the assignment problem for the patch block, we use a structured backtracking algorithm that:

- Assigns values to the patch block one position at a time.
- At each step, enforces that the accumulated differences, together with the remaining positions, can cover the missing differences M.
- Prunes infeasible assignments early to reduce the search space.

This systematic approach transforms the extension problem into a constrained search, where the objective is to find an assignment for the patch block that “completes” the difference set.

---

## 3. Current Verification Program

### 3.1 Program Description

Our current program implements the following components:

- verify_full_diff_perm:  
  A function that checks whether a given permutation has the full difference property.

- structured_patch_extend_refined:  
  A function that attempts to extend a full difference permutation of length n to one of length n + 4 by reassigning the last patch_size positions together with 4 new positions using a backtracking strategy. It constructs a patch block such that the differences in that block exactly match the missing differences.

- build_full_diff_perm_refined:  
  A recursive function that, starting from the base cases, builds a full difference permutation for a given n (where n ≡ 0 or 1 mod 4) by repeatedly applying the structured patch extension.

- main:  
  A driver function that tests the construction for n from 1 to 25 and prints the results.

### 3.2 Code Listing

```python
import itertools

def verify_full_diff_perm(perm):
    """
    Verify that for a permutation 'perm' of [1, 2, …, n],
    the set of absolute differences |perm[i] - (i+1)| equals {0, 1, …, n-1}.
    """
    n = len(perm)
    differences = {abs(perm[i] - (i + 1)) for i in range(n)}
    return differences == set(range(n))

def structured_patch_extend_refined(perm, patch_size):
    """
    Extend a full difference permutation 'perm' (of length n) to one of length n+4
    by reassigning the last 'patch_size' positions together with the 4 new positions,
    using a structured backtracking approach.
    
    Parameters:
      perm       : list, a valid full difference permutation of [1,..., n]
      patch_size : int, the number of tail positions from 'perm' to reassign
      
    Returns:
      A candidate permutation of length n+4 with the full difference property,
      or None if not found.
    """
    n = len(perm)
    N = n + 4  # New total length
    start = n - patch_size  # Position where the patch begins
    fixed = perm[:start]
    D_fixed = {abs(fixed[i] - (i + 1)) for i in range(len(fixed))}
    L = patch_size + 4  # Length of the patch block
    M = set(range(N)) - D_fixed  # Missing differences to be introduced
    if len(M) != L:
        return None
    # Available numbers for the patch block: those not used in the fixed part.
    avail = [x for x in range(1, N + 1) if x not in set(fixed)]
    patch = [None] * L

    def backtrack(i, used, current_diffs):
        if i == L:
            return current_diffs == M
        pos = start + i  # Actual position (0-indexed) in the extended permutation
        missing = M - current_diffs
        # Prune: if the number of positions remaining doesn't equal the number of missing differences.
        if len(missing) != (L - i):
            return False
        for val in sorted(avail, key=lambda v: abs(v - (pos + 1))):
            if val in used:
                continue
            diff = abs(val - (pos + 1))
            if diff not in missing:
                continue
            patch[i] = val
            used.add(val)
            current_diffs.add(diff)
            if backtrack(i + 1, used, current_diffs):
                return True
            used.remove(val)
            current_diffs.remove(diff)
        return False

    used = set()
    current_diffs = set()
    if backtrack(0, used, current_diffs):
        candidate = fixed + patch
        if verify_full_diff_perm(candidate):
            return candidate
    return None

def build_full_diff_perm_refined(n, base_solution, max_patch=20):
    """
    Recursively build a full difference permutation for length n (n ≡ 0 or 1 mod 4)
    using the structured patch extension method.
    
    Parameters:
      n             : target length
      base_solution : dictionary mapping small admissible n to known valid permutations
      max_patch     : maximum patch size (number of positions to reassign) to try
      
    Returns:
      A valid full difference permutation (list) for length n, or None if not found.
    """
    if n in base_solution:
        return base_solution[n]
    prev_n = n - 4
    prev_perm = build_full_diff_perm_refined(prev_n, base_solution, max_patch)
    if prev_perm is None:
        return None
    for patch_size in range(0, max_patch + 1):
        candidate = structured_patch_extend_refined(prev_perm, patch_size)
        if candidate is not None:
            return candidate
    return None

def main():
    # Define base solutions for small admissible n.
    base_solution = {
        1: [1],
        4: [2, 4, 3, 1],
        5: [3, 5, 2, 4, 1]
    }
    
    results = {}
    # Test for n from 1 up to 25.
    for n in range(1, 26):
        if n % 4 not in (0, 1):
            results[n] = f"n = {n}: No solution (n ≡ {n % 4} mod 4, as expected)"
        else:
            candidate = build_full_diff_perm_refined(n, base_solution, max_patch=20)
            if candidate and verify_full_diff_perm(candidate):
                results[n] = f"n = {n}: Valid solution: {candidate}"
            else:
                results[n] = f"n = {n}: Failed to construct a valid solution"
    
    for n in sorted(results.keys()):
        print(results[n])

if __name__ == "__main__":
    main()
```

---

## 4. Empirical Results and Analysis

### 4.1 Valid Constructions

Our current implementation yields valid full difference permutations for several values:
- n = 1: [1]
- n = 4: [2, 4, 3, 1]
- n = 5: [3, 5, 2, 4, 1]
- n = 8 and n = 9: Valid extensions were found.
- n = 12 and n = 13: Valid solutions were constructed.

### 4.2 Observed Challenges

For some larger values (e.g., n = 16, 17, 20, 21, etc.), our program currently fails to construct a valid solution. This indicates that as n increases, the combinatorial constraints in the patch extension become more challenging to satisfy. These failures point to the need for further refinement in our method, such as:
- Allowing a larger or dynamically chosen patch size.
- Improving the heuristics in the backtracking algorithm.
- Performing deeper theoretical analysis of the structure of the missing difference set M.

---

## 5. Future Directions and Refinement

### 5.1 Theoretical Refinements

- Uniform Bound on Patch Size:  
  A central theoretical question is whether there exists a uniform bound (or a bound that grows slowly with n) on the patch size required to extend a full difference permutation from n to n + 4. Proving such a bound would be a significant step toward a complete inductive proof.

- Constraint Analysis:  
  A deeper examination of the missing difference set M may yield insights that lead to stronger pruning criteria or more efficient assignment strategies in the backtracking process.

### 5.2 Algorithmic Enhancements

- Dynamic Patch Sizing:  
  Future implementations may incorporate a dynamic strategy to determine the minimal necessary patch size for each extension step, rather than relying on a fixed maximum.

- Enhanced Heuristics:  
  Incorporating heuristics based on the structure of M—such as prioritizing assignments that cover the largest missing differences—may further reduce the search space and improve success rates.

- Optimization for Larger n:  
  As n grows, the algorithm will need additional optimizations, which could include hybrid approaches that combine our structured patch method with other constructive techniques.

### 5.3 Concluding Remarks

Our comprehensive document presents the current state of our work on full difference permutations, including:
- A detailed statement of the open problem.
- An inductive construction strategy based on patch extension.
- A complete Python verification program.
- Empirical results and analysis.
- A discussion of challenges and avenues for further refinement.

While our method remains a work in progress (WIP), the progress so far is promising. We have demonstrated valid constructions for a range of small values of n and identified key challenges that must be addressed to extend the method to all admissible n. Continued research and refinement—both theoretically and algorithmically—will be essential to fully resolve this intriguing combinatorial problem.

---

## 6. Conclusion

In this document, we have:
- Stated the open problem of full difference permutations.
- Outlined a rigorous inductive approach, based on reassigning a patch from the tail of the permutation along with new positions.
- Developed and presented a verification program in Python.
- Analyzed empirical results and identified areas for further improvement.

Our work in progress lays a strong foundation for future research. With additional theoretical insights and algorithmic optimizations, we aim to eventually prove that a full difference permutation exists for all n with n ≡ 0 or 1 (mod 4).

---

## 7. Appendix

### 7.1 Glossary

- Full Difference Permutation: A permutation π of [n] where D(π) = { |π(i) − i| : i ∈ [n] } equals { 0, 1, …, n − 1 }.
- Patch Extension: A method of extending a full difference permutation from [n] to [n + 4] by reassigning a block (the patch) that includes a subset of the tail positions along with 4 new positions.
- Backtracking: A systematic search method used to explore all possible assignments in the patch extension while pruning infeasible paths.

### 7.2 Detailed Experimental Data

*Note: This section includes logs and data from multiple test runs. The current version of our program successfully constructs valid permutations for n = 1, 4, 5, 8, 9, 12, and 13. For larger values (e.g., n = 16, 17, 20, 21), our algorithm has not yet produced valid solutions. Detailed logs are maintained separately for further analysis.*

### 7.3 Additional References and Notes

- Graceful Labelings and Difference Sets:  
  The concept of full difference permutations is closely related to graceful labelings of graphs and Golomb rulers. Several research articles in combinatorial design theory provide background on similar problems.
  
- Future Theoretical Work:  
  A formal proof of the inductive step (i.e., the existence of a bounded patch extension for all admissible n) remains an open challenge. This document serves as a preliminary exploration towards that goal.
