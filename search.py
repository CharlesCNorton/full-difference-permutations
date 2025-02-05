
import itertools
import argparse
import json
import time
import logging
import concurrent.futures
import os

# Configure logging to output detailed debug info.
logging.basicConfig(level=logging.DEBUG,
                    format='%(asctime)s [%(levelname)s] %(message)s',
                    datefmt='%H:%M:%S')
logger = logging.getLogger(__name__)

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
    using a structured backtracking approach with sum heuristics.
    """
    n = len(perm)
    N = n + 4  # New total length
    start = n - patch_size  # Beginning index of the patch block
    fixed = perm[:start]
    D_fixed = {abs(fixed[i] - (i + 1)) for i in range(len(fixed))}
    L = patch_size + 4  # Length of patch block
    M = set(range(N)) - D_fixed  # Missing differences that must be introduced
    if len(M) != L:
        logger.debug(f"Patch size {patch_size}: Incompatible M, len(M)={len(M)} != L={L}")
        return None
    avail = [x for x in range(1, N + 1) if x not in set(fixed)]
    patch = [None] * L

    sum_M = sum(M)

    def backtrack(i, used, current_diffs):
        if i == L:
            return current_diffs == M
        pos = start + i  # Actual position (0-indexed)
        missing = M - current_diffs

        # Sum heuristic: Check if the remaining differences can reach the required sum.
        current_sum = sum(current_diffs)
        remaining_sum = sum_M - current_sum
        rem = L - i
        sorted_missing = sorted(missing)
        min_possible = sum(sorted_missing[:rem])
        max_possible = sum(sorted_missing[-rem:])
        if not (min_possible <= remaining_sum <= max_possible):
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
            logger.debug(f"Patch extension succeeded with patch_size={patch_size}")
            return candidate
    logger.debug(f"Patch extension failed for patch_size={patch_size}")
    return None

def build_full_diff_perm_refined(n, base_solution, max_patch):
    """
    Recursively build a full difference permutation for length n (n ≡ 0 or 1 mod 4)
    using structured patch extension with dynamic patch sizing.
    """
    if n in base_solution:
        return base_solution[n]
    prev_n = n - 4
    prev_perm = build_full_diff_perm_refined(prev_n, base_solution, max_patch)
    if prev_perm is None:
        logger.debug(f"Failed to build permutation for n = {prev_n}")
        return None
    for patch_size in range(0, max_patch + 1):
        logger.debug(f"Attempting extension from n = {prev_n} to n = {n} with patch_size = {patch_size}")
        candidate = structured_patch_extend_refined(prev_perm, patch_size)
        if candidate is not None:
            return candidate
    return None

def process_n(n, base_solution, max_patch):
    """
    Process a single n: build a full difference permutation for n and return the result
    along with timing information.
    """
    start_time = time.time()
    if n % 4 not in (0, 1):
        result = {
            'status': 'expected_failure',
            'message': f"n = {n}: No solution (n ≡ {n % 4} mod 4, as expected)",
            'time': 0
        }
    else:
        candidate = build_full_diff_perm_refined(n, base_solution, max_patch)
        elapsed = time.time() - start_time
        if candidate and verify_full_diff_perm(candidate):
            result = {
                'status': 'success',
                'solution': candidate,
                'message': f"n = {n}: Valid solution found",
                'time': elapsed
            }
        else:
            result = {
                'status': 'failure',
                'message': f"n = {n}: Failed to construct a valid solution",
                'time': elapsed
            }
    logger.info(f"Processed n = {n} in {result['time']:.2f} seconds: {result['message']}")
    return n, result

def automate_experiments(max_n, max_patch, output_file=None):
    """
    Automate the construction of full difference permutations for n in [1, max_n] in parallel.
    """
    base_solution = {
        1: [1],
        4: [2, 4, 3, 1],
        5: [3, 5, 2, 4, 1]
    }
    results = {}
    # Use all available CPU cores
    max_workers = os.cpu_count() or 4
    logger.info(f"Using {max_workers} worker processes.")
    with concurrent.futures.ProcessPoolExecutor(max_workers=max_workers) as executor:
        future_to_n = {executor.submit(process_n, n, base_solution, max_patch): n for n in range(1, max_n+1)}
        for future in concurrent.futures.as_completed(future_to_n):
            n, result = future.result()
            results[n] = result
    if output_file:
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
    return results

def main():
    parser = argparse.ArgumentParser(description="Automate experiments for full difference permutations")
    parser.add_argument("--max_n", type=int, default=25, help="Maximum n to test (default: 25)")
    parser.add_argument("--max_patch", type=int, default=20, help="Maximum patch size to try (default: 20)")
    parser.add_argument("--output", type=str, help="Output file to store results in JSON format")
    args = parser.parse_args()
    
    results = automate_experiments(args.max_n, args.max_patch, args.output)
    
    for n in sorted(results.keys()):
        print(f"n = {n}: {results[n]}")

if __name__ == "__main__":
    main()
