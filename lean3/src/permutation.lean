def permutation (N : ℕ) := { l : list (fin N) // l.length = N ∧ ∀ n : fin N, l.any (λ n', n = n') }

def permutation.append {N M} : permutation N → permutation M → permutation (N + M) := sorry
def permutation.swap {N} (i j : fin N) : permutation N → permutation N := sorry
def permutation.compose {N} : permutation N → permutation N → permutation N := sorry

