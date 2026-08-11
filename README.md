# gd-attention-lean

This repository formalizes a minimal verified kernel of GD-Attention:
passage geometry, orthogonal rigidity, conditional lifting of axis
uniqueness, semantic-energy ordering, and deterministic finite-candidate
selection.

This is a Lean 4 formal specification and verification kernel, not an
executable GD-Attention runtime. In particular, `SelectionCertificate` and
`VerifiedSelection` are Lean proof objects, not JSON certificate checkers.

## What Is Verified

- The jump length and jump direction induced by two distinct centers.
- The second center lies at the endpoint of the passage determined by
  `jumpLength` and `jumpDirection`.
- Squared-distance decomposition into passage and orthogonal components.
- Orthogonal residuals give a minimum squared deviation from the passage.
- Positivity and factorization of the two-center Gaussian coherence score.
- Strict coherence decrease away from the passage when `0 < alpha < 1`.
- Semantic energy ordering as the reverse of coherence ordering.
- Strict semantic-energy increase away from the passage.
- Conditional lifting: if the one-dimensional axis coherence has a unique
  maximum, then full-space coherence has a unique passage maximum, and
  semantic energy has the corresponding unique minimum.
- Deterministic finite-candidate selection by minimum score, with least-index
  tie-break, and exact single-candidate output.

## What Is Not Verified

- GD-Attention as a complete AI system.
- Any learning algorithm, multi-head attention system, or empirical claim.
- Complex or Hermitian semantic spaces.
- Softmax impossibility or superiority claims.
- Unconditional uniqueness of the two-Gaussian energy for all `alpha` and `L`.
- The analytic `L^2 < 2` sufficient condition for axis uniqueness.

One-dimensional uniqueness is deliberately conditional:

```lean
hAxis : IsUniqueMaximum (axisCoherenceScore alpha L) xStar
```

This avoids the false unconditional claim that the two-Gaussian energy always
has a unique global optimum.

## Build

The project is pinned to Lean 4.26.0 and mathlib `v4.26.0`.

```bash
lake build
```

## Main Theorems

- `jumpLength_pos`
- `jumpDirection_unit`
- `second_center_eq_passage_endpoint`
- `jumpDirection_eq_zero_of_centers_eq`
- `squared_distance_to_mu1_decomposition`
- `squared_distance_to_mu2_decomposition`
- `distance_to_passage_decomposition`
- `orthogonalResidual_is_minimum_deviation`
- `coherenceScore_pos`
- `coherence_factorization`
- `coherence_factorization_between_centers`
- `semanticEnergy_le_iff_coherence_ge`
- `semanticEnergy_decomposition`
- `off_passage_coherence_strictly_lower`
- `off_passage_energy_strictly_higher`
- `unique_full_maximum_of_unique_axis_maximum`
- `unique_full_energy_minimum_of_unique_axis_coherence_maximum`
- `selected_index_is_optimal`
- `selected_index_is_least_among_ties`
- `selected_output_is_exact_candidate`
- `selected_is_optimal`
- `selected_is_least_among_ties`
- `selected_output_is_candidate`

## Axiom Check

Run `#print axioms` on the public theorems after `lake build`. In the local
verification run, the public theorems above depend only on standard
Lean/mathlib foundations:

```text
[propext, Classical.choice, Quot.sound]
```

There are no project-specific axioms and no incomplete proof placeholders.

## Files

```text
gd-attention-lean/
├─ GDAttention.lean
├─ README.md
├─ lakefile.toml
├─ lake-manifest.json
├─ lean-toolchain
├─ .gitignore
└─ .github/
   └─ workflows/
      └─ lean.yml
```
