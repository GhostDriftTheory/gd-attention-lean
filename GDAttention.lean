import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# GD-Attention Minimal Verified Kernel

This file is a compact Lean 4 formal specification of the mathematical kernel
used by GD-Attention: passage geometry, orthogonal rigidity, conditional
coherence/energy optimality, deterministic finite-candidate selection, and
proof objects for selected outputs.
-/

noncomputable section

namespace GDAttention

/-!
## 1. Passage Geometry
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Squared norm, used as squared semantic distance. -/
def normSq (v : E) : Real :=
  norm v ^ 2

/-- Euclidean length of the jump between two concept centers. -/
def jumpLength (mu1 mu2 : E) : Real :=
  norm (mu2 - mu1)

/-- Unit jump direction when the centers are distinct, and zero otherwise. -/
def jumpDirection (mu1 mu2 : E) : E :=
  (jumpLength mu1 mu2)⁻¹ • (mu2 - mu1)

/-- Point on the semantic passage through `mu1` in direction `g`. -/
def passagePoint (mu1 g : E) (x : Real) : E :=
  mu1 + x • g

/-- Coordinate of a point along a unit passage direction. -/
def axisCoord (mu1 g s : E) : Real :=
  inner Real g (s - mu1)

/-- Residual after removing the passage component. -/
def orthogonalResidual (mu1 g s : E) : E :=
  s - mu1 - axisCoord mu1 g s • g

theorem point_decomposition (mu1 g s : E) :
    s = mu1 + axisCoord mu1 g s • g + orthogonalResidual mu1 g s := by
  simp [orthogonalResidual, axisCoord]

theorem jumpDirection_eq_zero_of_centers_eq {mu1 mu2 : E} (h : mu1 = mu2) :
    jumpDirection mu1 mu2 = 0 := by
  subst mu2
  simp [jumpDirection, jumpLength]

omit [InnerProductSpace Real E] in
theorem jumpLength_pos {mu1 mu2 : E} (hneq : mu1 ≠ mu2) :
    0 < jumpLength mu1 mu2 := by
  unfold jumpLength
  rw [norm_pos_iff]
  intro hsub
  apply hneq
  exact (sub_eq_zero.mp hsub).symm

theorem jumpDirection_unit {mu1 mu2 : E} (hneq : mu1 ≠ mu2) :
    norm (jumpDirection mu1 mu2) = 1 := by
  have hpos : 0 < jumpLength mu1 mu2 := jumpLength_pos hneq
  calc
    norm (jumpDirection mu1 mu2)
        = |(jumpLength mu1 mu2)⁻¹| * norm (mu2 - mu1) := by
            simp [jumpDirection, norm_smul, Real.norm_eq_abs]
    _ = (jumpLength mu1 mu2)⁻¹ * jumpLength mu1 mu2 := by
            rw [abs_of_pos (inv_pos.mpr hpos)]
            rfl
    _ = 1 := by
            exact inv_mul_cancel₀ hpos.ne'

theorem second_center_eq_passage_endpoint {mu1 mu2 : E} (hneq : mu1 ≠ mu2) :
    mu2 = mu1 + jumpLength mu1 mu2 • jumpDirection mu1 mu2 := by
  have hne : jumpLength mu1 mu2 ≠ 0 := (jumpLength_pos hneq).ne'
  unfold jumpDirection
  rw [smul_smul, mul_inv_cancel₀ hne]
  simp

theorem orthogonalResidual_orthogonal
    (mu1 g s : E) (hg : norm g = 1) :
    inner Real g (orthogonalResidual mu1 g s) = 0 := by
  simp [orthogonalResidual, axisCoord, inner_sub_right, real_inner_smul_right, hg]

theorem normSq_smul_of_unit (x : Real) {g : E} (hg : norm g = 1) :
    normSq (x • g) = x ^ 2 := by
  simp [normSq, norm_smul, hg, Real.norm_eq_abs, sq_abs]

/-- Distance from a passage point plus an orthogonal residual to the first center. -/
theorem squared_distance_to_mu1_decomposition
    (mu1 g y : E) (x : Real)
    (hg : norm g = 1) (hy : inner Real g y = 0) :
    normSq ((mu1 + x • g + y) - mu1) = x ^ 2 + normSq y := by
  have hinner : inner Real (x • g) y = 0 := by
    simp [real_inner_smul_left, hy]
  calc
    normSq ((mu1 + x • g + y) - mu1)
        = normSq (x • g + y) := by
            congr 1
            abel
    _ = normSq (x • g) + normSq y := by
            simpa [normSq, pow_two] using
              (norm_add_sq_eq_norm_sq_add_norm_sq_real (x := x • g) (y := y) hinner)
    _ = x ^ 2 + normSq y := by
            rw [normSq_smul_of_unit x hg]

/-- Distance from a passage point plus an orthogonal residual to the second center. -/
theorem squared_distance_to_mu2_decomposition
    (mu1 mu2 g y : E) (x L : Real)
    (hg : norm g = 1) (hy : inner Real g y = 0)
    (hmu2 : mu2 = mu1 + L • g) :
    normSq ((mu1 + x • g + y) - mu2) = (x - L) ^ 2 + normSq y := by
  subst mu2
  have hinner : inner Real ((x - L) • g) y = 0 := by
    simp [real_inner_smul_left, hy]
  calc
    normSq ((mu1 + x • g + y) - (mu1 + L • g))
        = normSq ((x - L) • g + y) := by
            congr 1
            rw [sub_smul]
            abel
    _ = normSq ((x - L) • g) + normSq y := by
            simpa [normSq, pow_two] using
              (norm_add_sq_eq_norm_sq_add_norm_sq_real
                (x := (x - L) • g) (y := y) hinner)
    _ = (x - L) ^ 2 + normSq y := by
            rw [normSq_smul_of_unit (x - L) hg]

theorem distance_to_passage_decomposition
    (mu1 g y : E) (x t : Real)
    (hg : norm g = 1) (hy : inner Real g y = 0) :
    normSq ((mu1 + x • g + y) - passagePoint mu1 g t)
      = (x - t) ^ 2 + normSq y := by
  simpa [passagePoint] using
    squared_distance_to_mu2_decomposition
      (mu1 := mu1) (mu2 := passagePoint mu1 g t) (g := g) (y := y)
      (x := x) (L := t) hg hy rfl

theorem orthogonalResidual_is_minimum_deviation
    (mu1 g s : E) (hg : norm g = 1) (t : Real) :
    normSq (orthogonalResidual mu1 g s) ≤
      normSq (s - passagePoint mu1 g t) := by
  let x := axisCoord mu1 g s
  let y := orthogonalResidual mu1 g s
  have hdecomp : s = mu1 + x • g + y := by
    simpa [x, y] using point_decomposition (mu1 := mu1) (g := g) (s := s)
  have hy : inner Real g y = 0 := by
    simpa [y] using orthogonalResidual_orthogonal (mu1 := mu1) (g := g) (s := s) hg
  have hdist :
      normSq (s - passagePoint mu1 g t) = (x - t) ^ 2 + normSq y := by
    rw [hdecomp]
    exact distance_to_passage_decomposition
      (mu1 := mu1) (g := g) (y := y) (x := x) (t := t) hg hy
  rw [hdist]
  exact le_add_of_nonneg_left (sq_nonneg (x - t))

/-!
## 2. Coherence, Energy, And Rigidity
-/

/-- Positive coherence score for the two-center Gaussian kernel. -/
def coherenceScore (alpha : Real) (mu1 mu2 s : E) : Real :=
  alpha * Real.exp (-(normSq (s - mu1))) +
    (1 - alpha) * Real.exp (-(normSq (s - mu2)))

/-- One-dimensional coherence score along a passage of length `L`. -/
def axisCoherenceScore (alpha L x : Real) : Real :=
  alpha * Real.exp (-(x ^ 2)) +
    (1 - alpha) * Real.exp (-((x - L) ^ 2))

/-- Semantic energy, defined as the negative logarithm of coherence. -/
def semanticEnergy (alpha : Real) (mu1 mu2 s : E) : Real :=
  -Real.log (coherenceScore alpha mu1 mu2 s)

/-- Axis energy induced by the axis coherence score. -/
def axisSemanticEnergy (alpha L x : Real) : Real :=
  -Real.log (axisCoherenceScore alpha L x)

/-- A point is a unique maximum when it is maximal and equality forces identity. -/
def IsUniqueMaximum {X : Type*} (f : X -> Real) (xStar : X) : Prop :=
  (forall x, f x <= f xStar) /\ (forall x, f x = f xStar -> x = xStar)

/-- A point is a unique minimum when it is minimal and equality forces identity. -/
def IsUniqueMinimum {X : Type*} (f : X -> Real) (xStar : X) : Prop :=
  (forall x, f xStar <= f x) /\ (forall x, f x = f xStar -> x = xStar)

theorem axisCoherenceScore_pos
    {alpha L x : Real} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    0 < axisCoherenceScore alpha L x := by
  have h1 : 0 < alpha * Real.exp (-(x ^ 2)) :=
    mul_pos halpha0 (Real.exp_pos _)
  have h2 : 0 < (1 - alpha) * Real.exp (-((x - L) ^ 2)) := by
    exact mul_pos (sub_pos.mpr halpha1) (Real.exp_pos _)
  exact add_pos h1 h2

omit [InnerProductSpace Real E] in
theorem coherenceScore_pos
    {alpha : Real} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (mu1 mu2 s : E) :
    0 < coherenceScore alpha mu1 mu2 s := by
  have h1 : 0 < alpha * Real.exp (-(normSq (s - mu1))) :=
    mul_pos halpha0 (Real.exp_pos _)
  have h2 : 0 < (1 - alpha) * Real.exp (-(normSq (s - mu2))) := by
    exact mul_pos (sub_pos.mpr halpha1) (Real.exp_pos _)
  exact add_pos h1 h2

theorem coherence_factorization
    (alpha L x : Real) (mu1 mu2 g y : E)
    (hg : norm g = 1) (hy : inner Real g y = 0)
    (hmu2 : mu2 = mu1 + L • g) :
    coherenceScore alpha mu1 mu2 (mu1 + x • g + y)
      = Real.exp (-(normSq y)) * axisCoherenceScore alpha L x := by
  have h1 :=
    squared_distance_to_mu1_decomposition
      (mu1 := mu1) (g := g) (y := y) (x := x) hg hy
  have h2 :=
    squared_distance_to_mu2_decomposition
      (mu1 := mu1) (mu2 := mu2) (g := g) (y := y) (x := x) (L := L) hg hy hmu2
  rw [coherenceScore, axisCoherenceScore, h1, h2]
  have hexp1 :
      Real.exp (-(x ^ 2 + normSq y))
        = Real.exp (-(normSq y)) * Real.exp (-(x ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp2 :
      Real.exp (-((x - L) ^ 2 + normSq y))
        = Real.exp (-(normSq y)) * Real.exp (-((x - L) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp1, hexp2]
  ring

theorem coherence_factorization_between_centers
    {alpha x : Real} {mu1 mu2 y : E}
    (hneq : mu1 ≠ mu2)
    (hy : inner Real (jumpDirection mu1 mu2) y = 0) :
    coherenceScore alpha mu1 mu2 (mu1 + x • jumpDirection mu1 mu2 + y)
      = Real.exp (-(normSq y)) *
          axisCoherenceScore alpha (jumpLength mu1 mu2) x := by
  exact coherence_factorization
    (alpha := alpha) (L := jumpLength mu1 mu2) (x := x)
    (mu1 := mu1) (mu2 := mu2) (g := jumpDirection mu1 mu2) (y := y)
    (jumpDirection_unit hneq) hy (second_center_eq_passage_endpoint hneq)

theorem coherence_on_passage
    (alpha L x : Real) (mu1 mu2 g : E)
    (hg : norm g = 1) (hmu2 : mu2 = mu1 + L • g) :
    coherenceScore alpha mu1 mu2 (passagePoint mu1 g x)
      = axisCoherenceScore alpha L x := by
  have h0 : inner Real g (0 : E) = 0 := by simp
  have hfact :=
    coherence_factorization
      (alpha := alpha) (L := L) (x := x) (mu1 := mu1) (mu2 := mu2)
      (g := g) (y := (0 : E)) hg h0 hmu2
  simpa [passagePoint, normSq] using hfact

omit [InnerProductSpace Real E] in
theorem exp_neg_normSq_lt_one {y : E} (hy : y ≠ 0) :
    Real.exp (-(normSq y)) < 1 := by
  have hypos : 0 < normSq y := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hy)
  exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hypos)

omit [InnerProductSpace Real E] in
theorem exp_neg_normSq_le_one (y : E) :
    Real.exp (-(normSq y)) <= 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg (norm y)))

omit [InnerProductSpace Real E] in
theorem semanticEnergy_le_iff_coherence_ge
    {alpha : Real} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (mu1 mu2 s t : E) :
    semanticEnergy alpha mu1 mu2 s <= semanticEnergy alpha mu1 mu2 t ↔
      coherenceScore alpha mu1 mu2 t <= coherenceScore alpha mu1 mu2 s := by
  have hspos := coherenceScore_pos
    (alpha := alpha) halpha0 halpha1 mu1 mu2 s
  have htpos := coherenceScore_pos
    (alpha := alpha) halpha0 halpha1 mu1 mu2 t
  constructor
  · intro h
    have hlog :
        Real.log (coherenceScore alpha mu1 mu2 t) <=
          Real.log (coherenceScore alpha mu1 mu2 s) := by
      unfold semanticEnergy at h
      linarith
    exact (Real.log_le_log_iff htpos hspos).1 hlog
  · intro h
    have hlog :
        Real.log (coherenceScore alpha mu1 mu2 t) <=
          Real.log (coherenceScore alpha mu1 mu2 s) :=
      (Real.log_le_log_iff htpos hspos).2 h
    unfold semanticEnergy
    linarith

theorem semanticEnergy_decomposition
    {alpha L x : Real} {mu1 mu2 g y : E}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hg : norm g = 1) (hy : inner Real g y = 0)
    (hmu2 : mu2 = mu1 + L • g) :
    semanticEnergy alpha mu1 mu2 (mu1 + x • g + y)
      = normSq y + axisSemanticEnergy alpha L x := by
  have hfact :=
    coherence_factorization
      (alpha := alpha) (L := L) (x := x) (mu1 := mu1) (mu2 := mu2)
      (g := g) (y := y) hg hy hmu2
  have haxispos : 0 < axisCoherenceScore alpha L x :=
    axisCoherenceScore_pos (alpha := alpha) (L := L) (x := x) halpha0 halpha1
  unfold semanticEnergy axisSemanticEnergy
  rw [hfact]
  rw [Real.log_mul (Real.exp_ne_zero _) haxispos.ne']
  rw [Real.log_exp]
  ring

theorem off_passage_coherence_strictly_lower
    {alpha L x : Real} {mu1 mu2 g y : E}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hg : norm g = 1) (hy : inner Real g y = 0) (hyne : y ≠ 0)
    (hmu2 : mu2 = mu1 + L • g) :
    coherenceScore alpha mu1 mu2 (mu1 + x • g + y)
      < coherenceScore alpha mu1 mu2 (passagePoint mu1 g x) := by
  rw [coherence_factorization
    (alpha := alpha) (L := L) (x := x) (mu1 := mu1) (mu2 := mu2)
    (g := g) (y := y) hg hy hmu2]
  rw [coherence_on_passage
    (alpha := alpha) (L := L) (x := x) (mu1 := mu1) (mu2 := mu2)
    (g := g) hg hmu2]
  exact mul_lt_of_lt_one_left
    (axisCoherenceScore_pos (alpha := alpha) (L := L) (x := x) halpha0 halpha1)
    (exp_neg_normSq_lt_one (y := y) hyne)

theorem off_passage_energy_strictly_higher
    {alpha L x : Real} {mu1 mu2 g y : E}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hg : norm g = 1) (hy : inner Real g y = 0) (hyne : y ≠ 0)
    (hmu2 : mu2 = mu1 + L • g) :
    semanticEnergy alpha mu1 mu2 (mu1 + x • g + y)
      > semanticEnergy alpha mu1 mu2 (passagePoint mu1 g x) := by
  have hstrict :
      coherenceScore alpha mu1 mu2 (mu1 + x • g + y)
        < coherenceScore alpha mu1 mu2 (passagePoint mu1 g x) :=
    off_passage_coherence_strictly_lower
      (alpha := alpha) (L := L) (x := x) (mu1 := mu1) (mu2 := mu2)
      (g := g) (y := y) halpha0 halpha1 hg hy hyne hmu2
  have hoffpos := coherenceScore_pos
    (alpha := alpha) halpha0 halpha1 mu1 mu2 (mu1 + x • g + y)
  have hlog := Real.log_lt_log hoffpos hstrict
  unfold semanticEnergy
  linarith

theorem unique_full_maximum_of_unique_axis_maximum
    {alpha L xStar : Real} {mu1 mu2 g : E}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hg : norm g = 1) (hmu2 : mu2 = mu1 + L • g)
    (hAxis : IsUniqueMaximum (axisCoherenceScore alpha L) xStar) :
    IsUniqueMaximum (fun s : E => coherenceScore alpha mu1 mu2 s)
      (passagePoint mu1 g xStar) := by
  constructor
  · intro s
    let x := axisCoord mu1 g s
    let y := orthogonalResidual mu1 g s
    have hdecomp : s = mu1 + x • g + y := by
      simpa [x, y] using point_decomposition (mu1 := mu1) (g := g) (s := s)
    have hy : inner Real g y = 0 := by
      simpa [y] using orthogonalResidual_orthogonal (mu1 := mu1) (g := g) (s := s) hg
    rw [hdecomp]
    change coherenceScore alpha mu1 mu2 (mu1 + x • g + y) <=
      coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar)
    rw [coherence_factorization
      (alpha := alpha) (L := L) (x := x) (mu1 := mu1) (mu2 := mu2)
      (g := g) (y := y) hg hy hmu2]
    rw [coherence_on_passage
      (alpha := alpha) (L := L) (x := xStar) (mu1 := mu1) (mu2 := mu2)
      (g := g) hg hmu2]
    exact le_trans
      (mul_le_of_le_one_left
        (le_of_lt (axisCoherenceScore_pos (alpha := alpha) (L := L) (x := x) halpha0 halpha1))
        (exp_neg_normSq_le_one (y := y)))
      (hAxis.1 x)
  · intro s hs
    let x := axisCoord mu1 g s
    let y := orthogonalResidual mu1 g s
    have hdecomp : s = mu1 + x • g + y := by
      simpa [x, y] using point_decomposition (mu1 := mu1) (g := g) (s := s)
    have hy : inner Real g y = 0 := by
      simpa [y] using orthogonalResidual_orthogonal (mu1 := mu1) (g := g) (s := s) hg
    have hAxisLe : axisCoherenceScore alpha L x <= axisCoherenceScore alpha L xStar := hAxis.1 x
    have hnot : Not (y ≠ 0) := by
      intro hyne
      have hstrict :
          coherenceScore alpha mu1 mu2 (mu1 + x • g + y)
            < coherenceScore alpha mu1 mu2 (passagePoint mu1 g x) :=
        off_passage_coherence_strictly_lower
          (alpha := alpha) (L := L) (x := x) (mu1 := mu1) (mu2 := mu2)
          (g := g) (y := y) halpha0 halpha1 hg hy hyne hmu2
      have hpass :
          coherenceScore alpha mu1 mu2 (passagePoint mu1 g x)
            = axisCoherenceScore alpha L x :=
        coherence_on_passage
          (alpha := alpha) (L := L) (x := x) (mu1 := mu1) (mu2 := mu2)
          (g := g) hg hmu2
      have hstar :
          coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar)
            = axisCoherenceScore alpha L xStar :=
        coherence_on_passage
          (alpha := alpha) (L := L) (x := xStar) (mu1 := mu1) (mu2 := mu2)
          (g := g) hg hmu2
      have hlt :
          coherenceScore alpha mu1 mu2 s
            < coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar) := by
        rw [hdecomp]
        have hstrictAxis :
            coherenceScore alpha mu1 mu2 (mu1 + x • g + y)
              < axisCoherenceScore alpha L x := by
          simpa [hpass] using hstrict
        rw [hstar]
        exact lt_of_lt_of_le hstrictAxis hAxisLe
      have hbad :
          coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar) <
            coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar) := by
        have hs' :
            coherenceScore alpha mu1 mu2 s =
              coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar) := hs
        rw [hs'] at hlt
        exact hlt
      exact (lt_irrefl (coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar))) hbad
    have hyzero : y = 0 := by exact of_not_not hnot
    have haxisEq : axisCoherenceScore alpha L x = axisCoherenceScore alpha L xStar := by
      have hleft :
          coherenceScore alpha mu1 mu2 s = axisCoherenceScore alpha L x := by
        rw [hdecomp, hyzero]
        simpa [passagePoint] using coherence_on_passage
          (alpha := alpha) (L := L) (x := x) (mu1 := mu1) (mu2 := mu2)
          (g := g) hg hmu2
      have hstar :
          coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar)
            = axisCoherenceScore alpha L xStar :=
        coherence_on_passage
          (alpha := alpha) (L := L) (x := xStar) (mu1 := mu1) (mu2 := mu2)
          (g := g) hg hmu2
      simpa [hleft, hstar] using hs
    have hx : x = xStar := hAxis.2 x haxisEq
    rw [hdecomp, hyzero, hx]
    simp [passagePoint]

theorem unique_full_energy_minimum_of_unique_axis_coherence_maximum
    {alpha L xStar : Real} {mu1 mu2 g : E}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hg : norm g = 1) (hmu2 : mu2 = mu1 + L • g)
    (hAxis : IsUniqueMaximum (axisCoherenceScore alpha L) xStar) :
    IsUniqueMinimum (fun s : E => semanticEnergy alpha mu1 mu2 s)
      (passagePoint mu1 g xStar) := by
  have hFull :=
    unique_full_maximum_of_unique_axis_maximum
      (alpha := alpha) (L := L) (xStar := xStar)
      (mu1 := mu1) (mu2 := mu2) (g := g)
      halpha0 halpha1 hg hmu2 hAxis
  constructor
  · intro s
    exact
      (semanticEnergy_le_iff_coherence_ge
        (alpha := alpha) halpha0 halpha1 mu1 mu2
        (passagePoint mu1 g xStar) s).2 (hFull.1 s)
  · intro s hs
    have hle1 :
        coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar) <=
          coherenceScore alpha mu1 mu2 s := by
      exact
        (semanticEnergy_le_iff_coherence_ge
          (alpha := alpha) halpha0 halpha1 mu1 mu2 s
          (passagePoint mu1 g xStar)).1 (le_of_eq hs)
    have hle2 :
        coherenceScore alpha mu1 mu2 s <=
          coherenceScore alpha mu1 mu2 (passagePoint mu1 g xStar) := by
      exact
        (semanticEnergy_le_iff_coherence_ge
          (alpha := alpha) halpha0 halpha1 mu1 mu2
          (passagePoint mu1 g xStar) s).1 (le_of_eq hs.symm)
    exact hFull.2 s (le_antisymm hle2 hle1)

/-!
## 3. Deterministic Finite Selection
-/

variable {n : Nat} [NeZero n]

theorem exists_selected_index_spec (score : Fin n -> Real) :
    Exists fun i : Fin n =>
      (forall j : Fin n, score i <= score j) /\
      (forall j : Fin n, score j = score i -> i <= j) := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨0, by simp⟩
  obtain ⟨i0, _hi0mem, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin n)) score huniv
  let ties : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun i => score i = score i0
  have hties : ties.Nonempty := by
    refine ⟨i0, ?_⟩
    simp [ties]
  let i : Fin n := ties.min' hties
  have hi_mem : i ∈ ties := by
    exact Finset.min'_mem ties hties
  have hi_score : score i = score i0 := by
    exact (Finset.mem_filter.mp hi_mem).2
  refine ⟨i, ?_, ?_⟩
  · intro j
    rw [hi_score]
    exact hmin j (by simp)
  · intro j hj
    have hj_mem : j ∈ ties := by
      simp [ties, hj, hi_score]
    exact Finset.min'_le ties j hj_mem

/-- Deterministic choice of the minimum score, breaking ties by least index. -/
def selectedIndex (score : Fin n -> Real) : Fin n :=
  Classical.choose (exists_selected_index_spec score)

theorem selected_index_is_optimal (score : Fin n -> Real) :
    forall j : Fin n, score (selectedIndex score) <= score j :=
  (Classical.choose_spec (exists_selected_index_spec score)).1

theorem selected_index_is_least_among_ties (score : Fin n -> Real) :
    forall j : Fin n, score j = score (selectedIndex score) -> selectedIndex score <= j :=
  (Classical.choose_spec (exists_selected_index_spec score)).2

/-- GD-Attention returns exactly one candidate value, selected by score and tie-break. -/
def gdAttentionOutput {Value : Type*} (score : Fin n -> Real) (values : Fin n -> Value) : Value :=
  values (selectedIndex score)

theorem selected_output_is_exact_candidate
    {Value : Type*} (score : Fin n -> Real) (values : Fin n -> Value) :
    gdAttentionOutput score values = values (selectedIndex score) := rfl

/-!
## 4. Proof Objects
-/

/-- Machine-checkable certificate for deterministic finite-candidate selection. -/
structure SelectionCertificate (n : Nat) [NeZero n] (score : Fin n -> Real) where
  selected : Fin n
  optimal : forall j : Fin n, score selected <= score j
  leastAmongTies :
    forall j : Fin n, score j = score selected -> selected <= j

def canonicalSelectionCertificate (score : Fin n -> Real) :
    SelectionCertificate n score where
  selected := selectedIndex score
  optimal := selected_index_is_optimal score
  leastAmongTies := selected_index_is_least_among_ties score

/-- Verified output package: an output together with its selection certificate. -/
structure VerifiedSelection (n : Nat) [NeZero n]
    (Value : Type*) (score : Fin n -> Real) (values : Fin n -> Value) where
  output : Value
  certificate : SelectionCertificate n score
  output_eq_selected :
    output = values certificate.selected

def verifiedSelection
    {Value : Type*} (score : Fin n -> Real) (values : Fin n -> Value) :
    VerifiedSelection n Value score values where
  output := gdAttentionOutput score values
  certificate := canonicalSelectionCertificate score
  output_eq_selected := rfl

theorem selected_is_optimal (score : Fin n -> Real) :
    forall j : Fin n,
      score (canonicalSelectionCertificate (n := n) score).selected <= score j :=
  (canonicalSelectionCertificate (n := n) score).optimal

theorem selected_is_least_among_ties (score : Fin n -> Real) :
    forall j : Fin n,
      score j = score (canonicalSelectionCertificate (n := n) score).selected ->
        (canonicalSelectionCertificate (n := n) score).selected <= j :=
  (canonicalSelectionCertificate (n := n) score).leastAmongTies

theorem selected_output_is_candidate
    {Value : Type*} (score : Fin n -> Real) (values : Fin n -> Value) :
    (verifiedSelection (n := n) score values).output =
      values (verifiedSelection (n := n) score values).certificate.selected :=
  (verifiedSelection (n := n) score values).output_eq_selected

end GDAttention
