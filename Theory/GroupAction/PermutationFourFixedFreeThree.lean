module
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Fixed-free cubics on binary four-space and a nonsolvability obstruction

Let X be an actual automorphism subgroup of W, with a specified equivalence
from W to the four-coordinate elementary abelian two-group. If X contains
every coordinate permutation transported along that equivalence, and contains
an automorphism t of cube one fixing only the identity, then X is nonsolvable.
The statement uses the library's literal `mulAutArrow` permutation action;
the complete permutation-module identification is an essential hypothesis.

The product of v, t(v), and t²(v) is fixed by t, so fixed-point freeness gives
t²(v)=v*t(v). The first coordinate vector and its image span an invariant
plane. Choose the first coordinate vector outside that plane. Its image is
outside the resulting three-dimensional span, since otherwise applying t and
the same quadratic identity would put the chosen vector back in the plane.
These four vectors are therefore a basis and determine t.

Vectors are encoded by four binary digits. Kernel-checked tables identify
all admissible pairs of image vectors with seven representatives up to
coordinate permutation. Seven explicit invertible changes of basis put every
fixed-free cubic into the common form `(x₁, x₀*x₁, x₂*x₃, x₂)`. The public
conjugacy theorem provides this frame without any permutation-subgroup premise;
its consumer combines an actual A4 action with a mover of its invariant plane.
For the permutation-module obstruction, short explicit words express
a fixed nonidentity coordinate 3-cycle as the commutator of two of its
conjugates. Normality of the derived series puts this element in every derived
subgroup, proving nonsolvability. The final transport uses the supplied group
equivalence and retains the original subgroup X throughout the conclusion.

This is the finite-action obstruction used for the two actions on W in
Stellmacher (8.6)(b3), Journal of Algebra 190 (1997), printed p.44. The local
construction of W and its permutation-module equivalence are separate inputs.
The common frame also supports the corrected A4-plane proof of that same
normalizer obstruction. Every finite identity used here is checked by Lean's kernel.
-/

namespace PermutationFourFixedFreeThree
open scoped commutatorElement Matrix
private abbrev V := Fin 4 → Multiplicative (ZMod 2)
private abbrev Aut := MulAut V

private def vector (n : Fin 16) : V := fun i =>
  Multiplicative.ofAdd (if n.val.testBit i.val then 1 else 0)
private def e0 : V := vector 1
private def permutations : Fin 24 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0], ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0], ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]
private def inversePermutations : Fin 24 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 3, 1, 2], ![0, 2, 3, 1], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2], ![2, 0, 1, 3], ![3, 0, 1, 2], ![2, 0, 3, 1], ![3, 0, 2, 1], ![1, 2, 0, 3], ![1, 3, 0, 2], ![2, 1, 0, 3], ![3, 1, 0, 2], ![2, 3, 0, 1], ![3, 2, 0, 1], ![1, 2, 3, 0], ![1, 3, 2, 0], ![2, 1, 3, 0], ![3, 1, 2, 0], ![2, 3, 1, 0], ![3, 2, 1, 0]]
private theorem permutation_inverse : ∀ k : Fin 24, ∀ i : Fin 4,
    inversePermutations k (permutations k i) = i ∧
      permutations k (inversePermutations k i) = i := by decide +kernel
private def permutation (k : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := permutations k
  invFun := inversePermutations k
  left_inv i := (permutation_inverse k i).1
  right_inv i := (permutation_inverse k i).2
private def coordinate (p : Equiv.Perm (Fin 4)) : Aut :=
  mulAutArrow (G := Equiv.Perm (Fin 4)) (A := Fin 4) (M := Multiplicative (ZMod 2)) p
private def columns : Fin 7 → Fin 4 → Fin 16 := ![![2, 3, 8, 12], ![2, 3, 9, 15], ![2, 3, 10, 13], ![2, 3, 11, 14], ![6, 9, 14, 13], ![6, 12, 11, 5], ![7, 14, 15, 13]]
private def matrix (k : Fin 7) : Matrix (Fin 4) (Fin 4) (ZMod 2) := fun i j =>
  if (columns k j).val.testBit i.val then 1 else 0
private def matrixMap (m : Matrix (Fin 4) (Fin 4) (ZMod 2)) : V →* V where
  toFun v i := Multiplicative.ofAdd ((m *ᵥ (fun j => (v j).toAdd)) i)
  map_one' := by
    funext i
    change Multiplicative.ofAdd ((m *ᵥ 0) i) = 1
    simp
  map_mul' v w := by
    funext i
    change Multiplicative.ofAdd ((m *ᵥ ((fun j => (v j).toAdd) +
      (fun j => (w j).toAdd))) i) = _
    rw [Matrix.mulVec_add]
    rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem cube_spec : ∀ k : Fin 7, ∀ v : V,
    matrixMap (matrix k) (matrixMap (matrix k) (matrixMap (matrix k) v)) = v := by
  decide +kernel
private def representative (k : Fin 7) : Aut where
  toFun := matrixMap (matrix k)
  invFun v := matrixMap (matrix k) (matrixMap (matrix k) v)
  left_inv v := cube_spec k v
  right_inv v := cube_spec k v
  map_mul' := (matrixMap (matrix k)).map_mul
private def x : Aut := coordinate (permutation 8)
private def letter (k : Fin 7) (i : Fin 26) : Aut :=
  if h : i.val < 24 then coordinate (permutation ⟨i.val,h⟩)
  else if i.val = 24 then representative k else representative k ^ 2
private def wordValue (k : Fin 7) (word : List (Fin 26)) : Aut :=
  (word.map (letter k)).prod
private def leftWord : Fin 7 → List (Fin 26) := ![[25, 3, 24], [3, 24], [1], [7, 24], [25, 3, 24], [1], [1]]
private def rightWord : Fin 7 → List (Fin 26) := ![[24, 19, 24, 1], [9, 24], [1, 24], [25, 1], [14, 25, 3, 24], [7, 24], [15, 24]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
private theorem perfect_certificate : ∀ k : Fin 7, ∀ v : V,
    ⁅wordValue k (leftWord k) * x * (wordValue k (leftWord k))⁻¹,
      wordValue k (rightWord k) * x * (wordValue k (rightWord k))⁻¹⁆ v = x v := by
  decide +kernel

private def second (a : Fin 16) : Fin 16 := if a = 2 ∨ a = 3 then 4 else 2
private def choices : Fin 16 → Fin 16 → Fin 24 × Fin 7 := ![
  ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (16, 0), (0, 1), (0, 2), (0, 3), (22, 0), (1, 2), (1, 3), (1, 1)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (17, 0), (6, 2), (6, 1), (6, 3), (23, 0), (7, 3), (7, 2), (7, 1)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (10, 0), (2, 1), (20, 0), (3, 2), (2, 2), (2, 3), (3, 3), (3, 1)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (12, 0), (12, 2), (21, 0), (13, 3), (12, 1), (12, 3), (13, 2), (13, 1)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (10, 1), (7, 4), (20, 2), (22, 2), (19, 5), (18, 5), (13, 4), (16, 1)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (11, 2), (17, 2), (21, 3), (22, 4), (20, 4), (23, 3), (19, 6), (18, 6)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (8, 0), (4, 1), (14, 0), (5, 2), (0, 0), (0, 0), (0, 0), (0, 0), (4, 2), (4, 3), (5, 3), (5, 1)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (18, 0), (18, 2), (19, 0), (19, 3), (0, 0), (0, 0), (0, 0), (0, 0), (18, 1), (18, 3), (19, 2), (19, 1)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (8, 1), (6, 4), (14, 2), (16, 2), (0, 0), (0, 0), (0, 0), (0, 0), (13, 5), (23, 5), (19, 4), (22, 1)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (9, 2), (23, 2), (15, 3), (23, 4), (0, 0), (0, 0), (0, 0), (0, 0), (14, 4), (17, 3), (13, 6), (23, 6)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (8, 2), (21, 5), (14, 1), (18, 4), (10, 2), (15, 5), (20, 1), (12, 4), (0, 0), (0, 0), (0, 0), (0, 0)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (9, 3), (15, 4), (15, 2), (21, 6), (11, 3), (21, 4), (21, 2), (15, 6), (0, 0), (0, 0), (0, 0), (0, 0)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (8, 3), (20, 5), (14, 3), (22, 3), (10, 3), (22, 5), (20, 3), (16, 3), (0, 0), (0, 0), (0, 0), (0, 0)],
  ![(0, 0), (0, 0), (0, 0), (0, 0), (9, 1), (17, 1), (15, 1), (20, 6), (11, 1), (23, 1), (21, 1), (22, 6), (0, 0), (0, 0), (0, 0), (0, 0)]]
private def candidate (a c : Fin 16) : Aut :=
  coordinate (permutation (choices a c).1) * representative (choices a c).2 *
    (coordinate (permutation (choices a c).1))⁻¹
private def admissible (a c : Fin 16) : Prop :=
  a ≠ 0 ∧ a ≠ 1 ∧ ∀ i j k : Fin 2,
    vector c ≠ e0 ^ i.val * vector a ^ j.val * vector (second a) ^ k.val
private instance (a c : Fin 16) : Decidable (admissible a c) := inferInstanceAs
  (Decidable (a ≠ 0 ∧ a ≠ 1 ∧ ∀ i j k : Fin 2,
    vector c ≠ e0 ^ i.val * vector a ^ j.val * vector (second a) ^ k.val))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
private theorem candidate_values : ∀ a c : Fin 16, admissible a c →
    candidate a c e0 = vector a ∧
    candidate a c (vector a) = e0 * vector a ∧
    candidate a c (vector (second a)) = vector c ∧
    candidate a c (vector c) = vector (second a) * vector c := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
private theorem basis_spans : ∀ a c : Fin 16, admissible a c → ∀ v : V,
    ∃ i j k l : Fin 2,
      v = e0 ^ i.val * vector a ^ j.val * vector (second a) ^ k.val * vector c ^ l.val := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 100000 in
private theorem second_outside : ∀ a : Fin 16, a ≠ 0 → a ≠ 1 → ∀ i j : Fin 2,
    vector (second a) ≠ e0 ^ i.val * vector a ^ j.val := by
  decide +kernel

private theorem vector_surjective : Function.Surjective vector := by decide +kernel

private theorem square_one (v : V) : v * v = 1 := by
  funext i
  exact congrArg Multiplicative.ofAdd (ZModModule.add_self (v i).toAdd)

private theorem inverse_self (v : V) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_left (square_one v)

private theorem cubic_apply (t : Aut) (hthree : t ^ 3 = 1) (v : V) :
    t (t (t v)) = v := by
  have hh := congrArg (fun a : Aut => a v) hthree
  simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using hh

private theorem cubic_quadratic (t : Aut) (hthree : t ^ 3 = 1)
    (hfixed : ∀ v : V, t v = v → v = 1) (v : V) : t (t v) = v * t v := by
  have hnorm : v * t v * t (t v) = 1 := hfixed _ (by
    rw [map_mul,map_mul,cubic_apply t hthree]
    ac_rfl)
  calc
    t (t v) = (v * t v)⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
      simpa only [mul_comm,mul_left_comm,mul_assoc] using hnorm)
    _ = v * t v := inverse_self _

private def inPlane (a : Fin 16) (v : V) : Prop :=
  ∃ i j : Fin 2, v = e0 ^ i.val * vector a ^ j.val

private theorem plane_stable (t : Aut) (a : Fin 16)
    (ha : t e0 = vector a) (hqa : t (vector a) = e0 * vector a)
    {v : V} (hv : inPlane a v) : inPlane a (t v) := by
  obtain ⟨i,j,rfl⟩ := hv
  fin_cases i <;> fin_cases j
  · exact ⟨0,0,by simp⟩
  · exact ⟨1,1,by simp [hqa]⟩
  · exact ⟨0,1,by simp [ha]⟩
  · refine ⟨1,0,?_⟩
    simp only [Fin.val_one,Fin.val_zero,pow_one,pow_zero,mul_one,map_mul,ha,hqa]
    calc
      vector a * (e0 * vector a) = e0 * (vector a * vector a) := by ac_rfl
      _ = e0 := by rw [square_one,mul_one]

private theorem vector_zero : vector 0 = 1 := by decide +kernel
private theorem e0_ne_one : e0 ≠ 1 := by decide +kernel

private theorem cubic_classification (t : Aut) (hthree : t ^ 3 = 1)
    (hfixed : ∀ v : V, t v = v → v = 1) :
    ∃ a c : Fin 16, admissible a c ∧ t = candidate a c := by
  obtain ⟨a,ha⟩ := vector_surjective (t e0)
  have hta : t e0 = vector a := ha.symm
  have ha0 : a ≠ 0 := by
    intro heq
    have hz : t e0 = 1 := by rw [hta,heq,vector_zero]
    exact e0_ne_one (t.map_eq_one_iff.mp hz)
  have ha1 : a ≠ 1 := by
    intro heq
    apply e0_ne_one
    apply hfixed
    simpa only [heq,e0] using hta
  have hqa : t (vector a) = e0 * vector a := by
    rw [←hta]
    exact cubic_quadratic t hthree hfixed e0
  let b := vector (second a)
  have hb : ¬ inPlane a b := by
    rintro ⟨i,j,hij⟩
    exact second_outside a ha0 ha1 i j hij
  obtain ⟨c,hc⟩ := vector_surjective (t b)
  have htb : t b = vector c := hc.symm
  have hqc : t (vector c) = b * vector c := by
    rw [←htb]
    exact cubic_quadratic t hthree hfixed b
  have hgood : admissible a c := by
    refine ⟨ha0,ha1,?_⟩
    intro i j k h
    fin_cases k
    · simp only [pow_zero,mul_one] at h
      have hcP : inPlane a (vector c) := ⟨i,j,h⟩
      have hP := plane_stable t a hta hqa (plane_stable t a hta hqa hcP)
      have heq : t (t (vector c)) = b := by
        rw [←htb]
        exact cubic_apply t hthree b
      rw [heq] at hP
      exact hb hP
    · simp only [pow_one] at h
      have hh := congrArg t h
      rw [hqc,map_mul,htb] at hh
      have heq : b = t (e0 ^ i.val * vector a ^ j.val) := mul_right_cancel hh
      apply hb
      rw [heq]
      exact plane_stable t a hta hqa ⟨i,j,rfl⟩
  refine ⟨a,c,hgood,?_⟩
  obtain ⟨h0,h1,h2,h3⟩ := candidate_values a c hgood
  change t (vector (second a)) = vector c at htb
  change t (vector c) = vector (second a) * vector c at hqc
  apply MulEquiv.ext
  intro v
  obtain ⟨i,j,k,l,rfl⟩ := basis_spans a c hgood v
  simp only [map_mul,map_pow,hta,hqa,htb,hqc,h0,h1,h2,h3]

private theorem x_ne_one : x ≠ 1 := by
  have hmoves : x e0 ≠ e0 := by decide +kernel
  intro h
  apply hmoves
  rw [h]
  rfl

private theorem representative_obstruction (X : Subgroup Aut)
    (hperms : ∀ p : Equiv.Perm (Fin 4), coordinate p ∈ X)
    (k : Fin 7) (hr : representative k ∈ X) : ¬ Group.IsSolvable X := by
  have hletter (i : Fin 26) : letter k i ∈ X := by
    unfold letter
    split_ifs with h h24
    · exact hperms _
    · exact hr
    · exact X.pow_mem hr 2
  have hword (w : List (Fin 26)) : wordValue k w ∈ X := by
    induction w with
    | nil => exact X.one_mem
    | cons i w ih => exact X.mul_mem (hletter i) ih
  let xX : X := ⟨x,hperms _⟩
  let aX : X := ⟨wordValue k (leftWord k),hword _⟩
  let bX : X := ⟨wordValue k (rightWord k),hword _⟩
  have hrelation : ⁅aX*xX*aX⁻¹,bX*xX*bX⁻¹⁆ = xX := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    exact perfect_certificate k v
  apply not_isSolvable_of_mem_derivedSeries
    (fun h : xX = 1 => x_ne_one (congrArg Subtype.val h))
  intro n
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
    rw [←hrelation]
    exact Subgroup.commutator_mem_commutator
      ((derivedSeries_normal X n).conj_mem _ ih _)
      ((derivedSeries_normal X n).conj_mem _ ih _)

private theorem concrete_obstruction (X : Subgroup Aut)
    (hperms : ∀ p : Equiv.Perm (Fin 4), coordinate p ∈ X)
    (t : Aut) (ht : t ∈ X) (hthree : t ^ 3 = 1)
    (hfixed : ∀ v : V, t v = v → v = 1) : ¬ Group.IsSolvable X := by
  obtain ⟨a,c,hgood,heq⟩ := cubic_classification t hthree hfixed
  let p := coordinate (permutation (choices a c).1)
  have hp : p ∈ X := hperms _
  have hr : representative (choices a c).2 ∈ X := by
    have hh := X.mul_mem (X.mul_mem (X.inv_mem hp) ht) hp
    rw [heq] at hh
    change p⁻¹ * (p * representative (choices a c).2 * p⁻¹) * p ∈ X at hh
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
  exact representative_obstruction X hperms (choices a c).2 hr

private def frameColumns : Fin 7 → Fin 4 → Fin 16 := ![![1, 2, 4, 12], ![1, 2, 4, 13], ![1, 2, 4, 14], ![1, 2, 4, 15], ![1, 4, 6, 13], ![1, 4, 6, 10], ![1, 4, 7, 15]]
private def inverseFrameColumns : Fin 7 → Fin 4 → Fin 16 := ![![1, 2, 4, 12], ![1, 2, 4, 13], ![1, 2, 4, 14], ![1, 2, 4, 15], ![1, 6, 2, 11], ![1, 6, 2, 14], ![1, 7, 2, 12]]
private def frameMatrix (k : Fin 7) : Matrix (Fin 4) (Fin 4) (ZMod 2) := fun i j =>
  if (frameColumns k j).val.testBit i.val then 1 else 0
private def inverseFrameMatrix (k : Fin 7) : Matrix (Fin 4) (Fin 4) (ZMod 2) := fun i j =>
  if (inverseFrameColumns k j).val.testBit i.val then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem frame_certificate : ∀ k : Fin 7, ∀ v : V,
    matrixMap (inverseFrameMatrix k) (matrixMap (frameMatrix k) v) = v ∧
    matrixMap (frameMatrix k) (matrixMap (inverseFrameMatrix k) v) = v ∧
    matrixMap (frameMatrix k) (representative k v) =
      ![(matrixMap (frameMatrix k) v) 1,
        (matrixMap (frameMatrix k) v) 0 * (matrixMap (frameMatrix k) v) 1,
        (matrixMap (frameMatrix k) v) 2 * (matrixMap (frameMatrix k) v) 3,
        (matrixMap (frameMatrix k) v) 2] := by
  decide +kernel

private def frame (k : Fin 7) : Aut where
  toFun := matrixMap (frameMatrix k)
  invFun := matrixMap (inverseFrameMatrix k)
  left_inv v := (frame_certificate k v).1
  right_inv v := (frame_certificate k v).2.1
  map_mul' := (matrixMap (frameMatrix k)).map_mul

private theorem frame_formula (k : Fin 7) (v : V) :
    frame k (representative k v) =
      ![(frame k v) 1, (frame k v) 0 * (frame k v) 1,
        (frame k v) 2 * (frame k v) 3, (frame k v) 2] :=
  (frame_certificate k v).2.2

end PermutationFourFixedFreeThree

namespace MulAut

/-- Every fixed-free cubic on binary four-space has a common concrete frame. -/
public theorem exists_conjugacy_fixed_free_three_four
    (t : MulAut (Fin 4 → Multiplicative (ZMod 2))) (hthree : t ^ 3 = 1)
    (hfixed : ∀ v : Fin 4 → Multiplicative (ZMod 2), t v = v → v = 1) :
    ∃ a : MulAut (Fin 4 → Multiplicative (ZMod 2)), ∀ v,
      a (t v) = ![(a v) 1, (a v) 0 * (a v) 1,
        (a v) 2 * (a v) 3, (a v) 2] := by
  obtain ⟨i,j,_hgood,heq⟩ := PermutationFourFixedFreeThree.cubic_classification t hthree hfixed
  let p := PermutationFourFixedFreeThree.coordinate
    (PermutationFourFixedFreeThree.permutation (PermutationFourFixedFreeThree.choices i j).1)
  let k := (PermutationFourFixedFreeThree.choices i j).2
  let a := PermutationFourFixedFreeThree.frame k * p⁻¹
  refine ⟨a,?_⟩
  intro v
  rw [heq]
  change PermutationFourFixedFreeThree.frame k
      (p⁻¹ ((p * PermutationFourFixedFreeThree.representative k * p⁻¹) v)) = _
  simp only [MulAut.mul_apply,MulAut.inv_apply,MulEquiv.symm_apply_apply]
  exact PermutationFourFixedFreeThree.frame_formula k (p⁻¹ v)

public theorem not_isSolvable_of_permutation_four_and_fixed_free_three
    {W : Type*} [Group W] (X : Subgroup (MulAut W))
    (e : W ≃* (Fin 4 → Multiplicative (ZMod 2)))
    (hperms : ∀ p : Equiv.Perm (Fin 4),
      e.trans ((mulAutArrow (G := Equiv.Perm (Fin 4)) (A := Fin 4)
        (M := Multiplicative (ZMod 2)) p).trans e.symm) ∈ X)
    (t : MulAut W) (ht : t ∈ X) (hthree : t ^ 3 = 1)
    (hfixed : ∀ w : W, t w = w → w = 1) : ¬ Group.IsSolvable X := by
  let f := (MulAut.congr e).toMonoidHom
  let Y := X.map f
  have hYperms : ∀ p : Equiv.Perm (Fin 4),
      PermutationFourFixedFreeThree.coordinate p ∈ Y := by
    intro p
    refine ⟨e.trans ((mulAutArrow p).trans e.symm),hperms p,?_⟩
    change (MulAut.congr e) (e.trans ((mulAutArrow p).trans e.symm)) = _
    rw [MulAut.congr_apply]
    apply MulEquiv.ext
    intro v
    change e (e.symm ((mulAutArrow p) (e (e.symm v)))) = (mulAutArrow p) v
    simp only [MulEquiv.apply_symm_apply]
  have hz : f t ∈ Y := Subgroup.mem_map_of_mem f ht
  have hz3 : (f t)^3 = 1 := by rw [←map_pow,hthree,map_one]
  have hzf : ∀ v : Fin 4 → Multiplicative (ZMod 2), f t v = v → v = 1 := by
    intro v hv
    change e (t (e.symm v)) = v at hv
    have htv := congrArg e.symm hv
    simp only [MulEquiv.symm_apply_apply] at htv
    have heq := hfixed (e.symm v) htv
    have hh := congrArg e heq
    simpa only [MulEquiv.apply_symm_apply,map_one] using hh
  have hn := PermutationFourFixedFreeThree.concrete_obstruction Y hYperms (f t) hz hz3 hzf
  intro hX
  let _ := hX
  let eqv := X.equivMapOfInjective f (MulAut.congr e).injective
  exact hn (Group.isSolvable_of_surjective (f := eqv.toMonoidHom) eqv.surjective)

end MulAut
