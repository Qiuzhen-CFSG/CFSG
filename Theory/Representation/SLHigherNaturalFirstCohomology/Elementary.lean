module

public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomology
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Elementary coordinates for special-linear first cohomology

Elementary transvections generate the special linear group: a six-transvection
factorization removes the diagonal case of Mathlib's Gaussian-elimination
induction. Thus cocycles and principality can be checked on these generators.
Commuting and three-index relations give coordinate constraints; row-supported
cocycle values are always principal in dimension at least three.

Over F₂ the center is trivial, so the canonical projection identifies SL with
PSL and transports the actual column-vector action. These facts support the
natural-module calculations in Aschbacher--Smith, *The Classification of
Quasithin Groups*, Lemma I.1.6(4), (6), printed p.408. The six-factor identity
also occurs in `Theory.AlgebraicGroup.Connected.SLStandard`.
-/

open Matrix Matrix.SpecialLinearGroup

namespace Representation.OneCohomology.SLHigherNatural

variable {K : Type*} [Field K] {d : ℕ}

private lemma diag2n_eq_transvections {i j : Fin d} (hij : i ≠ j) (c : K) (hc : c ≠ 0) :
    diag2n hij c hc =
      transvection hij c * transvection hij.symm (-c⁻¹) * transvection hij c *
      transvection hij (-1) * transvection hij.symm 1 * transvection hij (-1) := by
  apply Subtype.ext
  ext r s
  simp [diag2n_coe, transvection_coe, Matrix.diagonal_apply, mul_add, add_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ hij,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsi : s = i <;> by_cases hsj : s = j <;>
    by_cases hrs : r = s <;>
    simp_all [Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- Elementary transvections generate the special linear group over a field. -/
public lemma transvection_induction [Nontrivial (Fin d)]
    (P : SpecialLinearGroup (Fin d) K → Prop)
    (htrans : ∀ i j (hij : i ≠ j) c, P (transvection hij c))
    (hmul : ∀ a b, P a → P b → P (a * b)) (g : SpecialLinearGroup (Fin d) K) : P g := by
  apply diagonal_transvection_induction' P g ?_ htrans hmul
  intro i j hij c hc
  rw [diag2n_eq_transvections hij c hc]
  exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _
    (htrans _ _ _ _) (htrans _ _ _ _)) (htrans _ _ _ _)) (htrans _ _ _ _))
    (htrans _ _ _ _)) (htrans _ _ _ _)

/-- A transvection adds one multiple of a coordinate to another coordinate. -/
public lemma action_transvection {i j : Fin d} (hij : i ≠ j) (c : K) (v : Fin d → K) :
    specialLinearNatural d (transvection hij c) v = v + Pi.single i (c * v j) := by
  ext r
  simp [specialLinearNatural_apply, transvection_coe, Matrix.add_mulVec,
    Matrix.single_mulVec_eq, Pi.single_apply]

/-- A natural-module cocycle is determined by its values on elementary transvections. -/
public lemma cocycle_ext [Nontrivial (Fin d)]
    (f t : cocycles (specialLinearNatural (k := K) d))
    (h : ∀ i j (hij : i ≠ j) c, f.val (transvection hij c) = t.val (transvection hij c)) :
    f = t := by
  apply Subtype.ext
  funext g
  apply transvection_induction (fun g => f.val g = t.val g) h ?_ g
  intro a b ha hb
  rw [f.property, t.property, ha, hb]

/-- The values of a principal cocycle on the elementary generators. -/
public lemma principal_transvection (v : Fin d → K) {i j : Fin d} (hij : i ≠ j) (c : K) :
    (principal (specialLinearNatural d) v).val (transvection hij c) =
      Pi.single i (c * v j) := by
  change specialLinearNatural d _ v - v = _
  rw [action_transvection]
  abel

/-- Principality can be checked just on elementary transvections. -/
public lemma eq_principal_iff [Nontrivial (Fin d)]
    (f : cocycles (specialLinearNatural (k := K) d)) (v : Fin d → K) :
    f = principal (specialLinearNatural d) v ↔
      ∀ i j (hij : i ≠ j) c, f.val (transvection hij c) = Pi.single i (c * v j) := by
  constructor
  · rintro rfl i j hij c
    exact principal_transvection v hij c
  · intro h
    apply cocycle_ext
    intro i j hij c
    rw [h, principal_transvection]

/-- Elementary transvections commute when both cross terms vanish. -/
public lemma transvection_commute {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : K) :
    transvection hij a * transvection hkl b = transvection hkl b * transvection hij a := by
  apply Subtype.ext
  simp [transvection_coe, mul_add, add_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk,
    Matrix.single_mul_single_of_ne _ _ _ _ hli, add_comm, add_left_comm]

/-- A commuting transvection kills a specified off-row cocycle coordinate. -/
public lemma cocycle_off_diagonal (f : cocycles (specialLinearNatural (k := K) d))
    {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (hki : k ≠ i) (a : K) :
    f.val (transvection hij a) l = 0 := by
  have h := congrArg (fun g => f.val g k) (transvection_commute hij hkl hjk hli a 1)
  rw [f.property, f.property] at h
  simp only [action_transvection, Pi.add_apply] at h
  simp only [Pi.single_eq_of_ne hki, Pi.single_eq_same, one_mul, add_zero] at h
  linear_combination -h

/-- The elementary three-index relation, without inverses. -/
public lemma transvection_chain {i j k : Fin d} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : K) :
    transvection hij a * transvection hjk b =
      transvection hjk b * transvection hik (a * b) * transvection hij a := by
  apply Subtype.ext
  simp [transvection_coe, mul_add, add_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ hik.symm,
    add_assoc, add_comm, add_left_comm]

/-- For row-supported values, the three-index relation identifies their coefficients. -/
public lemma cocycle_transvection_chain
    (f : cocycles (specialLinearNatural (k := K) d))
    (hs : ∀ (i j : Fin d) (hij : i ≠ j) a,
      f.val (transvection hij a) = Pi.single i (f.val (transvection hij a) i))
    {i j k : Fin d} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : K) :
    f.val (transvection hik (a * b)) i = a * f.val (transvection hjk b) j := by
  have hf : ∀ g t, f.val (g * t) = specialLinearNatural d g (f.val t) + f.val g :=
    f.property
  have h := congrArg (fun g => f.val g i) (transvection_chain hij hjk hik a b)
  simp only [hf, map_mul, Module.End.mul_apply, action_transvection, Pi.add_apply] at h
  have hz (x y : Fin d) (hxy : x ≠ y) (c : K) (r : Fin d) (hr : r ≠ x) :
      f.val (transvection hxy c) r = 0 := by
    rw [hs x y hxy c]
    exact Pi.single_eq_of_ne hr _
  simp [hij, hik.symm,
    hz j k hjk b i hij, hz i k hik (a * b) k hik.symm,
    hz i j hij a k hik.symm] at h
  linear_combination -h

/-- A cocycle whose elementary values are supported in their rows is principal. -/
public lemma exists_principal_of_support (hd : 3 ≤ d)
    (f : cocycles (specialLinearNatural (k := K) d))
    (hs : ∀ (i j : Fin d) (hij : i ≠ j) a,
      f.val (transvection hij a) = Pi.single i (f.val (transvection hij a) i)) :
    ∃ v : Fin d → K, f = principal (specialLinearNatural (k := K) d) v := by
  classical
  let : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hne (j : Fin d) : ∃ i : Fin d, i ≠ j := exists_ne j
  let r (j : Fin d) := (hne j).choose
  have hr (j : Fin d) : r j ≠ j := (hne j).choose_spec
  refine ⟨fun j => f.val (transvection (hr j) 1) (r j), ?_⟩
  apply (eq_principal_iff f _).mpr
  intro i j hij a
  rw [hs i j hij a]
  apply congrArg (Pi.single i)
  by_cases hir : i = r j
  · obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    have h₁ := cocycle_transvection_chain f hs hki.symm hkj hij a 1
    have h₂ := cocycle_transvection_chain f hs hki hij hkj 1 1
    simp only [mul_one, one_mul] at h₁ h₂
    simpa [h₂, hir] using h₁
  · simpa only [mul_one] using cocycle_transvection_chain f hs hir (hr j) hij a 1

/-- The natural module has no fixed vectors in dimension at least two. -/
public lemma fixed_eq_bot (hd : 2 ≤ d) :
    fixed (specialLinearNatural (k := K) d) = ⊥ := by
  let : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  apply bot_unique
  intro v hv
  change v = 0
  funext j
  obtain ⟨i, hij⟩ := exists_ne j
  have h := congrFun (hv (transvection hij (1 : K))) i
  simpa [action_transvection] using h

/-- The special linear group over the two-element field has trivial center. -/
public lemma binary_center_eq_bot (d : ℕ) :
    Subgroup.center (SpecialLinearGroup (Fin d) (ZMod 2)) = ⊥ := by
  cases d with
  | zero => exact center_eq_bot_of_subsingleton
  | succ d =>
    apply eq_bot_iff.mpr
    intro g hg
    change g = 1
    obtain ⟨c, hc, he⟩ := mem_center_iff.mp hg
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases c with rfl | rfl
    · simp at hc
    · apply Subtype.ext
      simpa using he.symm

/-- The canonical quotient identifies special and projective special linear groups over F₂. -/
@[expose] public noncomputable def binaryProjectiveEquiv (d : ℕ) :
    SpecialLinearGroup (Fin d) (ZMod 2) ≃* ProjectiveSpecialLinearGroup (Fin d) (ZMod 2) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', binary_center_eq_bot],
    QuotientGroup.mk'_surjective _⟩

/-- The identification with the projective group is the actual quotient map. -/
public lemma binaryProjectiveEquiv_apply (d : ℕ) (g : SpecialLinearGroup (Fin d) (ZMod 2)) :
    binaryProjectiveEquiv d g = QuotientGroup.mk' _ g := rfl

/-- The natural projective special-linear action over F₂, using the canonical quotient isomorphism. -/
@[expose] public noncomputable def binaryProjectiveNatural (d : ℕ) :
    Representation (ZMod 2) (ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)) (Fin d → ZMod 2) :=
  (specialLinearNatural d).comp (binaryProjectiveEquiv d).symm.toMonoidHom

/-- Under the quotient identification, the projective natural action is matrix multiplication. -/
public lemma binaryProjectiveNatural_apply (d : ℕ)
    (g : SpecialLinearGroup (Fin d) (ZMod 2)) (v : Fin d → ZMod 2) :
    binaryProjectiveNatural d (binaryProjectiveEquiv d g) v = specialLinearNatural d g v := by
  change specialLinearNatural d ((binaryProjectiveEquiv d).symm (binaryProjectiveEquiv d g)) v = _
  rw [MulEquiv.symm_apply_apply]

end Representation.OneCohomology.SLHigherNatural
