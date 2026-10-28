module

public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial
public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore.Diagonal
public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore.CoordinateAction
public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore.GroupAction
public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial.LocalCore.SignSubgroup
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.SpecificGroups.ProjectiveLinearInvolutions

/-!
# Three-cores inside the unitary monomial subgroups

The coordinate-line permutation action and the diagonal sign two-subgroup
reduce both actual models to the finite-group calculation. In the projective
model the restricted special-to-projective map has a central three-group
kernel. Descending the action and sign subgroup through this map preserves
the centralizer property, so the same order-nine calculation applies.

The full ambient Sylow hypothesis puts the normal sign subgroup inside H.
Its centralizer contains O₃(H), forcing the core into the diagonal kernel.
The nonabelian three-subgroup forces the permutation image to have three-part
three; the order of H then gives a diagonal three-part of nine, which is
exactly the order of its three-core.

The final special and projective theorems discharge both concrete matrix
witnesses. Their field parameters match the nonsplit prime-field branch;
the calculation itself needs only an identity Gram matrix and odd field
order. The three-core is intrinsic to H.

Source: GLS3, Theorem 6.5.3(b), `refs/KGroup/GLS3/chapter6.tex`, and
Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528).
-/

public section

open Subgroup

namespace BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- The special model's local core calculation from a three-point action
and a normal sign two-subgroup. -/
theorem special_core_card_nine_of_action
    (f : special J →* Equiv.Perm (Fin 3)) [IsMulCommutative f.ker]
    (V : Subgroup (special J)) [V.Normal] (hV : IsPGroup 2 V)
    (hcentral : centralizer (V : Set (special J)) ≤ f.ker)
    (T : Sylow 2 J.specialSubgroup) (H : Subgroup J.specialSubgroup)
    (hTH : (T : Subgroup J.specialSubgroup) ≤ H) (hHM : H ≤ special J)
    (hcard : Nat.card H = 27 * Nat.card T)
    (hU : ∃ U : Subgroup J.specialSubgroup,
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card (pCore 3 H) = 9 :=
  CoreCalculation.core_card_nine_of_normal_two_subgroup
    (special J) H T hTH hHM f V hV hcentral hcard hU

/-- Descent through the actual scalar kernel supplies the projective
calculation from the same special monomial action. -/
theorem projective_core_card_nine_of_special_action
    (f : special J →* Equiv.Perm (Fin 3)) [IsMulCommutative f.ker]
    (V : Subgroup (special J)) [V.Normal] (hV : IsPGroup 2 V)
    (hcentral : centralizer (V : Set (special J)) ≤ f.ker)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hTH : (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ H)
    (hHM : H ≤ projective J) (hcard : Nat.card H = 27 * Nat.card T)
    (hU : ∃ U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card (pCore 3 H) = 9 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let q : special J →* projective J := J.specialToProjective.subgroupMap (special J)
  have hq : Function.Surjective q := J.specialToProjective.subgroupMap_surjective (special J)
  have hker : q.ker = J.specialToProjective.ker.comap (special J).subtype := by
    ext x
    change q x = 1 ↔ J.specialToProjective x.val = 1
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hqcentral : q.ker ≤ center (special J) := by
    intro x hx
    rw [hker] at hx
    have hc := J.specialToProjective_ker_le_center hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hc y.val)
  have hthree : IsPGroup 3 J.specialToProjective.ker :=
    fun x => ⟨1, by simpa using J.specialToProjective_ker_cube x⟩
  have hqthree : IsPGroup 3 q.ker := by
    rw [hker]
    exact hthree.comap_of_injective (special J).subtype (special J).subtype_injective
  obtain ⟨a, ha, W, hWnormal, hW, hWcentral⟩ :=
    CoreCalculation.descend_action f V hV hcentral q hq hqcentral hqthree
  exact CoreCalculation.core_card_nine_of_normal_two_subgroup
    (projective J) H T hTH hHM a W hW hWcentral hcard hU

section MatrixFacts

variable
    (haction : ∃ f : special J →* Equiv.Perm (Fin 3),
      ∀ x : special J, f x = 1 ↔ IsDiagonal x)
    (hsigns : ∃ V : Subgroup (special J), V.Normal ∧ IsPGroup 2 V ∧
      ∀ x ∈ centralizer (V : Set (special J)), IsDiagonal x)

include haction hsigns

/-- The special contract reduces to two independent concrete matrix facts. -/
theorem special_core_card_nine_of_matrix_facts
    (T : Sylow 2 J.specialSubgroup) (H : Subgroup J.specialSubgroup)
    (hTH : (T : Subgroup J.specialSubgroup) ≤ H) (hHM : H ≤ special J)
    (hcard : Nat.card H = 27 * Nat.card T)
    (hU : ∃ U : Subgroup J.specialSubgroup,
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card (pCore 3 H) = 9 := by
  obtain ⟨f, hf⟩ := haction
  have hab := isMulCommutative_kernel_of_isDiagonal f (fun x => (hf x).mp)
  obtain ⟨V, hn, hV, hc⟩ := hsigns
  exact special_core_card_nine_of_action J f V hV (fun x hx => (hf x).mpr (hc x hx))
    T H hTH hHM hcard hU

/-- The same two special matrix facts also give the projective contract,
with the scalar kernel retained in the proof. -/
theorem projective_core_card_nine_of_matrix_facts
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hTH : (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ H)
    (hHM : H ≤ projective J) (hcard : Nat.card H = 27 * Nat.card T)
    (hU : ∃ U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card (pCore 3 H) = 9 := by
  obtain ⟨f, hf⟩ := haction
  have hab := isMulCommutative_kernel_of_isDiagonal f (fun x => (hf x).mp)
  obtain ⟨V, hn, hV, hc⟩ := hsigns
  exact projective_core_card_nine_of_special_action J f V hV
    (fun x hx => (hf x).mpr (hc x hx)) T H hTH hHM hcard hU

end MatrixFacts

/-- A subgroup of the actual special-unitary monomial group containing a
full ambient Sylow two-subgroup and a nonabelian three-subgroup has three-core
of order nine when its order is twenty-seven times the Sylow two-order. -/
theorem special_core_card_nine
    {p : ℕ} (_hp : p.Prime) (ho : Odd p) (_hlarge : 3 < p)
    (_hmod : p % 3 = 2) (hE : Nat.card E = p ^ 2)
    (_hconj : ∀ x, J.conj x = x ^ p) (hJ : J.form = 1)
    (T : Sylow 2 J.specialSubgroup) (H : Subgroup J.specialSubgroup)
    (hTH : (T : Subgroup J.specialSubgroup) ≤ H) (hHM : H ≤ special J)
    (hcard : Nat.card H = 27 * Nat.card T)
    (hU : ∃ U : Subgroup J.specialSubgroup,
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card (pCore 3 H) = 9 := by
  have h2 : (2 : E) ≠ 0 := Field.two_ne_zero_of_odd_card E (by
    rw [hE]
    exact ho.pow)
  exact special_core_card_nine_of_matrix_facts J (exists_coordinate_action J)
    (exists_normal_sign_subgroup J hJ h2) T H hTH hHM hcard hU

/-- The same local three-core calculation in the actual projective image,
with the central scalar three-group retained in the descent. -/
theorem projective_core_card_nine
    {p : ℕ} (_hp : p.Prime) (ho : Odd p) (_hlarge : 3 < p)
    (_hmod : p % 3 = 2) (hE : Nat.card E = p ^ 2)
    (_hconj : ∀ x, J.conj x = x ^ p) (hJ : J.form = 1)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hTH : (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ H)
    (hHM : H ≤ projective J) (hcard : Nat.card H = 27 * Nat.card T)
    (hU : ∃ U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    Nat.card (pCore 3 H) = 9 := by
  have h2 : (2 : E) ≠ 0 := Field.two_ne_zero_of_odd_card E (by
    rw [hE]
    exact ho.pow)
  exact projective_core_card_nine_of_matrix_facts J (exists_coordinate_action J)
    (exists_normal_sign_subgroup J hJ h2) T H hTH hHM hcard hU

end BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal.Monomial
