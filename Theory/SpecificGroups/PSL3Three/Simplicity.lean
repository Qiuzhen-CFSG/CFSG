module

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.Algebra.Field.ZMod

/-!
# Simplicity and nonsolvability of PSL₃(3)

The concrete projective special linear group over `ZMod 3` is simple and
nonsolvable. This supplies the intrinsic model facts for the PSL₃(3) member
of Thompson's minimal-simple catalogue.

Elementary matrices generate SL₃(3): the special-linear induction theorem
reduces generation to transvections and two-entry diagonal matrices, and each
such diagonal is a product of four transvections. A third index expresses
every transvection as a commutator, proving perfection. The elementary matrix
identities are checked by kernel reduction over the finite coefficient field.

Each transvection belongs to the abelian radical attached to its coordinate
line. Thus these radicals generate the projective quotient. Mathlib's faithful
primitive projective action and Iwasawa criterion then prove simplicity;
nontriviality and perfection imply nonsolvability.

Source: the elementary-matrix and Iwasawa proof of projective linear simplicity,
following `Mathlib.LinearAlgebra.Projectivization.PSL.PSL2` and its
rank-independent line stabilizer and projective action APIs. This module does
not assert a proper-subgroup classification.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped commutatorElement LinearAlgebra.Projectivization

private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)
private abbrev Q := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)

private def elementary (i j : Fin 3) (c : ZMod 3) : SL :=
  if h : i ≠ j then transvection h c else 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem elementary_commutator :
    ∀ i j k : Fin 3, ∀ c : ZMod 3, i ≠ j → i ≠ k → k ≠ j →
      ⁅elementary i k c, elementary k j 1⁆ = elementary i j c := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem diag_matrix : ∀ i j : Fin 3, ∀ c : ZMod 3, i ≠ j → c ≠ 0 →
    Matrix.diagonal (fun r => if r = i then c else if r = j then c⁻¹ else 1) =
    ((elementary i j (c - 1) * elementary j i 1) *
      elementary i j (c⁻¹ - 1) * elementary j i (-c)).val := by
  have hinv : ∀ c : ZMod 3, c⁻¹ = c := by
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · exact inv_eq_of_mul_eq_one_left ((by decide : ∀ c : ZMod 3, c ≠ 0 → c * c = 1) c hc)
  simp only [hinv]
  decide

private theorem transvection_induction (P : SL → Prop)
    (htrans : ∀ (i j : Fin 3) (hij : i ≠ j) (c : ZMod 3), P (transvection hij c))
    (hmul : ∀ a b, P a → P b → P (a * b)) (a : SL) : P a := by
  apply diagonal_transvection_induction' P a ?_ htrans hmul
  intro i j hij c hc
  have hd : diag2n hij c hc =
      ((transvection hij (c - 1) * transvection hij.symm 1) *
        transvection hij (c⁻¹ - 1) * transvection hij.symm (-c)) := by
    apply Subtype.ext
    simpa [diag2n_coe, elementary, hij, hij.symm] using diag_matrix i j c hij hc
  rw [hd]
  exact hmul _ _ (hmul _ _ (hmul _ _ (htrans _ _ _ _) (htrans _ _ _ _))
    (htrans _ _ _ _)) (htrans _ _ _ _)

/-- The special linear group SL₃(3) is perfect. -/
public theorem sl3_three_isPerfect :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) := by
  constructor
  apply le_antisymm le_top
  intro a _
  apply transvection_induction (fun x => x ∈ commutator SL) ?_ (fun _ _ => mul_mem) a
  intro i j hij c
  have exists_mid : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, i ≠ k ∧ k ≠ j := by decide
  obtain ⟨k, hik, hkj⟩ := exists_mid i j hij
  have h := elementary_commutator i j k c hij hik hkj
  simp only [elementary, dif_pos hij] at h
  rw [← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem iSup_lineStab_eq_top :
    (⨆ p : ℙ (ZMod 3) (Fin 3 → ZMod 3), lineStab p.submodule) = (⊤ : Subgroup SL) := by
  apply le_antisymm le_top
  intro a _
  apply transvection_induction (fun x => x ∈ ⨆ p : ℙ (ZMod 3) (Fin 3 → ZMod 3),
    lineStab p.submodule) ?_ (fun _ _ => mul_mem) a
  intro i j hij c
  have hm := SL2Gen.transvection_mem_lineStab hij c
  rw [← Projectivization.submodule_mk (K := ZMod 3) _
    (Pi.single_ne_zero_iff.mpr one_ne_zero)] at hm
  exact (le_iSup (fun p : ℙ (ZMod 3) (Fin 3 → ZMod 3) => lineStab p.submodule) _) hm

private noncomputable def iwasawa : MulAction.IwasawaStructure Q (ℙ (ZMod 3) (Fin 3 → ZMod 3)) where
  T := PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (lineStab p.submodule) := by
      rw [← Projectivization.mk_rep p, Projectivization.submodule_mk]
      exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
    exact Subgroup.map_isMulCommutative _ _
  is_conj g p := by
    obtain ⟨g_SL, rfl⟩ := QuotientGroup.mk_surjective g
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
    change Subgroup.map _ _ = _
    rw [PSL.smul_submodule, Matrix.SpecialLinearGroup.lineStab_smul,
      PSL.iwasawaT_map_conj]
  is_generator := by
    change (⨆ p : ℙ (ZMod 3) (Fin 3 → ZMod 3),
      (lineStab p.submodule).map (QuotientGroup.mk' (Subgroup.center SL))) = ⊤
    rw [← Subgroup.map_iSup, iSup_lineStab_eq_top]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- The concrete projective special linear group PSL₃(3) is simple. -/
public theorem isSimpleGroup_psl3_three :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) := by
  let := sl3_three_isPerfect
  exact MulAction.IwasawaStructure.isSimpleGroup
    (Group.IsPerfect.commutator_eq_top (G := Q)) iwasawa inferInstance

/-- The concrete projective special linear group PSL₃(3) is nonsolvable. -/
public theorem not_isSolvable_psl3_three :
    ¬ Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) := by
  let := sl3_three_isPerfect
  exact Group.IsPerfect.not_isSolvable Q
