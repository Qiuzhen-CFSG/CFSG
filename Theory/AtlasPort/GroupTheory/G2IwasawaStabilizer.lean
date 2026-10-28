module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/GroupTheory/IwasawaStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Subgroup.Simple

/-! A normal abelian subgroup of a point stabilizer in a faithful primitive perfect group implies simplicity when its conjugates generate the group. -/

@[expose] public section

namespace Atlas.GroupTheory
variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPreprimitive G X]

-- Retain the source theorem’s action hypotheses for API compatibility.
set_option linter.unusedSectionVars false in
theorem normal_sup_abelian_eq_top (a : X) (A : Subgroup G)
    (hA : A ≤ MulAction.stabilizer G a)
    (hAn : (A.subgroupOf (MulAction.stabilizer G a)).Normal)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤)
    (L : Subgroup G) [L.Normal] [MulAction.IsPretransitive L X] : L ⊔ A = ⊤ := by
  have hc : Subgroup.normalClosure (A : Set G) ≤ L ⊔ A := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨b,hb,hbx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hbx
    obtain ⟨n,hn⟩ := MulAction.exists_smul_eq L a (g • a)
    let s : MulAction.stabilizer G a := ⟨n.val⁻¹*g,by
      change (n.val⁻¹*g) • a = a
      rw [mul_smul,← hn]
      exact inv_smul_smul n.val a⟩
    let b' : MulAction.stabilizer G a := ⟨b,hA hb⟩
    have hs : s*b'*s⁻¹ ∈ A.subgroupOf (MulAction.stabilizer G a) :=
      hAn.conj_mem b' hb s
    have hsa : s.val*b*s.val⁻¹ ∈ A := hs
    have he : g*b*g⁻¹ = n.val * (s.val*b*s.val⁻¹) * n.val⁻¹ := by
      dsimp [s]
      group
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.prop)
      (Subgroup.mem_sup_right hsa)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left n.prop))
  exact top_unique (hgen ▸ hc)

theorem iwasawa_stabilizer_normal_subgroups [Group.IsPerfect G]
    (a : X) (A : Subgroup G) (hA : A ≤ MulAction.stabilizer G a)
    (hAn : (A.subgroupOf (MulAction.stabilizer G a)).Normal) (hAc : IsMulCommutative A)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤)
    (L : Subgroup G) [hL : L.Normal] : L = ⊥ ∨ L = ⊤ := by
  by_cases hbot : L = ⊥
  · exact Or.inl hbot
  · let := normal_pretransitive (X := X) L hbot
    have he := normal_sup_abelian_eq_top a A hA hAn hgen L
    have hc := hL.commutator_le_of_self_sup_commutative_eq_top he hAc
    rw [Group.IsPerfect.commutator_eq_top] at hc
    exact Or.inr (top_unique hc)

theorem iwasawa_stabilizer_simple [Nontrivial G] [Group.IsPerfect G]
    (a : X) (A : Subgroup G) (hA : A ≤ MulAction.stabilizer G a)
    (hAn : (A.subgroupOf (MulAction.stabilizer G a)).Normal) (hAc : IsMulCommutative A)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤) : IsSimpleGroup G := by
  constructor
  intro L hL
  exact iwasawa_stabilizer_normal_subgroups a A hA hAn hAc hgen L

end Atlas.GroupTheory
