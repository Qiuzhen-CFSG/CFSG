module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The conjugate-generation argument is adapted from
Atlas/GroupTheory/IwasawaStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: retain the normal closure instead of assuming it is the whole group,
and deduce containment in nontrivial normal subgroups from its perfectness.
-/

public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Mathlib.GroupTheory.IsPerfect

/-!
# The perfect normal closure in the Iwasawa argument

Let A be an abelian normal subgroup of a point stabilizer. Every transitive
subgroup N satisfies ⟨Aᴳ⟩ ≤ NA. When N is normal, the image of ⟨Aᴳ⟩ in G/N
is therefore abelian. If this normal closure is perfect, that image is trivial.
In a faithful primitive action, every nontrivial normal subgroup is transitive,
so the perfect normal closure lies in every such subgroup.

This is the stabilizer Iwasawa argument from the attributed ATLAS source above,
without the requirement that A normally generate all of G.
-/

public section

namespace Subgroup
variable {G : Type*} [Group G]

/-- A perfect subgroup contained in a normal subgroup times one of its own
abelian subgroups is contained in the normal subgroup. -/
theorem le_normal_of_perfect_of_le_sup_commutative
    (H N A : Subgroup G) [N.Normal] [Group.IsPerfect H] [IsMulCommutative A]
    (hA : A ≤ H) (h : H ≤ N ⊔ A) : H ≤ N := by
  let q := QuotientGroup.mk' N
  have he : H.map q = A.map q := by
    apply le_antisymm
    · calc
        H.map q ≤ (N ⊔ A).map q := map_mono h
        _ = A.map q := by simp [q, map_sup]
    · exact map_mono hA
  let : Group.IsPerfect (A.map q) := he ▸ Group.IsPerfect.map q (H := H)
  have hb : H.map q = ⊥ := he.trans (A.map q).eq_bot_of_subsingleton
  simpa [q] using (map_eq_bot_iff H).mp hb

end Subgroup

namespace MulAction
variable {G X : Type*} [Group G] [MulAction G X]

/-- The conjugates of a stabilizer-normal subgroup lie in its join with any
transitive subgroup. No normality of the transitive subgroup is required. -/
theorem normalClosure_le_sup_of_pretransitive (a : X) (A : Subgroup G)
    (hA : A ≤ stabilizer G a)
    (hAn : (A.subgroupOf (stabilizer G a)).Normal)
    (N : Subgroup G) [IsPretransitive N X] :
    Subgroup.normalClosure (A : Set G) ≤ N ⊔ A := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨b, hb, hbx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp hbx
  obtain ⟨n, hn⟩ := exists_smul_eq N a (g • a)
  let s : stabilizer G a := ⟨n.val⁻¹ * g, by
    change (n.val⁻¹ * g) • a = a
    rw [mul_smul, ← hn]
    exact inv_smul_smul n.val a⟩
  let b' : stabilizer G a := ⟨b, hA hb⟩
  have hs : s * b' * s⁻¹ ∈ A.subgroupOf (stabilizer G a) :=
    hAn.conj_mem b' hb s
  have hsa : s.val * b * s.val⁻¹ ∈ A := hs
  have he : g * b * g⁻¹ = n.val * (s.val * b * s.val⁻¹) * n.val⁻¹ := by
    dsimp [s]
    group
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.prop)
    (Subgroup.mem_sup_right hsa)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left n.prop))

/-- In a faithful primitive action, a perfect normal closure of an abelian
stabilizer-normal subgroup lies in every nontrivial normal subgroup. -/
theorem perfect_normalClosure_le_normal
    [FaithfulSMul G X] [IsPreprimitive G X]
    (a : X) (A : Subgroup G) [IsMulCommutative A]
    [Group.IsPerfect (Subgroup.normalClosure (A : Set G))]
    (hA : A ≤ stabilizer G a)
    (hAn : (A.subgroupOf (stabilizer G a)).Normal)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) :
    Subgroup.normalClosure (A : Set G) ≤ N := by
  let := Atlas.GroupTheory.normal_pretransitive (X := X) N hne
  exact Subgroup.le_normal_of_perfect_of_le_sup_commutative _ N A
    Subgroup.subset_normalClosure (normalClosure_le_sup_of_pretransitive a A hA hAn N)

end MulAction
