module

public import Theory.GroupTheory.GraphUniquenessSystem

/-!
# Local comparison of uniqueness systems

The rigidity criterion is Aschbacher, *Sporadic Groups*, Theorem 37.9. Two
isomorphisms of the edge fixer agree everywhere if they agree on its intersection
with the local group and that subgroup has trivial pointwise automorphism
centralizer. Apply this to the two ways of conjugating by an edge reversal.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem

universe u v u' v'
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable {G' : Type u'} {V' : Type v'} [Group G'] [MulAction G' V']

/-- The pointwise centralizer of a subgroup in the automorphism group is trivial. -/
def AutomorphismRigid {K : Type*} [Group K] (J : Subgroup K) : Prop :=
  ∀ a : MulAut K, (∀ j : J, a j = j) → a = MulEquiv.refl K

/-- Isomorphisms out of a group are determined on an automorphism-rigid subgroup. -/
theorem mulEquiv_eq_of_agree {K L : Type*} [Group K] [Group L]
    {J : Subgroup K} (hJ : AutomorphismRigid J) (f g : K ≃* L)
    (h : ∀ j : J, f j = g j) : f = g := by
  have he : f.trans g.symm = MulEquiv.refl K := hJ _ (by
    intro j
    change g.symm (f j) = j
    rw [h j, g.symm_apply_apply])
  ext k
  have hk := congrArg (fun a : MulAut K => a k) he
  exact g.symm.injective (hk.trans (g.symm_apply_apply k).symm)

namespace System
variable (U : System G V)

/-- Conjugation by an edge reversal, restricted to the pointwise edge fixer. -/
def edgeConj (t : G) (htx : t • U.x = U.y) (hty : t • U.y = U.x) :
    MulAut U.edgeGroup where
  toFun b := ⟨t * b * t⁻¹, U.conj_mem_edgeGroup htx hty b.property⟩
  invFun b := ⟨t⁻¹ * b * (t⁻¹)⁻¹, U.conj_mem_edgeGroup
    (by rw [inv_smul_eq_iff, hty]) (by rw [inv_smul_eq_iff, htx]) b.property⟩
  left_inv b := by apply Subtype.ext; simp [mul_assoc]
  right_inv b := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

end System

namespace Similarity
variable {U : System G V} {U' : System G' V'} (s : Similarity U U')

/-- Restriction of the vertex isomorphism to the pointwise edge fixers. -/
def edgeIso : U.edgeGroup ≃* U'.edgeGroup where
  toFun b := ⟨s.vertexIso ⟨b, b.property.1⟩, (s.edge _).mp b.property⟩
  invFun b := ⟨s.vertexIso.symm ⟨b, b.property.1⟩,
    (s.edge _).mpr (by simp)⟩
  left_inv b := by
    apply Subtype.ext
    exact congrArg (fun a : U.vertexGroup => (a : G))
      (s.vertexIso.symm_apply_apply ⟨b, b.property.1⟩)
  right_inv b := by
    apply Subtype.ext
    exact congrArg (fun a : U'.vertexGroup => (a : G'))
      (s.vertexIso.apply_symm_apply ⟨b, b.property.1⟩)
  map_mul' a b := by
    apply Subtype.ext
    exact congrArg (fun c : U'.vertexGroup => (c : G'))
      (s.vertexIso.map_mul ⟨a, a.property.1⟩ ⟨b, b.property.1⟩)

/-- On local elements of the edge fixer, restriction agrees with the local isomorphism. -/
theorem edgeIso_agree (b : U.edgeGroup) (hb : (b : G) ∈ U.H) :
    (s.edgeIso b : G') = (s.localIso ⟨b, hb⟩ : G') :=
  s.agree b hb b.property.1

/-- Theorem 37.9: rigidity of the edge fixer upgrades similarity to equivalence. -/
theorem isEquivalence_of_rigid
    (hRigid : AutomorphismRigid (U.H.subgroupOf U.edgeGroup)) : s.IsEquivalence := by
  obtain ⟨t, htx, hty⟩ := U.exists_swap
  obtain ⟨htx', hty'⟩ := s.map_swap t htx hty
  let f := (U.edgeConj t htx hty).trans s.edgeIso
  let g := s.edgeIso.trans (U'.edgeConj (s.localIso t) htx' hty')
  have he : f = g := mulEquiv_eq_of_agree hRigid f g (by
    intro j
    apply Subtype.ext
    change (s.edgeIso (U.edgeConj t htx hty j) : G') =
      (s.localIso t : G') * (s.edgeIso j : G') * (s.localIso t : G')⁻¹
    rw [s.edgeIso_agree j j.property]
    have hj : ((U.edgeConj t htx hty j : U.edgeGroup) : G) ∈ U.H :=
      U.H.mul_mem (U.H.mul_mem t.property j.property) (U.H.inv_mem t.property)
    rw [s.edgeIso_agree _ hj]
    change (s.localIso (t * ⟨(j : U.edgeGroup), j.property⟩ * t⁻¹) : G') = _
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv])
  refine ⟨t, htx, hty, ?_⟩
  intro b
  exact congrArg (fun e : U.edgeGroup ≃* U'.edgeGroup => (e b : G')) he

end Similarity

end Theory.GroupTheory.GraphUniquenessSystem
