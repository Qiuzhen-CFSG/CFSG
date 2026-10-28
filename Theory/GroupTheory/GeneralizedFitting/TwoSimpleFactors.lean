module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Nilpotent

/-!
# Components in two centerless quasisimple factors

A component in a product of two centerless quasisimple groups is one of its
factors. A component also survives any homomorphism whose kernel is a 2-group.
Together these facts recognize the component orbit of the quadratic four-group
model. Source: GLS2, component calculus and Theorem 25.14.
-/

public section
open Subgroup
namespace Theory.GroupTheory

lemma IsComponent.prod_cases {S : Type*} [Group S] [IsQuasisimple S]
    (hz : center S = ⊥) {K : Subgroup (S × S)} (hK : IsComponent (S × S) K) :
    K = (MonoidHom.inl S S).range ∨ K = (MonoidHom.inr S S).range := by
  let P := (MonoidHom.inl S S).range
  let Q := (MonoidHom.inr S S).range
  let : P.Normal := ⟨by
    rintro _ ⟨x,rfl⟩ g
    exact ⟨g.1*x*g.1⁻¹, by ext <;> simp⟩⟩
  let : Q.Normal := ⟨by
    rintro _ ⟨x,rfl⟩ g
    exact ⟨g.2*x*g.2⁻¹, by ext <;> simp⟩⟩
  have hP : IsComponent (S × S) P := ⟨(inferInstance : P.Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective
      (show Function.Injective (MonoidHom.inl S S) from fun x y he => congrArg Prod.fst he))⟩
  have hQ : IsComponent (S × S) Q := ⟨(inferInstance : Q.Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective
      (show Function.Injective (MonoidHom.inr S S) from fun x y he => congrArg Prod.snd he))⟩
  rcases hK.normal_dichotomy P with hp | hc
  · exact Or.inl (hK.eq_of_le hP hp)
  · apply Or.inr
    apply hK.eq_of_le hQ
    intro z hzK
    have hzc : z.1 ∈ center S := by
      apply mem_center_iff.mpr
      intro s
      have hh := mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hc hzK) (s,1) ⟨s,rfl⟩
      exact congrArg Prod.fst hh
    have hz1 : z.1 = 1 := mem_bot.mp (hz ▸ hzc)
    exact ⟨z.2, Prod.ext hz1.symm rfl⟩

lemma IsComponent.map_ne_bot_of_twoGroup_kernel
    {G H : Type*} [Group G] [Finite G] [Group H]
    {L : Subgroup G} (hL : IsComponent G L) (f : G →* H) (hker : IsPGroup 2 f.ker) :
    L.map f ≠ ⊥ := by
  intro he
  have hl := (map_eq_bot_iff L).mp he
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  let : Group.IsNilpotent L := (hker.to_le hl).isNilpotent
  exact Group.IsPerfect.not_isSolvable L inferInstance
end Theory.GroupTheory

