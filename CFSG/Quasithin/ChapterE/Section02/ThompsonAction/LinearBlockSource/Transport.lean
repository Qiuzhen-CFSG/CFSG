module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
/-!
# Transporting the actual χ₀ block from a normal subgroup

The natural block module is transported together with the core quotient.
Subnormality then lifts a χ₀ block in a normal subgroup to the original group.

Source: the block definitions in Aschbacher--Smith C.1.12, p.121.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource
open ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem chiZero_of_equiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : IsChiZeroBlock A) : IsChiZeroBlock B := by
  rcases h with ⟨n,hn,hs,F,hF,hfi,hcard,hquot,hm⟩ | ha | ha
  · refine Or.inl ⟨n,hn,RankOne.Solvable.isShort_of_equiv e hs,F,hF,hfi,hcard,?_,?_⟩
    · exact hquot.of_mulEquiv (QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)).symm
    · obtain ⟨ρ,⟨m⟩,hρ⟩ := hm
      have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
      have hp : IsPGroup 2 e.toMonoidHom.ker := by rw [hk]; exact IsPGroup.of_bot
      obtain ⟨m'⟩ := BlockModuleModel.exists_of_central_two_quotient e.toMonoidHom e.surjective
        hs.twoPerfect hp (hk ▸ bot_le) ρ m
      exact ⟨ρ,⟨m'⟩,hρ⟩
  · exact Or.inr (Or.inl (RankOne.Solvable.isAlternatingBlock_of_equiv e ha))
  · exact Or.inr (Or.inr (RankOne.Solvable.isAlternatingBlock_of_equiv e ha))

theorem chiZero_map_normal_subgroup (N : Subgroup G) [N.Normal]
    (L : Subgroup N) (hL : IsChiZeroBlockIn L) : IsChiZeroBlockIn (L.map N.subtype) := by
  let e := L.equivMapOfInjective N.subtype N.subtype_injective
  exact ⟨⟨inferInstance,RankOne.Solvable.isShort_of_equiv e hL.1.short,
    hL.1.subnormal.trans' (inferInstance : N.Normal).isSubnormal⟩,chiZero_of_equiv e hL.2⟩
end CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource
