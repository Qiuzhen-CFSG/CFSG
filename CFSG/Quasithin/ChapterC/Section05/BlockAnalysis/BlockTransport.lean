module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits

/-!
# Literal transport of the C.5.3 block types

Faithful inclusion into a subnormal subgroup preserves both the original
short group and its specified natural conjugation module. The χ₀ alternatives
are retained separately, so no larger alternating block type is introduced.

Source: Aschbacher–Smith C.1.12 and C.5.3, printed pp.124 and154–155.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

theorem chiZero_equiv (e : A ≃* B) (h : IsChiZeroBlock A) : IsChiZeroBlock B := by
  rcases h with ⟨n,hn,hs,F,hF,hfin,hcard,hq,hm⟩ | ha | ha
  · refine Or.inl ⟨n,hn,RankOne.Solvable.isShort_of_equiv e hs,F,hF,hfin,hcard,?_,?_⟩
    · exact hq.of_mulEquiv
        (QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)).symm
    · obtain ⟨ρ,⟨m⟩,hρ⟩ := hm
      have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
      have hp : IsPGroup 2 e.toMonoidHom.ker := by rw [hk]; exact IsPGroup.of_bot
      obtain ⟨m'⟩ := BlockModuleModel.exists_of_central_two_quotient e.toMonoidHom
        e.surjective hs.twoPerfect hp (hk ▸ bot_le) ρ m
      exact ⟨ρ,⟨m'⟩,hρ⟩
  · exact Or.inr (Or.inl (RankOne.Solvable.isAlternatingBlock_of_equiv e ha))
  · exact Or.inr (Or.inr (RankOne.Solvable.isAlternatingBlock_of_equiv e ha))

/-- A faithful homomorphism with subnormal range preserves the actual χ₀ block. -/
theorem chiZero_map (f : A →* B) (hf : Function.Injective f)
    (hr : f.range.IsSubnormal) {L : Subgroup A} (hL : IsChiZeroBlockIn L) :
    IsChiZeroBlockIn (L.map f) := by
  have he := equivMapOfInjective L f hf
  refine ⟨⟨inferInstance,RankOne.Solvable.isShort_of_equiv he hL.1.short,?_⟩,
    chiZero_equiv he hL.2⟩
  have hs := (hL.1.subnormal.map f.rangeRestrict_surjective).trans' hr
  rw [Subgroup.map_map] at hs
  exact hs

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
