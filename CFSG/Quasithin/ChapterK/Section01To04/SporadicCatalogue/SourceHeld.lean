module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.HeldExclusion
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Held
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Faithfulness
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.SpecificGroups.Held.ThreeConjugates
public import Theory.SpecificGroups.Held.TwoRank.Normalizer

/-!
# Held is excluded on the original cubic source domain

The center of a perfect central cover of the actual Held group is a 2-group.
Faithfulness and irreducibility in characteristic two therefore remove that
center. The native Held degree lower bound is forty-two, whereas three
conjugates and automorphism 2-rank at most six bound a source module of cubic
ratio at most two by thirty-six. All cover and automorphism premises are
supplied by their concrete carrier theorems.

Source: Aschbacher--Smith K.4, printed p.457, and B.4.2, printed p.86.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem held_automorphism_rank : primeRank 2 (MulAut Held.He) ≤ 6 := by
  let e := MulEquiv.ofBijective Held.permutationGroup.normalizerMonoidHom
    ⟨Held.OuterInvolution.normalizer_action_injective, Held.Realization.normalizer_surjective⟩
  exact (primeRank_le_of_injective 2 e.symm.toMonoidHom e.symm.injective).trans
    (Held.TwoRank.normalizer_twoRank_le_six Held.permutationNormalizerQuotient_card_le_two)

/-- The Held central quotient cannot occur even on the full cubic source domain. -/
theorem held_impossible (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.he.Carrier)) : False := by
  obtain ⟨e⟩ := he
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := h.layer_normal
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hz2 := Held.OddPrimary.center_isPGroup_of_quotient_equiv e
  have hk := normal_p_subgroup_le_ker (ρ.comp L.subtype) (center L) hz2
  have hZ : center L = ⊥ := by
    apply bot_unique
    simpa only [(ρ.comp L.subtype).ker_eq_bot_iff.mpr
      (h.faithful.comp L.subtype_injective)] using hk
  let eL : L ≃* Held.He :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  have hlow := Held.BinaryDegree.finrank_ge_fortyTwo
    ((ρ.comp L.subtype).comp eL.symm.toMonoidHom)
    (h.faithful.comp (L.subtype_injective.comp eL.symm.injective))
  have hupp := finrank_le_six_mul_of_cubic_central_quotient ρ L
    h.faithful h.irreducible e
    (Held.threeConjugateAutomorphisms Held.Realization.normalizer_surjective)
    held_automorphism_rank h.smallCubic
  omega
end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF

namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory
universe u v
/-- The literal Held entry is excluded without additional model premises. -/
theorem sourceExclusion_he : SourceExclusion.{u,v} .he := by
  intro G V _ _ _ _ _ ρ h he
  exact SourceFF.held_impossible {
    sqtk := h.sqtk
    fitting := rfl
    quasisimple := h.quasisimple
    faithful := h.faithful
    irreducible := h.irreducible
    smallCubic := h.cubic_le_two } he
end CFSG.Quasithin.ChapterK.SporadicCatalogue
