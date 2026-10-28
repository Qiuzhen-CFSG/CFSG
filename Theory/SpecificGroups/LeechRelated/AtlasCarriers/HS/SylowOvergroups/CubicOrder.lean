module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Overgroups
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart

/-!
# The three-part of proper Higman--Sims Sylow overgroups

Conjugate the given full Sylow to the fixed native Sylow. The exhaustive
cover puts a proper overgroup in one of the two literal local normalizers,
both of order indivisible by nine. Divisibility of subgroup orders carries
that obstruction back through the conjugation, without a maximality premise.
Source: Aschbacher--Smith A.3.12(18), pp.47--48, used in 12.5.3, p.818.
The imported modules retain the ATLAS carrier and checked certificates.
-/
public noncomputable section
open Subgroup
namespace Sporadic.LeechRelated.HS.SylowOvergroups

/-- Nine does not divide the order of any proper full-Sylow overgroup. -/
theorem proper_overgroup_not_nine_dvd
    (S : Sylow 2 Sporadic.LeechRelated.HS.Carrier)
    (D : Subgroup Sporadic.LeechRelated.HS.Carrier)
    (hSD : (S : Subgroup _) ≤ D) (hD : D ≠ ⊤) : ¬ 9 ∣ Nat.card D := by
  let c := MulAut.conj (Classical.choose (MulAction.exists_smul_eq
    Sporadic.LeechRelated.HS.Carrier S Sporadic.LeechRelated.HS.BlockNormalizer.baseSylow))
  have hg := Classical.choose_spec (MulAction.exists_smul_eq
    Sporadic.LeechRelated.HS.Carrier S Sporadic.LeechRelated.HS.BlockNormalizer.baseSylow)
  have hS : (S : Subgroup _).map c.toMonoidHom =
      Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup :=
    congrArg Sylow.toSubgroup hg
  have hDc : D.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hD
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  intro hd
  have hd' : 9 ∣ Nat.card (D.map c.toMonoidHom) := by
    rwa [card_map_of_injective c.injective]
  rcases Sporadic.LeechRelated.HS.SylowOvergroups.proper_overgroup_le
      (D.map c.toMonoidHom) (hS ▸ map_mono hSD) hDc with hl | hl
  · exact Sporadic.LeechRelated.HS.EvenLocalCandidates.central_localGroup_nine_not_dvd
      (hd'.trans (card_dvd_of_le hl))
  · exact Sporadic.LeechRelated.HS.EvenLocalCandidates.large_localGroup_nine_not_dvd
      2 (by decide) (hd'.trans (card_dvd_of_le hl))

end Sporadic.LeechRelated.HS.SylowOvergroups
