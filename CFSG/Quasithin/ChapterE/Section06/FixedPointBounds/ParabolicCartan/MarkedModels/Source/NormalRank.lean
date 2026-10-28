module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalClauses
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Two-rank in the original normal-component quotient

The source kernel modulo the two-core is the center of the normal component
image. That image has trivial two-core, so its center has odd order. The
original projection from H/O₂(H) to H/J therefore has coprime kernel and
preserves two-rank. This transfers the unitary automorphism rank bound without
removing the possible central subgroup of order three.

Source: Aschbacher–Smith E.2.2(2), printed pp. 215–216; applied in 14.2.16.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

/-- The original two-core and normal-core quotients have the same two-rank. -/
theorem source_single_two_rank_eq
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    primeRank 2 (H ⧸ pCore 2 H) =
      primeRank 2 (H ⧸ sourceKernel (ChapterB.minimalParabolicMax T hP)) := by
  let N := sourceKernel (ChapterB.minimalParabolicMax T hP)
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : (actorImage K).Normal := Subgroup.Normal.map inferInstance q hq
  have hcore : pCore 2 (actorImage K) = ⊥ := by
    rw [pCore_eq_comap_of_normal, pCore_quotient_pCore_eq_bot]
    exact (actorImage K).subtype.ker_eq_bot (actorImage K).subtype_injective
  have hodd : ¬ 2 ∣ Nat.card (center (actorImage K)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hcore _ le_rfl
  let f := QuotientGroup.lift (pCore 2 H) (QuotientGroup.mk' N)
    (by simpa only [QuotientGroup.ker_mk'] using twoCore_le_sourceKernel T hP)
  have hk : f.ker = (center (actorImage K)).map (actorImage K).subtype := by
    rw [QuotientGroup.ker_lift, QuotientGroup.ker_mk']
    exact (source_single_clauses T hP hs K hK hqK hgen).kernel_center
  have hc : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hk, Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (actorImage K).subtype_injective).toEquiv.symm]
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hodd
  exact primeRank_eq_of_surjective_of_coprime 2 f
    (QuotientGroup.lift_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective N) _) hc
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
