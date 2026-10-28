module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.InnerSylow
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Inner
public import Theory.GroupTheory.CoprimeIndexMarking

/-!
# Odd outer degree on the same U₅(4) extension

The equality S=T makes the transported middle Sylow inner. Its index
therefore proves that this same extension has odd outer degree. In the
original plane normalizer, the normal subgroup L contains the full ambient
Sylow; hence every two-subgroup of that normalizer lies in L. These are the
parity and return premises needed in the two short-centralizer quotients.

Source: Aschbacher–Smith F.4.38,42, printed pp.294–296 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The given extension has odd degree over its literal inner subgroup. -/
theorem Preparation.unitaryFive_outer_odd
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    ¬ 2 ∣ (inner U.Carrier).relIndex r.extension.carrier := by
  have hST := d.unitaryFive_sourceS_eq_sylow h hH hp U hc r
  obtain ⟨a,ell,F,h0,h1,hD,hE,hleft,hright,hmiddle,P,hP,hinner,_⟩ :=
    d.unitaryFive_marked_sylow_split h hH hp U hc r
  have hPI : (P : Subgroup r.extension.middle) ≤ r.extension.nativeOverlap := by
    rw [hST,←hP] at hinner
    exact inf_eq_left.mp hinner
  have hr : r.extension.baseHom.range = (inner U.Carrier).subgroupOf r.extension.carrier := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  change ¬ 2 ∣ ((inner U.Carrier).subgroupOf r.extension.carrier).index
  rw [←hr,←r.extension.nativeOverlap_index_eq]
  exact fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPI))

/-- Every original plane-normalizer two-subgroup lies in the whole residual L. -/
theorem Preparation.unitaryFive_normalizer_two_subgroup_le_left
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (L : Set G)) :
    P ≤ L := by
  have hTL : (T : Subgroup G) ≤ L := by
    rw [←d.unitaryFive_sourceS_eq_sylow h hH hp U hc r,
      d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc]
    exact inf_le_right
  let N := normalizer (L : Set G)
  have hindex : ¬ 2 ∣ (L.subgroupOf N).index := by
    intro hd
    exact (T.subtype h.sylow_normalizes).not_dvd_index
      (hd.trans (index_dvd_of_le (show (T.subtype h.sylow_normalizes : Subgroup N) ≤
        L.subgroupOf N from fun x hx => hTL hx)))
  have hle := IsPGroup.le_normal_of_index_primeTo (L.subgroupOf N)
    (P.subgroupOf N) hP.comap_subtype hindex
  intro x hx
  exact hle (show (⟨x,hPN hx⟩ : N) ∈ P.subgroupOf N from hx)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
