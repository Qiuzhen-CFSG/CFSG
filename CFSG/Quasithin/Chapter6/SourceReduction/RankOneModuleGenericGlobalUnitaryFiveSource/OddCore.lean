module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FieldTransfer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.LongRoot
public import Theory.GroupTheory.CharacteristicTwoInheritance
public import Theory.GroupTheory.OddCoreKleinFourCentralizers
public import Theory.GroupTheory.PPrimeCoreReduction

/-!
# Trivial odd cores of all ambient involution centralizers in the U₅(4) row

Each nonidentity element of the original long-root four-group has its full
centralizer in the line normalizer. Characteristic-two inheritance from that
normalizer proves characteristic two for these full ambient centralizers.
The proved Klein-four centralizer theorem therefore eliminates the odd core
of C_G(x) whenever x is an involution in the whole residual: the long-root
four-group centralizes x. Cyclic field transfer puts every ambient involution
into the original S, which lies in that residual. Conjugation transports the
odd-core conclusion back to the original ambient centralizer.

This uses the actual full centralizers, their literal subgroup embeddings,
and the original KnownSimple input. It does not assert S=T or identify the
full short centralizer with its local subgroup. The marked common-centralizer
module and Chapter12 consume these results on the same source row.
Source: Aschbacher--Smith F.4.34,38,42, printed pp.291,294--296;
characteristic-two inheritance is 1.1.3--4, pp.500--501.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
/-- Full ambient centralizers of nonidentity long-root elements have
characteristic two, inherited from the original line normalizer. -/
theorem Preparation.unitaryFive_long_centralizers_characteristic
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (z : G) (hz : z ∈ (center (residual H)).map (residual H).subtype) (hz1 : z ≠ 1) :
    HasCharacteristicTwo (centralizer ({z} : Set G)) := by
  obtain ⟨hZ,_,_⟩ := d.unitaryFive_right_center_fusion h hH hp U hc
  let := hZ
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz) hz1
  have hloc := d.unitaryFive_normalizer_local_conditions h hH hp U hc
  have hM : normalizer (residual H : Set G) ∈ Chapter1.He G :=
    Chapter1.mem_He_iff.mpr ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hloc.fitting_right)
  have hzM : z ∈ normalizer (residual H : Set G) :=
    (residual H).le_normalizer (map_subtype_le _ hz)
  have hzp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers,pow_one] using hz2)
  have hh := pCoreIn_selfCentralizing_centralizer hM hzp (zpowers_le.mpr hzM)
  have he : centralizer (zpowers z : Set G) = centralizer ({z} : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
  have hbound := d.unitaryFive_central_involution_centralizers h hH hp U hc 1 z hz hz2
  have hmeet : normalizer (residual H : Set G) ⊓ centralizer ({z} : Set G) =
      centralizer ({z} : Set G) := inf_eq_right.mpr hbound
  dsimp only at hh
  rw [he,hmeet] at hh
  exact Chapter1.mem_He_iff.mp hh

/-- The original long-root four-group detects the odd core of the full
ambient centralizer of every involution in the whole residual. -/
theorem Preparation.unitaryFive_residual_involution_centralizer_oddCore
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (x : G) (hx : x ∈ residual H) (hx2 : orderOf x = 2) :
    pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ := by
  let Z := (center (residual H)).map (residual H).subtype
  have hZ := (d.unitaryFive_right_center_fusion h hH hp U hc).1
  let := hZ
  have hcard : Nat.card Z = 4 :=
    (card_map_of_injective (residual H).subtype_injective).trans
      (d.unitaryFive_right_center_card h hH hp U hc)
  have hZx : Z ≤ centralizer ({x} : Set G) := by
    rintro z ⟨v,hv,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (residual H).subtype (mem_center_iff.mp hv ⟨x,hx⟩)).symm
  exact pPrimeCore_centralizer_eq_bot_of_klein_four x hx2 Z hcard hZx
    (d.unitaryFive_long_centralizers_characteristic h hH hp U hc)

/-- Every ambient involution centralizer has trivial odd core. Fusion into
S supplies the residual placement; no Sylow equality is assumed. -/
theorem Preparation.unitaryFive_involution_centralizer_oddCore
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (x : G) (hx : orderOf x = 2) :
    pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ := by
  obtain ⟨y,hy,hxy⟩ := d.unitaryFive_involution_fused_into_sourceS h hH hp U hc x hx
  have hyR : y ∈ (T : Subgroup G) ⊓ L :=
    (d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc).le hy
  have hyK : y ∈ residual H :=
    ((d.common_sylow_of_comparison h hH.1.1.2 hp (.unitaryFive U hc)).le hyR).2
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  have he : MulAut.conj g x = y := hg
  have hy2 : orderOf y = 2 := by
    rw [←he]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  have hodd := d.unitaryFive_residual_involution_centralizer_oddCore h hH hp U hc y hyK hy2
  rw [←he] at hodd
  exact pPrimeCore_eq_bot_of_equiv (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) x) hodd

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
