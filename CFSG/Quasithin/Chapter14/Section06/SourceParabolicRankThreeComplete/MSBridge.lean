module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedA6MSInput
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoReconstruction

/-!
# The literal C.2.7 component-radical product as a small MS-pair

The odd-index witness restricts to KR with its original embedded two-core.
The characteristic-normalizer condition transfers across the inclusion of R
in KR, yielding precisely MS3. Thus a central-core quotient marking supplies
all hypotheses of the existing small MS reconstruction contract. In the A₆
row that contract retains both the natural block and exceptional triple cover.

This is the bridge used by the original 14.6.10(5) A₆ branch; reconstruction
itself remains the independently owned C.1.32 theorem.
Source: Aschbacher--Smith C.1.31--32, pp.135--136, C.2.7, pp.146--147,
and original 14.6.10(5), p.1029.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (D : Subgroup A) [D.Characteristic] :
    (D.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply (a (e y))

/-- A small central-core quotient turns the original C.2.7 input into
an MS-pair, without assuming that the radical is Sylow. -/
theorem smallMSPair_from_c27 {κ : GroupClass.{u}} {H R M K : Subgroup G}
    (h : Input κ H R M K)
    (hr : ChapterC.MSOddIndexRadical (R.subgroupOf H))
    (hm : SmallRankTwoQuotient K) : SmallMSPair κ K R := by
  let J := K ⊔ R
  let hj := ChapterC.C27Source.source_join_input h
  let : (K.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  refine ⟨inferInstance,hj.setup.sqtk,ChapterC.C27Source.source_join_fitting h,
    ?_,hj.component.2,hm,?_,?_⟩
  · intro g hg
    have hs : K.subgroupOf J ⊔ R.subgroupOf J = ⊤ := by
      rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
    obtain ⟨k,hk,r,hr,he⟩ := mem_sup_of_normal_left.mp (hs.ge (mem_top (⟨g,hg⟩ : J)))
    exact ⟨k,hk,r,hr,congrArg Subtype.val he⟩
  · obtain ⟨P,hP,ho,hcore⟩ := ChapterC.C27Source.msOddIndexRadical_join_from_source h hr
    have htop : (⊤ : Subgroup J).map J.subtype = J := by
      rw [←MonoidHom.range_eq_map,range_subtype]
    refine ⟨P.map J.subtype,?_,?_,?_⟩
    · simpa only [htop] using
        (map_lt_map_iff_of_injective J.subtype_injective).mpr hP
    · change Odd ((P.map J.subtype).comap J.subtype).index
      rwa [comap_map_eq_self_of_injective J.subtype_injective]
    · change P.pCoreIn 2 = R.subgroupOf J at hcore
      rw [←map_pCoreIn_of_injective 2 _ _ J.subtype_injective,hcore,
        map_subgroupOf_eq_of_le le_sup_right]
  · intro D hD hn
    let := hD
    let a : R ≃* R.subgroupOf J := (subgroupOfEquivOfLe (show R ≤ J from le_sup_right)).symm
    let E := D.map a.toMonoidHom
    let : E.Characteristic := characteristic_map_equiv a D
    have hE : E.map (R.subgroupOf J).subtype = (D.map R.subtype).subgroupOf J := by
      ext x
      constructor
      · rintro ⟨y,⟨d,hd,rfl⟩,rfl⟩
        exact ⟨d,hd,rfl⟩
      · rintro ⟨d,hd,he⟩
        refine ⟨a d,mem_map_of_mem _ hd,?_⟩
        exact Subtype.ext he
    have hbot : E = ⊥ :=
      (ChapterC.C27Source.join_msCharacteristic_from_source h).eq_bot_of_normal E (hE ▸ hn)
    exact (map_eq_bot_iff_of_injective D a.injective).mp hbot

/-- Whole-core A₆ reconstruction gives the two genuine C.1.32 block
alternatives on the original component carrier. -/
theorem alternatingSix_or_exceptional_from_c27
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    {H R M K : Subgroup G} (h : Input KnownSimple.IsKnownSimple H R M K)
    (hr : ChapterC.MSOddIndexRadical (R.subgroupOf H))
    (eA : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) :
    ChapterC.IsAlternatingBlock K 6 ∨ ChapterC.IsExceptionalAhat6Block K := by
  let es := eA.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp)).symm
  have hm := smallMSPair_from_c27 h hr (Or.inr (Or.inl ⟨es⟩))
  have r := ha G K R hm es
  have hs := hm.short_of_core r.elementary r.central h.quasisimple r.irreducible
  rcases r.model with hn | ⟨hz,hu,hc⟩
  · exact Or.inl ⟨by decide,hs,hn⟩
  · exact Or.inr ⟨hs,h.quasisimple,hz,
      ⟨(centralPreimageQuotientEquiv (pCore 2 K)).symm.trans eA⟩,hu,hc⟩
end CFSG.Quasithin.Chapter14.Section06
