module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Parabolics
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSInputs

/-!
# The original half-Sylow MS conditions from normalizer escape

Put T₁=N_T(L). If N_G(T₁) escapes the original maximal local subgroup,
no nontrivial characteristic subgroup of T₁ is normal in L T₁: T normalizes
such a subgroup, hence the entire original component orbit does, contradicting
uniqueness. The actual Sylow T₁ supplies MS2(a) inside L T₁.

The guard is failure of the original requested normalizer containment. No
normality of a commutator span in the original two-parabolic join is assumed.
Source: Aschbacher--Smith 10.2.5, printed pp.747--748, and C.1.31.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

private theorem uniquenessMS : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- Normalizer escape excludes every nontrivial characteristic subgroup of
the actual half-Sylow that is normalized by the original component. -/
theorem characteristic_halfSylow_eq_bot_of_normalizer_escape
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (C : Subgroup ↥((T : Subgroup G) ⊓ normalizer (L : Set G))) [C.Characteristic]
    (hLC : L ≤ normalizer (C.map ((T : Subgroup G) ⊓ normalizer (L : Set G)).subtype : Set G)) :
    C = ⊥ := by
  by_contra hne
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let W := C.map R.subtype
  have hNW : normalizer (R : Set G) ≤ normalizer (W : Set G) :=
    normalizer_le_normalizer_characteristic_image R C
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (Parabolics.stabilizer_normalized D hn).trans hNW
  have hp : IsPGroup 2 W := ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from
    inf_le_left)).to_subgroup C).map R.subtype
  have hW : W ≠ ⊥ := fun he => hne
    ((C.map_eq_bot_iff_of_injective R.subtype_injective).mp he)
  apply hout
  apply hNW.trans
  apply normalizer_le_of_unique_maximalTwoLocal
    (D.lemma_3_2_3_uniqueness (uniquenessMS D)).2.2 hp hW
  exact sup_le (iSup_conjugates_le_of_le_normalizer L T _ hLC
    (hTW.trans (normalizer (W : Set G)).le_normalizer)) hTW

/-- The literal half-Sylow is Sylow in the original component product. -/
theorem halfSylow_sylow_component_join
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))) := by
  apply (source_nonnormal_stabilizer_sylow D hn).restrict le_sup_right
  apply sup_le
  · exact le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer)
      L.le_normalizer
  · exact le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right

/-- The original Sylow subgroup itself is the proper odd-index subgroup
whose two-core supplies MS2(a). -/
theorem halfSylow_msOddIndexRadical
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ChapterC.MSOddIndexRadical
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := L ⊔ R
  obtain ⟨S,hS⟩ := halfSylow_sylow_component_join D hn
  have he : (S : Subgroup J) = R.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  refine ⟨R.subgroupOf J,lt_top_iff_ne_top.mpr ?_,?_,?_⟩
  · intro ht
    have hJR : J ≤ R := subgroupOf_eq_top.mp ht
    have hp : IsPGroup 2 L := T.isPGroup'.to_le
      ((show L ≤ J from le_sup_left).trans (hJR.trans inf_le_left))
    let := hp.isNilpotent
    exact Chapter1.mem_L_not_isSolvable D.maximal.1 inferInstance
  · rw [← he]
    simpa only [← even_iff_two_dvd,Nat.not_even_iff_odd] using S.not_dvd_index
  · have hp : IsPGroup 2 (R.subgroupOf J) := he ▸ S.isPGroup'
    have hcore : pCore 2 (R.subgroupOf J) = ⊤ :=
      top_unique (le_sSup ⟨inferInstance,hp.of_equiv topEquiv.symm⟩)
    rw [hcore,← MonoidHom.range_eq_map,range_subtype]

/-- Literal MS3 inside L T₁, transported through its actual subgroup
inclusion. The escape is that of N_G(T₁), not of L T₁. -/
theorem halfSylow_msCharacteristic_of_normalizer_escape
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal) :
    ChapterC.MSCharacteristicCondition
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := L ⊔ R
  let e : R.subgroupOf J ≃* R := subgroupOfEquivOfLe le_sup_right
  intro C hC hne hnormal
  let := hC
  let := hnormal
  let W := C.map e.toMonoidHom
  have hW : W.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp hC (MulAut.congr e.symm a) hy,?_⟩
    exact e.apply_symm_apply (a (e y))
  let := hW
  have hmap : W.map R.subtype = (C.map (R.subgroupOf J).subtype).map J.subtype := by
    rw [map_map,map_map]
    rfl
  have hnW : J ≤ normalizer (W.map R.subtype : Set G) := by
    rw [hmap]
    apply le_normalizer_iff.mpr
    intro g hg w hw
    obtain ⟨v,hv,rfl⟩ := hw
    exact mem_map.mpr ⟨⟨g,hg⟩ * v * ⟨g,hg⟩⁻¹,
      hnormal.conj_mem v hv ⟨g,hg⟩,rfl⟩
  have hbot : W = ⊥ := characteristic_halfSylow_eq_bot_of_normalizer_escape D hn hout W
    ((show L ≤ J from le_sup_left).trans hnW)
  exact hne ((C.map_eq_bot_iff_of_injective e.injective).mp hbot)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
