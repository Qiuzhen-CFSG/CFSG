module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryLinearThreeBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawLinearTwo
public import Theory.SpecificGroups.PSL3.CentralCoverBorelGeometry
public import Theory.SpecificGroups.Classical.EvenRankTwoOddRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal

/-!
# The actual original ordinary PSL₃(4) central-cover exclusion

The original faithful central seed supplies a nontrivial involutory Sylow
fixer on the same component, forcing its two-group center to be elementary.
Native lifting and Borel geometry then give Thompson normalization,
two-perfectness, and the Sylow centralizer comparison on that central cover.
The actual marked Borel equality and original residual intersection contradict
movement on L. No splitting, whole-M generation, global residual premise,
or replacement component is used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem raw_four_cover_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (e : (L ⧸ center L) ≃* Matrix.PSL3Four.PSL) :
    (L.subgroupOf (centralizer (Z1 : Set G))).Normal := by
  let := h.elementary
  obtain ⟨r,hr,ho,hR⟩ := Theory.SpecificGroups.Classical.EvenRankTwoOddRank.linear
    (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F)
  let : Fact r.Prime := ⟨hr⟩
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  let ek := subgroupOfEquivOfLe hLG
  have hZtwo : IsPGroup 2 (center L) := hcenter ▸ pCore_isPGroup
  have hZ' := hZtwo.of_equiv (centerCongr ek.symm)
  obtain ⟨k,hk⟩ := hZ'.exists_card_eq
  have hc : Nat.Coprime r (Nat.card (center (L.subgroupOf (centralizer (Z1 : Set G))))) := by
    rw [hk]
    exact (Nat.coprime_two_right.mpr ho).pow_right k
  let eq : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL :=
    (QuotientGroup.quotientMulEquivOfEq hcenter.symm).trans e
  have hR' : 2 ≤ primeRank r (L.subgroupOf (centralizer (Z1 : Set G))) := by
    rw [primeRank_equiv r ek,
      ←primeRank_quotient_eq_of_isTwoGroup r ho (pCore 2 L) pCore_isPGroup,
      primeRank_equiv r eq]
    exact hR
  exact hL.normal_of_coprime_center_primeRank r hc (by
    have hh := hsq.stronglyQuasithin r hr ho
    omega)

private theorem raw_four_cover_center_frattini
    (T : Sylow 2 G) {M Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    [IsQuasisimple L] (hcenter : center L = pCore 2 L)
    (hnZ : centralInvolutions T ≤ normalizer (L : Set G))
    (hfaith : centralInvolutions T ⊓ centralizer (L : Set G) = ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (e : (L ⧸ center L) ≃* Matrix.PSL3Four.PSL) : frattini (center L) = ⊥ := by
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  let α := L.normalizerMonoidHom ⟨z,hnZ hz⟩
  have ha (x : L) : (α x : G) = z*x*z⁻¹ := rfl
  obtain ⟨P,hP⟩ := hSyl
  have hfix : ∀ x ∈ P, α x = x := by
    intro x hx
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      (centralInvolutions_le_centralizer_sylow T hz x
        ((hP ▸ mem_map_of_mem L.subtype hx).1).1).symm
  have hz2 : z*z=1 := by
    have hh := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
    simpa only [pow_two] using hh.2.1
  have hα2 : α^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (α (α x) : G) = x
    rw [ha,ha]
    calc
      z*(z*(x:G)*z⁻¹)*z⁻¹ = (z*z)*x*(z*z)⁻¹ := by group
      _ = x := by rw [hz2]; simp
  have hαne : α ≠ 1 := by
    intro he
    have hc : z ∈ centralizer (L : Set G) := by
      intro x hx
      have hh := ha (⟨x,hx⟩ : L)
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    exact hzne (mem_bot.mp (hfaith ▸ ⟨hz,hc⟩))
  exact Matrix.PSL3.OrdinaryBorel.four_cover_center_frattini e
    (hcenter ▸ pCore_isPGroup) P α hα2 hαne hfix

private noncomputable def raw_centerQuotientCongr {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) : (X ⧸ center X) ≃* (Y ⧸ center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem raw_four_cover_borel_thompson
    (H S L : Subgroup G) (hLG : L ≤ H) (hSH : S ≤ H)
    (hnormal : (L.subgroupOf H).Normal) [IsQuasisimple L]
    (hSylG : Chapter1.IsSylowIn 2 S H)
    (hZtwo : IsPGroup 2 (center L)) (hFr : frattini (center L) = ⊥)
    (e : (L ⧸ center L) ≃* Matrix.PSL3Four.PSL) :
    let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
    B ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  let : (L.subgroupOf H).Normal := hnormal
  let K := L.subgroupOf H
  let ek : K ≃* L := subgroupOfEquivOfLe hLG
  let eQ := (raw_centerQuotientCongr ek).trans e
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv ek.symm
  have hZK : IsPGroup 2 (center K) := hZtwo.of_equiv (centerCongr ek).symm
  let : Fact (IsPGroup 2 (center L)) := ⟨hZtwo⟩
  let : IsElementaryAbelian 2 (center L) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hFr
  let : IsElementaryAbelian 2 (center K) := IsElementaryAbelian.of_surjective
    (centerCongr ek).symm.toMonoidHom (centerCongr ek).symm.surjective
  have hlift (W : Subgroup Matrix.PSL3Four.PSL) (hw : IsElementaryAbelian 2 W) :
      IsElementaryAbelian 2 (W.comap (Matrix.PSL3Even.ThompsonCentralCover.projection K eQ)) := by
    let := hw
    apply Matrix.PSL3Four.ElementaryParabolic.elementary_comap _
      (Matrix.PSL3Even.ThompsonCentralCover.projection_surjective K eQ)
    · rw [Matrix.PSL3Even.ThompsonCentralCover.projection_ker]
    · intro z hz
      rw [Matrix.PSL3Even.ThompsonCentralCover.projection_ker] at hz
      exact elemPow_eq_one_of_isElementaryAbelian z hz
  obtain ⟨P,hP⟩ := hSylG
  have hP' : (P : Subgroup H) = S.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSH]
  have hPK : ((P : Subgroup H).subgroupOf K).map ek.toMonoidHom = (S ⊓ L).subgroupOf L := by
    ext x
    rw [mem_map_equiv,hP']
    change (x:G) ∈ S ↔ (x:G) ∈ S ⊓ L
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hN := Matrix.PSL3.OrdinaryBorel.cover_normalizer_thompson K eQ hZK hlift
    (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F) P
  have hBN : ((normalizer ((P : Subgroup H).subgroupOf K : Set K)).map K.subtype).map
      H.subtype = B := by
    have hcomp : H.subtype.comp K.subtype = L.subtype.comp ek.toMonoidHom := rfl
    rw [map_map,hcomp,←map_map,map_equiv_normalizer_eq,hPK]
  have hJ : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ S := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
  have hh := (map_mono (f := H.subtype) hN).trans
    (le_normalizer_map (H := elementaryAbelianMaxJ (P : Subgroup H)) H.subtype)
  rwa [hBN,hJ] at hh

private theorem raw_four_cover_borel_twoPerfect
    (S L : Subgroup G) [IsQuasisimple L]
    (hSylL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    (hZtwo : IsPGroup 2 (center L))
    (e : (L ⧸ center L) ≃* Matrix.PSL3Four.PSL) :
    let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
    IsPPerfect 2 B := by
  obtain ⟨P,hP⟩ := hSylL
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hb := Matrix.PSL3.OrdinaryBorel.cover_normalizer_twoPerfect (n := 2) (by decide)
    (by simpa using Matrix.PSL3Four.card_F) e hZtwo P
  have hh := hb.of_surjective (L.subtype.subgroupMap (normalizer (P : Set L)))
    (L.subtype.subgroupMap_surjective _)
  change IsPPerfect 2 ((normalizer ((P : Subgroup L) : Set L)).map L.subtype) at hh
  rw [hP'] at hh
  exact hh

private theorem raw_four_cover_borel_centralizers
    (H S L : Subgroup G) (hLG : L ≤ H) (hSH : S ≤ H)
    (hnormal : (L.subgroupOf H).Normal) [IsQuasisimple L]
    (hSylL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    (e : (L ⧸ center L) ≃* Matrix.PSL3Four.PSL) :
    let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
    S ⊓ centralizer (B : Set G) ≤ S ⊓ centralizer (L : Set G) := by
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  have hSL : S ≤ normalizer (L : Set G) := hSH.trans
    ((normal_subgroupOf_iff_le_normalizer hLG).mp hnormal)
  obtain ⟨P,hP⟩ := hSylL
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hBG : (normalizer (P : Set L)).map L.subtype = B := by
    change (normalizer ((P : Subgroup L) : Set L)).map _ = _
    rw [hP']
  change S ⊓ centralizer (B : Set G) ≤ S ⊓ centralizer (L : Set G)
  rintro x ⟨hxS,hxB⟩
  refine ⟨hxS,?_⟩
  let α := L.normalizerMonoidHom ⟨x,hSL hxS⟩
  have hα : α=1 := Matrix.PSL3.OrdinaryBorel.cover_normalizer_fixer (n := 2) (by decide)
    (by simpa using Matrix.PSL3Four.card_F) e P α (by
      intro y hy
      apply Subtype.ext
      change x*(y:G)*x⁻¹=y
      exact mul_inv_eq_iff_eq_mul.mpr (hxB y (hBG ▸ mem_map_of_mem L.subtype hy)).symm)
  intro y hy
  have hh := congrArg Subtype.val (DFunLike.congr_fun hα (⟨y,hy⟩ : L))
  change x*y*x⁻¹=y at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The actual retained PSL₃(4) two-core quotient is impossible on the
original ordinary component, including nontrivial central two-covers. -/
theorem PreparedChosenModule.raw_ordinary_not_linearThree_four_cover
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hnZ : centralInvolutions T ≤ normalizer (L : Set G))
    (hfaith : centralInvolutions T ⊓ centralizer (L : Set G) = ⊥)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hmove : ⁅L,⁅V,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆⁆ ≠ ⊥)
    : ¬ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 := by
  intro hm
  let := h.elementary
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let R := (pResidual 2 (M ⊓ H : Subgroup G)).map (M ⊓ H).subtype
  let W := ⁅V,R⁆
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  let : IsQuasisimple (L.subgroupOf H) := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  have hZtwo : IsPGroup 2 (center L) := hcenter ▸ pCore_isPGroup
  obtain ⟨F,_,_,hF,⟨ef⟩⟩ := hm
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  let eq : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL := ef.trans (Atlas.fieldEquivPSL 3 eF)
  let e : (L ⧸ center L) ≃* Matrix.PSL3Four.PSL :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans eq
  have hnormal := raw_four_cover_normal hG T h hZ hZne hLG hL hcenter e
  have hFr := raw_four_cover_center_frattini T hM hcenter hnZ hfaith hSylL e
  have hBMZ : B ≤ H ⊓ Mc := by
    have he := h.raw_ordinary_linearThree_borel hG T hempty hM hu hZ hZne hLG hL hcenter
      hnZ hfaith hSylG hSylL hcontrol hbound (n := 2) (by decide)
      (by simpa using Matrix.PSL3Four.card_F) eq
    change (H ⊓ Mc) ⊓ L = B at he
    rw [←he]
    exact inf_le_left
  have hBJ := raw_four_cover_borel_thompson H S L hLG inf_le_right hnormal hSylG hZtwo hFr e
  have hBtwo := raw_four_cover_borel_twoPerfect S L hSylL hZtwo e
  have hfix := raw_four_cover_borel_centralizers H S L hLG inf_le_right hnormal hSylL e
  have hJS := (h.caseI_marked_thompson_control hG T hM hJ hZ).1
  have hNJ := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  have hBM : B ≤ M := by
    change B ≤ normalizer (elementaryAbelianMaxJ S : Set G) at hBJ
    change elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) at hJS
    rw [hJS] at hBJ
    exact hBJ.trans hNJ
  have hBI : B ≤ M ⊓ Mc ⊓ H :=
    le_inf (le_inf hBM (hBMZ.trans inf_le_right)) (hBMZ.trans inf_le_left)
  have hBV : B ≤ centralizer (V : Set G) := by
    have hh := embedded_pResidual_mono 2 hBI
    rw [(pResidual_eq_top_iff 2 B).mpr hBtwo,←MonoidHom.range_eq_map,range_subtype,hI] at hh
    exact hh.trans ((map_subtype_le _).trans inf_le_right)
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((map_subtype_le _).trans inf_le_left).trans h.normalized)
  have hWS : W ≤ S := hWV.trans (le_inf hVT
    (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left))))
  have hWB := hWV.trans (le_centralizer_iff.mp hBV)
  have hWL : W ≤ centralizer (L : Set G) := (le_inf hWS hWB).trans
    (hfix.trans inf_le_right)
  apply hmove
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hWL

end CFSG.Quasithin.Chapter15.Section01
