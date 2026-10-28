module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryLinearThreeBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawLinearTwo
public import Theory.SpecificGroups.PSL3.HigherFieldBorelGeometry

/-!
# Original ordinary higher-field linear-three exclusion

The actual component is normal by its odd rank and the ambient quasithin
bound. Its literal Borel is two-perfect, normalizes the original Thompson
subgroup, and has the required Sylow centralizer comparison. The independently
proved marked Borel equality and original residual-intersection identity
then contradict movement on this same component, without M-generation or
an earlier residual-normalization premise.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem raw_linear_three_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* PSL(3,F)) : (L.subgroupOf (centralizer (Z1 : Set G))).Normal := by
  let := h.elementary
  obtain ⟨r,hr,ho,hR⟩ := Theory.SpecificGroups.Classical.EvenRankTwoOddRank.linear hn hF
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
  have hR' : 2 ≤ primeRank r (L.subgroupOf (centralizer (Z1 : Set G))) := by
    rw [primeRank_equiv r ek,primeRank_equiv r e]
    exact hR
  exact hL.normal_of_coprime_center_primeRank r hc (by
    have hh := hsq.stronglyQuasithin r hr ho
    omega)

private theorem raw_linear_three_borel_thompson
    (H S L : Subgroup G) (hLG : L ≤ H) (hSH : S ≤ H)
    (hnormal : (L.subgroupOf H).Normal)
    (hSylG : Chapter1.IsSylowIn 2 S H)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* PSL(3,F)) :
    let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
    B ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype

  let : (L.subgroupOf H).Normal := hnormal
  let K := L.subgroupOf H
  let ek : K ≃* L := subgroupOfEquivOfLe hLG
  obtain ⟨P0,hS⟩ := hSylG
  have hS' : (P0 : Subgroup H) = S.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hSH]
  have hPK : ((P0 : Subgroup H).subgroupOf K).map ek.toMonoidHom = (S ⊓ L).subgroupOf L := by
    ext x
    rw [mem_map_equiv,hS']
    change (x:G) ∈ S ↔ (x:G) ∈ S ⊓ L
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hN := Matrix.PSL3.OrdinaryBorel.normalizer_thompson K (ek.trans e) hn hF P0
  have hBN : ((normalizer ((P0 : Subgroup H).subgroupOf K : Set K)).map K.subtype).map
      H.subtype = B := by
    have hcomp : H.subtype.comp K.subtype = L.subtype.comp ek.toMonoidHom := rfl
    rw [map_map,hcomp,← map_map,map_equiv_normalizer_eq,hPK]
  have hJ : (elementaryAbelianMaxJ (P0 : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ S := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hS]
  have hh := (map_mono (f:=H.subtype) hN).trans
    (le_normalizer_map (H := elementaryAbelianMaxJ (P0 : Subgroup H)) H.subtype)
  rwa [hBN,hJ] at hh


private theorem raw_linear_three_borel_twoPerfect
    (S L : Subgroup G)
    (hSylL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* PSL(3,F)) :
    let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
    IsPPerfect 2 B := by
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype

  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := hSylL
  have hP' : (P : Subgroup L)=(S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  let Q := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let B0 := normalizer (P : Set L)
  have hBQ : B0.map e.toMonoidHom = normalizer (Q : Set PSL(3,F)) := by
    exact map_equiv_normalizer_eq (P : Subgroup L) e
  let eB : B0 ≃* normalizer (Q : Set PSL(3,F)) :=
    (e.subgroupMap B0).trans (MulEquiv.subgroupCongr hBQ)
  have hb : IsPPerfect 2 B0 := (Matrix.PSL3.OrdinaryBorel.normalizer_twoPerfect hn hF Q).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  have hBG : B0.map L.subtype = B := by
    change (normalizer ((P : Subgroup L) : Set L)).map _ = _
    rw [hP']
  change IsPPerfect 2 B
  rw [← hBG]
  exact hb.of_surjective (L.subtype.subgroupMap B0) (L.subtype.subgroupMap_surjective B0)


private theorem raw_linear_three_borel_centralizers
    (H S L : Subgroup G) (hLG : L ≤ H) (hSH : S ≤ H)
    (hnormal : (L.subgroupOf H).Normal)
    (hSylL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* PSL(3,F)) :
    let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
    S ⊓ centralizer (B : Set G) ≤ S ⊓ centralizer (L : Set G) := by
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype

  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hSL : S ≤ normalizer (L : Set G) := hSH.trans
    ((normal_subgroupOf_iff_le_normalizer hLG).mp hnormal)
  obtain ⟨P,hP⟩ := hSylL
  have hP' : (P : Subgroup L)=(S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  let Q := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let B0 := normalizer (P : Set L)
  have hBQ : B0.map e.toMonoidHom = normalizer (Q : Set PSL(3,F)) := by
    exact map_equiv_normalizer_eq (P : Subgroup L) e
  have hBG : B0.map L.subtype = B := by
    change (normalizer ((P : Subgroup L) : Set L)).map _ = _
    rw [hP']
  change S ⊓ centralizer (B : Set G) ≤ S ⊓ centralizer (L : Set G)
  rintro x ⟨hxS,hxB⟩
  refine ⟨hxS,?_⟩
  let α := L.normalizerMonoidHom ⟨x,hSL hxS⟩
  have hfix : ∀ y ∈ normalizer (Q : Set PSL(3,F)), (MulAut.congr e α) y = y := by
    intro y hy
    rw [← hBQ] at hy
    obtain ⟨l,hl,rfl⟩ := hy
    change e (α (e.symm (e l))) = e l
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change x * (l:G) * x⁻¹ = l
    exact mul_inv_eq_iff_eq_mul.mpr (hxB l (hBG ▸ mem_map_of_mem L.subtype hl)).symm
  have hα : α=1 := (MulAut.congr e).injective
    ((Matrix.PSL3.OrdinaryBorel.normalizer_fixer hn hF Q _ hfix).trans (map_one _).symm)
  intro y hy
  have hh := congrArg Subtype.val (DFunLike.congr_fun hα (⟨y,hy⟩:L))
  change x*y*x⁻¹=y at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm


/-- The same original ordinary component cannot be a higher-field PSL₃.
All local controls are literal outputs of the raw source construction. -/
theorem PreparedChosenModule.raw_ordinary_not_linearThree
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
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* PSL(3,F)) : False := by
  let := h.elementary
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let R := (pResidual 2 (M ⊓ H : Subgroup G)).map (M ⊓ H).subtype
  let W := ⁅V,R⁆
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  have hnormal := raw_linear_three_normal hG T h hZ hZne hLG hL hcenter hn hF e
  have hz : center L = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro z hz
    have hh : e z ∈ center PSL(3,F) := (centerCongr e ⟨z,hz⟩).property
    rw [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F),mem_bot] at hh
    exact e.injective (hh.trans (map_one e).symm)
  have hcore : pCore 2 L = ⊥ := hcenter.symm.trans hz
  let eq := ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans e
  have hBMZ : B ≤ H ⊓ Mc := by
    have he := h.raw_ordinary_linearThree_borel hG T hempty hM hu hZ hZne hLG hL hcenter
      hnZ hfaith hSylG hSylL hcontrol hbound hn hF eq
    change (H ⊓ Mc) ⊓ L = B at he
    exact he.ge.trans inf_le_left
  have hBJ := raw_linear_three_borel_thompson H S L hLG inf_le_right hnormal hSylG hn hF e
  have hBtwo := raw_linear_three_borel_twoPerfect S L hSylL hn hF e
  have hfix := raw_linear_three_borel_centralizers H S L hLG inf_le_right hnormal hSylL hn hF e
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
