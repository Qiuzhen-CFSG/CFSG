module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinarySolvableBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawLinearTwo
public import Theory.SpecificGroups.SymplecticFour.HigherFieldBorelGeometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.SylowOvergroupNormalizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Solvable

/-!
# Original ordinary higher-field symplectic exclusion

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

private theorem raw_symplectic_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    {F : Type} [Field F] [Finite F] {n : ℕ} (_hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : (L.subgroupOf (centralizer (Z1 : Set G))).Normal := by
  let := h.elementary
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let r := 3
  have hr : r.Prime := by decide
  have ho : Odd r := by decide
  have hR : 2 ≤ primeRank r (Theory.SpecificGroups.SymplecticFour.Sp F) := by
    rw [primeRank_equiv r Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv]
    exact Theory.SpecificGroups.Classical.EvenRankTwoOddRank.symplectic
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

private theorem raw_symplectic_borel_thompson
    (H S L : Subgroup G) (hLG : L ≤ H) (hSH : S ≤ H)
    (hnormal : (L.subgroupOf H).Normal)
    (hSylG : Chapter1.IsSylowIn 2 S H)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
    B ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype

  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
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
  have hN := Theory.SpecificGroups.SymplecticFour.OrdinaryBorel.normalizer_thompson K (ek.trans e) hn hF P0
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


private theorem raw_symplectic_borel_twoPerfect
    (S L : Subgroup G)
    (hSylL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
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
  have hBQ : B0.map e.toMonoidHom = normalizer (Q : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) := by
    exact map_equiv_normalizer_eq (P : Subgroup L) e
  let eB : B0 ≃* normalizer (Q : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) :=
    (e.subgroupMap B0).trans (MulEquiv.subgroupCongr hBQ)
  have hb : IsPPerfect 2 B0 := (Theory.SpecificGroups.SymplecticFour.OrdinaryBorel.normalizer_twoPerfect hn hF Q).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  have hBG : B0.map L.subtype = B := by
    change (normalizer ((P : Subgroup L) : Set L)).map _ = _
    rw [hP']
  change IsPPerfect 2 B
  rw [← hBG]
  exact hb.of_surjective (L.subtype.subgroupMap B0) (L.subtype.subgroupMap_surjective B0)


private theorem raw_symplectic_borel_centralizers
    (H S L : Subgroup G) (hLG : L ≤ H) (hSH : S ≤ H)
    (hnormal : (L.subgroupOf H).Normal)
    (hSylL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
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
  have hBQ : B0.map e.toMonoidHom = normalizer (Q : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) := by
    exact map_equiv_normalizer_eq (P : Subgroup L) e
  have hBG : B0.map L.subtype = B := by
    change (normalizer ((P : Subgroup L) : Set L)).map _ = _
    rw [hP']
  change S ⊓ centralizer (B : Set G) ≤ S ⊓ centralizer (L : Set G)
  rintro x ⟨hxS,hxB⟩
  refine ⟨hxS,?_⟩
  let α := L.normalizerMonoidHom ⟨x,hSL hxS⟩
  have hfix : ∀ y ∈ normalizer (Q : Set (Theory.SpecificGroups.SymplecticFour.Sp F)), (MulAut.congr e α) y = y := by
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
    ((Theory.SpecificGroups.SymplecticFour.OrdinaryBorel.normalizer_fixer hn hF Q _ hfix).trans (map_one _).symm)
  intro y hy
  have hh := congrArg Subtype.val (DFunLike.congr_fun hα (⟨y,hy⟩:L))
  change x*y*x⁻¹=y at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm


private theorem raw_symplectic_nonsolvable_borel
    (H MZ S L : Subgroup G) (hLG : L ≤ H) (hMZH : MZ ≤ H) (hSM : S ≤ MZ)
    (hnormal : (L.subgroupOf H).Normal) (hout : ¬L ≤ MZ)
    (hSylL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    (hcoreN : H ⊓ normalizer (MZ.pCoreIn 2 : Set G) = MZ)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hns : ¬Group.IsSolvable (MZ ⊓ L : Subgroup G)) :
    (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype ≤ MZ := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let K := L.subgroupOf H
  let N := MZ.subgroupOf H
  let : K.Normal := hnormal
  let eK : K ≃* L := subgroupOfEquivOfLe hLG
  let e' := e.symm.trans eK.symm
  let f := K.subtype.comp e'.toMonoidHom
  obtain ⟨P,hP⟩ := hSylL
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hQN : (Q : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)).map f ≤ N := by
    rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
    have hm := hSM ((hP ▸ mem_map_of_mem L.subtype hz).1)
    change (e.symm (e z) : G) ∈ MZ
    rwa [e.symm_apply_apply]
  have hproper : N.comap f ≠ ⊤ := by
    intro ht
    apply hout
    intro x hx
    have hh : e ⟨x,hx⟩ ∈ N.comap f := ht ▸ mem_top _
    change (e.symm (e ⟨x,hx⟩) : G) ∈ MZ at hh
    change x ∈ MZ
    rw [e.symm_apply_apply] at hh
    exact hh
  have hns' : ¬ Group.IsSolvable (N.comap f) := by
    intro hs
    let := hs
    let j : (MZ ⊓ L : Subgroup G) →* N.comap f := {
      toFun x := ⟨e ⟨x,x.property.2⟩,by
        change (e.symm (e ⟨x,x.property.2⟩) : G) ∈ MZ
        rw [e.symm_apply_apply]
        exact x.property.1⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' x y := by
        apply Subtype.ext
        exact map_mul e ⟨x,x.property.2⟩ ⟨y,y.property.2⟩ }
    apply hns
    apply Group.isSolvable_of_isSolvable_injective (f := j)
    intro x y hxy
    exact Subtype.ext (congrArg (fun x : L => (x : G))
      (e.injective (congrArg Subtype.val hxy)))
  have hcore : normalizer (N.pCoreIn 2 : Set H) ≤ N := by
    rw [pCoreIn_subgroupOf 2 MZ H (show MZ ≤ H from hMZH)]
    intro x hx
    have hm := le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx)
    change (x : G) ∈ normalizer (((MZ.pCoreIn 2).subgroupOf H).map H.subtype : Set G) at hm
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 MZ).trans hMZH)] at hm
    change (x : G) ∈ MZ
    rw [←hcoreN]
    exact ⟨x.property,hm⟩
  have hb := Theory.SpecificGroups.SymplecticFour.nonsolvable_local_borel_le
    hF hn K N e' Q hQN hproper hns' hcore
  rintro x ⟨y,hy,rfl⟩
  have hQ : e y ∈ normalizer (Q : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) := by
    change e y ∈ normalizer ((P : Subgroup L).map e.toMonoidHom : Set _)
    rw [←map_equiv_normalizer_eq]
    apply mem_map_of_mem
    rwa [hP']
  have hm := hb (mem_map_of_mem f hQ)
  change (e.symm (e y) : G) ∈ MZ at hm
  rwa [e.symm_apply_apply] at hm

/-- The same original ordinary component cannot be a higher-field symplectic group.
All local controls are literal outputs of the raw source construction. -/
theorem PreparedChosenModule.raw_ordinary_not_symplectic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hcoreN : centralizer (Z1 : Set G) ⊓
      normalizer ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 : Set G) =
        centralizer (Z1 : Set G) ⊓ Mc)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hmove : ⁅L,⁅V,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆⁆ ≠ ⊥)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : False := by
  let := h.elementary
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let R := (pResidual 2 (M ⊓ H : Subgroup G)).map (M ⊓ H).subtype
  let W := ⁅V,R⁆
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  have hnormal := raw_symplectic_normal hG T h hZ hZne hLG hL hcenter hn hF e
  have hSM : S ≤ H ⊓ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨hx.2,hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz x hx.1).symm)⟩
  have hBMZ : B ≤ H ⊓ Mc := by
    by_cases hsol : Group.IsSolvable ((H ⊓ Mc) ⊓ L : Subgroup G)
    · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      have hlarge : 2 < Nat.card F := by
        rw [hF]
        exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
      have hc : SolvableSylowControl 2 L := SolvableSylowControl.of_equiv e
        (Theory.SpecificGroups.SymplecticFour.solvable_overgroups_of_orthogonal_root_orbits
          hF hn (fun A hA hUA =>
            Theory.SpecificGroups.SymplecticFour.solvable_unipotent_point_orbit_orthogonal
              hlarge A hA hUA))
      have hB : HasCharacteristicTwo B := by
        obtain ⟨P,hP⟩ := hSylL
        have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
          apply map_injective L.subtype_injective
          rw [hP,map_subgroupOf_eq_of_le inf_le_right]
        let B0 := normalizer (P : Set L)
        have hb : HasCharacteristicTwo B0 := by
          apply e.toMonoidHom.centralizer_pCore_subgroup_of_image
            (IsPGroup.ker_isPGroup_of_injective e.injective)
          rw [P.normalizer_map_surjective e.toMonoidHom e.surjective]
          exact (Theory.Quasithin.centralizer_pCore_le_iff 2
            (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.sylowNormalizerEquiv hF (by omega)
              (P.mapSurjective e.surjective))).mpr
            (Theory.SpecificGroups.SymplecticFour.borel_selfCentralizing_core hF hn)
        have he : B0.map L.subtype = B := by
          change (normalizer ((P : Subgroup L) : Set L)).map _ = _
          rw [hP']
        exact hb.of_equiv ((B0.equivMapOfInjective L.subtype L.subtype_injective).trans
          (MulEquiv.subgroupCongr he))
      have he := raw_ordinary_solvable_borel_eq H Mc S L
        (caseI_centralizer_sqtk hG Z1 hZne
          ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left)))
        hSM (T.isPGroup'.to_le inf_le_left) hSylG hLG hL hSylL hcontrol hbound hsol hc hB
      exact he.ge.trans inf_le_left
    · exact raw_symplectic_nonsolvable_borel H (H ⊓ Mc) S L hLG inf_le_left hSM
        hnormal hout hSylL hcoreN hn hF e hsol
  have hBJ := raw_symplectic_borel_thompson H S L hLG inf_le_right hnormal hSylG hn hF e
  have hBtwo := raw_symplectic_borel_twoPerfect S L hSylL hn hF e
  have hfix := raw_symplectic_borel_centralizers H S L hLG inf_le_right hnormal hSylL hn hF e
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
