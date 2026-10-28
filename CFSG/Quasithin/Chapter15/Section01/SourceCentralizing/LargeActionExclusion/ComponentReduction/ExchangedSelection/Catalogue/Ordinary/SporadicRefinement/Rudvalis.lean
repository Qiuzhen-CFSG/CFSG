module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.RudvalisSeed
public import Theory.SpecificGroups.Rudvalis.OrdinaryCharacteristic
public import Theory.GroupTheory.FixedElementaryTransport

/-!
# Excluding the ordinary Rudvalis component at the original marker

The sixth lower-central term of the actual Rudvalis Sylow is the marked
eight-group normalized by max4. Completeness of the central quotient and
normality of the original component lift this geometry through every retained
central two-cover. The lifted lower-central term joined with the Sylow center
is characteristic in the original full S and is normalized by the aligned
max4 preimage. Its perfect residual still escapes M_Z, contradicting the
source 14.1.6(3) characteristic-subgroup obstruction.

The argument applies before exchanged selection and retains both source
primes, the original quotient marking, and the complete covering center.
Source: Aschbacher--Smith 15.1.22, printed p.1100; GLS3 Table 5.3r.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem characteristic_equiv_image {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro a x ⟨y,hy,rfl⟩
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy,?_⟩
  exact e.apply_symm_apply (a (e y))

/-- The actual escaping Rudvalis seed normalizes a nontrivial characteristic
subgroup of the original full S, with all central covers retained. -/
theorem PreExclusionSource.rudvalis_escaping_characteristic_seed
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model) :
    ∃ B : Subgroup G, B ≤ d.L ∧ d.SL ≤ B ∧ ¬ B ≤ d.MZ ∧
      (∃ f : B →* Rudvalis.SylowOvergroups.max4,
        Function.Surjective f ∧ IsPGroup 2 f.ker ∧ f.ker ≤ center B) ∧
      ∃ C : Subgroup d.S, C.Characteristic ∧ C ≠ ⊥ ∧
        B ≤ normalizer (C.map d.S.subtype : Set G) := by
  obtain ⟨B,hBL,hSB,_,_,_,hout,hcover,γ,hγP,hγB⟩ :=
    s.rudvalis_escaping_normalizer_alignment (h := h) hG hM hu hL e
  let L := d.L.subgroupOf d.G1
  let el : L ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let : L.Normal := s.rudvalis_normal (h := h) hG hL e
  let : IsQuasisimple L := hL.2
  let ez := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv el
  let : IsSimpleGroup (d.L ⧸ center d.L) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := ez.symm.isSimpleGroup
  let e0 : (L ⧸ center L) ≃* Rudvalis.Model :=
    (QuotientGroup.congr _ _ el (FixedElementary.map_center el)).trans ez
  let q := ez.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
  let q0 := e0.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : q0 = q.comp el.toMonoidHom := by ext x; rfl
  obtain ⟨S,hS⟩ := s.centralizer_sylow
  obtain ⟨P,hP⟩ := S.exists_sylow_map_eq_inf_of_normal L
  have heP : (P : Subgroup L).map el.toMonoidHom = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le d.SL_le_L]
    have he : d.L.subtype.comp el.toMonoidHom = d.G1.subtype.comp L.subtype := rfl
    rw [he,←map_map,hP,Subgroup.map_inf _ _ _ d.G1.subtype_injective,hS]
    exact congrArg (fun A : Subgroup G => d.S ⊓ A)
      (map_subgroupOf_eq_of_le d.L_component.1)
  have hPq : (P : Subgroup L).map q0 =
      Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.localP.map γ.toMonoidHom := by
    rw [hq,←map_map,heP]
    exact hγP
  let B0 := B.subgroupOf d.G1
  have hBG : B ≤ d.G1 := hBL.trans d.L_component.1
  have hB0L : B0 ≤ L := subgroupOf_mono d.G1 hBL
  have heB : (B0.subgroupOf L).map el.toMonoidHom = B.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hBL]
    have he : d.L.subtype.comp el.toMonoidHom = d.G1.subtype.comp L.subtype := rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hB0L,map_subgroupOf_eq_of_le hBG]
  have hBq : (B0.subgroupOf L).map q0 = Rudvalis.SylowOvergroups.max4.map γ.toMonoidHom := by
    rw [hq,←map_map,heB]
    exact hγB
  have hz : IsPGroup 2 (center L) := (s.ordinary hL).center_two.of_equiv (centerCongr el.symm)
  obtain ⟨C,hC,hCne,hBC⟩ := Rudvalis.OrdinaryCharacteristic.exists_full_sylow_characteristic
    L e0 hz S P hP B0 hB0L γ hPq hBq
  let es : (S : Subgroup d.G1) ≃* d.S :=
    ((S : Subgroup d.G1).equivMapOfInjective d.G1.subtype d.G1.subtype_injective).trans
      (MulEquiv.subgroupCongr hS)
  let D := C.map es.toMonoidHom
  let := hC
  have hD : D.Characteristic := characteristic_equiv_image es C
  have hDne : D ≠ ⊥ := fun hh => hCne ((map_eq_bot_iff_of_injective _ es.injective).mp hh)
  have heD : D.map d.S.subtype = (C.map (S : Subgroup d.G1).subtype).map d.G1.subtype := by
    rw [map_map,map_map]
    rfl
  refine ⟨B,hBL,hSB,hout,hcover,D,hD,hDne,?_⟩
  have hm := (map_mono (f:=d.G1.subtype) hBC).trans
    ((C.map (S : Subgroup d.G1).subtype).le_normalizer_map d.G1.subtype)
  rwa [map_subgroupOf_eq_of_le hBG,←heD] at hm

/-- The original Rudvalis component is impossible, using the full-S
characteristic subgroup and the literal source 14.1.6(3) obstruction. -/
theorem PreExclusionSource.not_rudvalis
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model) : False := by
  obtain ⟨B,hBL,hSB,hout,⟨f,hf,hk,_⟩,C,hC,hCne,hBC⟩ :=
    s.rudvalis_escaping_characteristic_seed (h := h) hG hM hu hL e
  let R := solvableResidual B
  let K := R.map B.subtype
  let er : R ≃* K := R.equivMapOfInjective B.subtype B.subtype_injective
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f:=er.toMonoidHom) er.surjective
  let : Group.IsPerfect Rudvalis.SylowOvergroups.max4 := Rudvalis.Multiplier.TwoPrimary.max4_isPerfect
  have hR : R.map f = ⊤ := by
    change (solvableResidual B).map f = ⊤
    rw [map_solvableResidual_eq f hf,solvableResidual_eq_top]
  obtain ⟨Q,hQ⟩ := s.component_sylow.restrict hSB hBL
  have hRS : R ⊔ (Q : Subgroup B) = ⊤ := by
    have hh := congrArg (Subgroup.comap f) hR
    rw [comap_map_eq,comap_top] at hh
    apply top_unique
    rw [←hh]
    exact sup_le_sup_left (hk.le_sylow_of_normal Q) R
  have hBS : K ⊔ d.SL = B := by
    have hh := congrArg (Subgroup.map B.subtype) hRS
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,hQ] at hh
    exact hh
  have hSM : d.SL ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    apply le_inf (d.SL_le_L.trans d.L_component.1)
    apply d.SL_le_S.trans (d.S_le_T.trans ?_)
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hKout : ¬ K ≤ d.MZ := fun hh => hout (hBS ▸ sup_le hh hSM)
  have hKB : K ≤ B := map_subtype_le _
  exact s.perfect_escape_not_normalize_characteristic (h := h) hG hempty hu
    (hKB.trans (hBL.trans d.L_component.1)) hKout C hC hCne (hKB.trans hBC)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
