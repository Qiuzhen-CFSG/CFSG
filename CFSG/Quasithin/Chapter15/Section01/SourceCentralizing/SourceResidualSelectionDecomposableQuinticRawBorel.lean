module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineSolvableControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.OrbitBorel

/-!
# The actual rank-one Borel from raw marked-local controls

The original Sylow Borel's orbit has characteristic two and odd quotient.
The literal two-residual of the marked local normalizes the component and
its Borel. Its full normalizer bound therefore controls the orbit inside
the marked local. No Case-I generation record is needed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem raw_borel_eq (S K : Subgroup G) :
    K ⊓ normalizer (S ⊓ K : Set G) =
      (normalizer ((S ⊓ K).subgroupOf K : Set K)).map K.subtype := by
  rw [←subgroupOf_normalizer_eq (show S ⊓ K ≤ K from inf_le_right),subgroupOf_map_subtype]
  exact inf_comm _ _

private theorem raw_borel_bound (H Mc S K : Subgroup G)
    (hSM : S ≤ H ⊓ Mc) (hlocal : K ∈ Chapter1.L G S)
    (hout : ¬ K ≤ H ⊓ Mc) {n : ℕ} (hb : IsL2EvenBlock K n) :
    (H ⊓ Mc) ⊓ K ≤ (normalizer ((S ⊓ K).subgroupOf K : Set K)).map K.subtype := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hlocal
  have hPK : (P : Subgroup K) = (S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨_,_,F,_,_,hF,_,r,⟨m⟩,_⟩ := hb
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup K) := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hPA : (P : Subgroup K) ≤ (H ⊓ Mc).subgroupOf K := by
    intro x hx
    exact hSM ((hP ▸ mem_map_of_mem K.subtype hx).1)
  have hA : (H ⊓ Mc).subgroupOf K ≠ ⊤ := fun he => hout (subgroupOf_eq_top.mp he)
  have hn := Matrix.SpecialLinearGroup.proper_overgroup_le_sylow_normalizer_of_two_kernel
    q hq P hk ((H ⊓ Mc).subgroupOf K) hPA hA
  intro x hx
  exact ⟨⟨x,hx.2⟩,hPK ▸ hn hx.1,rfl⟩

private theorem raw_borel_core (H Mc S K : Subgroup G)
    (hSM : S ≤ H ⊓ Mc) (hS : IsPGroup 2 S) (hlocal : K ∈ Chapter1.L G S)
    (hout : ¬ K ≤ H ⊓ Mc) {n : ℕ} (hb : IsL2EvenBlock K n) :
    ((H ⊓ Mc) ⊓ K).pCoreIn 2 = S ⊓ K := by
  have hPA : S ⊓ K ≤ (H ⊓ Mc) ⊓ K := inf_le_inf_right K (hSM)
  have hn : (H ⊓ Mc) ⊓ K ≤ normalizer (S ⊓ K : Set G) := by
    have hN := ((S ⊓ K).subgroupOf K).le_normalizer_map K.subtype
    rw [map_subgroupOf_eq_of_le inf_le_right] at hN
    exact (raw_borel_bound H Mc S K hSM hlocal hout hb).trans hN
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hlocal
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show (H ⊓ Mc) ⊓ K ≤ K from inf_le_right) (hP ▸ hPA)
  exact le_antisymm ((pCoreIn_le_sylow _ Q).trans_eq (hQ.trans hP))
    (le_pCoreIn_of_normalizes (hS.to_le inf_le_left) hPA hn)

private theorem raw_borel_normalized (H Mc S K : Subgroup G)
    (hSM : S ≤ H ⊓ Mc) (hS : IsPGroup 2 S) (hlocal : K ∈ Chapter1.L G S)
    (hout : ¬ K ≤ H ⊓ Mc) {n : ℕ} (hb : IsL2EvenBlock K n) :
    (H ⊓ Mc) ⊓ normalizer (K : Set G) ≤
      normalizer ((K ⊓ normalizer (S ⊓ K : Set G) : Subgroup G) : Set G) := by
  rw [raw_borel_eq]

  have hnA : (H ⊓ Mc) ⊓ normalizer (K : Set G) ≤ normalizer ((H ⊓ Mc) ⊓ K : Set G) :=
    (le_inf (inf_le_left.trans (H ⊓ Mc).le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  have hnP : (H ⊓ Mc) ⊓ normalizer (K : Set G) ≤ normalizer (S ⊓ K : Set G) := by
    change (H ⊓ Mc) ⊓ normalizer (K : Set G) ≤ normalizer ((S ⊓ K : Subgroup G) : Set G)
    rw [←raw_borel_core H Mc S K hSM hS hlocal hout hb]
    exact hnA.trans (normalizer_le_normalizer_characteristic_image ((H ⊓ Mc) ⊓ K)
      (pCore 2 ((H ⊓ Mc) ⊓ K : Subgroup G)))
  have hB : (normalizer ((S ⊓ K).subgroupOf K : Set K)).map K.subtype =
      K ⊓ normalizer (S ⊓ K : Set G) := by
    rw [←subgroupOf_normalizer_eq (show S ⊓ K ≤ K from inf_le_right)]
    rw [subgroupOf_map_subtype]
    exact inf_comm _ _
  rw [hB]
  exact (le_inf inf_le_right (hnP.trans (normalizer (S ⊓ K : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

private theorem raw_orbit_structure (S K : Subgroup G)
    (hlocal : K ∈ Chapter1.L G S) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hb : IsShort K) :
    let B := conjugateSpanBy (K ⊓ normalizer (S ⊓ K : Set G)) S
    generalizedFitting B = pCore 2 B ∧
      (∃ P : Sylow 2 B, (P : Subgroup B) = pCore 2 B) ∧
      Odd (Nat.card (B ⧸ pCore 2 B)) := by
  let H := K ⊔ S
  let K0 := K.subgroupOf H
  let eK : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  obtain ⟨P,hP⟩ := hlocal.2.1
  have hK0 : IsBlock K0 := ⟨inferInstance,hb.of_mulEquiv eK.symm,hlocal.1.subnormal⟩
  let := hq
  have hq0 : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).symm
  let B := conjugateSpanBy (K0 ⊓ normalizer (((P : Subgroup H) ⊓ K0 : Subgroup H) : Set H)) (P : Subgroup H)
  have hB : B.map H.subtype = (conjugateSpanBy (K ⊓ normalizer (S ⊓ K : Set G)) S) := by
    rw [map_conjugateSpanBy,map_relative_sylowNormalizer _ _ _ H.subtype_injective,hP,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)]
    rfl
  let e : B ≃* (conjugateSpanBy (K ⊓ normalizer (S ⊓ K : Set G)) S) :=
    (equivMapOfInjective B H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hB)
  obtain ⟨hf,⟨R,hR⟩,ho⟩ := hK0.orbit_borel_structure P hq0
  have hf' : generalizedFitting ((conjugateSpanBy (K ⊓ normalizer (S ⊓ K : Set G)) S)) = pCore 2 ((conjugateSpanBy (K ⊓ normalizer (S ⊓ K : Set G)) S)) := by
    rw [←map_generalizedFitting_equiv e,←pCore_map_iso 2 e,hf]
  refine ⟨hf',⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩,?_⟩
  · change (R : Subgroup B).map e.toMonoidHom = _
    rw [hR,pCore_map_iso]
  · rwa [←Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]

private theorem raw_orbit_normalized (H Mc S K : Subgroup G)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hSM : S ≤ H ⊓ Mc) (hS : IsPGroup 2 S)
    (hSyl : Chapter1.IsSylowIn 2 S H)
    (hKH : K ≤ H) (hlocal : K ∈ Chapter1.L G S)
    (hcomp : (K.subgroupOf H).IsCComponent)
    (hout : ¬ K ≤ H ⊓ Mc) {n : ℕ} (hb : IsL2EvenBlock K n) :
    H ⊓ Mc ≤ normalizer (conjugateSpanBy (K ⊓ normalizer (S ⊓ K : Set G)) S : Set G) := by
  let R := (pResidual 2 (H ⊓ Mc : Subgroup G)).map (H ⊓ Mc).subtype
  have hRM : R ≤ (H ⊓ Mc) := map_subtype_le _
  have hRG : R ≤ H := hRM.trans inf_le_left
  let e := (subgroupOfEquivOfLe hRG).symm
  have hp : IsPPerfect 2 (R.subgroupOf H) :=
    (isPPerfect_embedded_pResidual 2 (H ⊓ Mc : Subgroup G)).of_surjective e.toMonoidHom e.surjective
  have hquot : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hH.isKGroup.quotient (pCore 2 H)⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 H) pCore_isPGroup).trans
      (hH.stronglyQuasithin q hq ho)
  have hn0 := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hquot hcomp hp
  have hnK := (map_mono (f := H.subtype) hn0).trans
    ((K.subgroupOf H).le_normalizer_map H.subtype)
  rw [map_subgroupOf_eq_of_le hRG,map_subgroupOf_eq_of_le hKH] at hnK
  have hnB : R ≤ normalizer ((K ⊓ normalizer (S ⊓ K : Set G) : Subgroup G) : Set G) :=
    (le_inf hRM hnK).trans (raw_borel_normalized H Mc S K hSM hS hlocal hout hb)
  have hnR : (H ⊓ Mc) ≤ normalizer (R : Set G) := (H ⊓ Mc).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (H ⊓ Mc) (pResidual 2 (H ⊓ Mc : Subgroup G)))
  obtain ⟨P,hP⟩ := hSyl
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show (H ⊓ Mc) ≤ H from inf_le_left) (hP ▸ hSM)
  have he : R ⊔ S = (H ⊓ Mc) := by
    have hh := congrArg (map (H ⊓ Mc).subtype) (pResidual_sup_sylow_eq_top Q)
    simpa only [Subgroup.map_sup,hQ,hP,←MonoidHom.range_eq_map,range_subtype] using hh
  rw [←he]
  exact sup_le (TwoOrbitSpan.normalizes_span _ _ R hnB (hSM.trans hnR))
    (le_normalizer_conjugateSpanBy _ _)

private theorem raw_solvable_control (H Mc S K : Subgroup G)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hSM : S ≤ H ⊓ Mc) (hSyl : Chapter1.IsSylowIn 2 S H)
    (hcontrol : ((H ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (H ⊓ Mc : Subgroup G)).map (H ⊓ Mc).subtype : Set G) ≤ Mc)
    (hK : K ≤ H) (hn : H ⊓ Mc ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : Odd (Nat.card (K ⧸ pCore 2 K))) : K ≤ H ⊓ Mc := by
  let N := (H ⊓ Mc).subgroupOf H
  let B := K.subgroupOf H
  let e : B ≃* K := subgroupOfEquivOfLe hK
  obtain ⟨P,hP⟩ := hSyl
  have hPN : (P : Subgroup H) ≤ N := by
    intro x hx
    exact hSM (hP ▸ mem_map_of_mem H.subtype hx)
  have hnB : N ≤ normalizer (B : Set H) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hn hx) b
  have hfB : generalizedFitting B = pCore 2 B := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hf]
  have hoB : Odd (Nat.card (B ⧸ pCore 2 B)) := by
    rwa [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
  have hc : (N.pCoreIn 2).characteristicNormalizerClosure ≤ N := by
    rw [show N = (H ⊓ Mc).subgroupOf H from rfl,pCoreIn_subgroupOf 2 (H ⊓ Mc) H inf_le_left]
    exact caseI_intrinsic_characteristic_control H Mc ((H ⊓ Mc).pCoreIn 2)
      ((pCoreIn_le 2 (H ⊓ Mc)).trans inf_le_left) hcontrol
  have hY : ((pResidual 2 N).map N.subtype).map H.subtype =
      (pResidual 2 (H ⊓ Mc : Subgroup G)).map (H ⊓ Mc).subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le (show (H ⊓ Mc) ≤ H from inf_le_left)]
  have hr : normalizer ((pResidual 2 N).map N.subtype : Set H) ≤ N := by
    intro x hx
    refine ⟨x.property,hbound ?_⟩
    have hm := le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx)
    rwa [hY] at hm
  have hle := CaseIComponentData.ConstrainedSolvable.controlled_of_odd_quotient
    hH P N B hPN hnB hfB hoB hc hr
  intro k hk
  exact hle (show (⟨k,hK hk⟩ : H) ∈ B from hk)

/-- The literal Sylow Borel of an outside natural block lies in the marked
local from its actual core and residual-normalizer controls. -/
theorem raw_component_borel_le_marked (H Mc S L : Subgroup G)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hSM : S ≤ H ⊓ Mc) (hS : IsPGroup 2 S)
    (hSyl : Chapter1.IsSylowIn 2 S H)
    (hL : L ∈ Chapter1.cComponentsIn H) (hlocal : L ∈ Chapter1.L G S)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hout : ¬L ≤ H ⊓ Mc)
    (hcontrol : ((H ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (H ⊓ Mc : Subgroup G)).map (H ⊓ Mc).subtype : Set G) ≤ Mc)
    {n : ℕ} (hb : IsL2EvenBlock L n) :
    (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype ≤ H ⊓ Mc := by
  let B := conjugateSpanBy (L ⊓ normalizer (S ⊓ L : Set G)) S
  have hBH : B ≤ H := conjugateSpanBy_le (inf_le_left.trans hL.1)
    ((hSM.trans inf_le_left).trans H.le_normalizer)
  have hn := raw_orbit_normalized H Mc S L hH hSM hS hSyl hL.1 hlocal hL.2 hout hb
  obtain ⟨hf,_,ho⟩ := raw_orbit_structure S L hlocal hq hb.2.1
  have hBM := raw_solvable_control H Mc S B hH hSM hSyl hcontrol hbound hBH hn hf ho
  rw [←raw_borel_eq]
  exact (le_conjugateSpanBy _ _).trans hBM

end CFSG.Quasithin.Chapter15.Section01
