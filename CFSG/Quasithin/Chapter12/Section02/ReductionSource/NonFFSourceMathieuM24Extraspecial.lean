module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24FixedCoset
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetCocycle
public import Theory.GroupTheory.DihedralCentralProductFourSix
public import Theory.GroupTheory.Commutator.PerfectClassTwoAction
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The original marked Mathieu centralizer core

A displacement cocycle detects any residual-fixed coset of the full LT core.
The native sextet calculation makes this cocycle principal; the trivial Sylow
centralizer then places its representative in the original cocode module.
Combined with the full-core fixed-coset bound, this proves that the center of
every subgroup between the original closure and the centralizer core is the
original involution line. The closure therefore equals the centralizer core,
and its elementary seven-space identifies its extraspecial plus type.

Finally, the perfect residual excludes the small alternative in its irreducible
core interval. Subgroup-product orders then give EV = O₂(L_z), retaining the
full LT core until the cardinality comparison. Together with the earlier
module intersection, these are all clauses of 8.2.12 for the marked M24 branch.

Source: Aschbacher–Smith 8.2.12(1–3), printed p.722, refs/quasithin.pdf.
The whole-cocode marking remains an explicit earlier-source input. Its
construction, the other Mathieu branches, the full centralizer quotient in
8.2.13 and ambient J4 recognition remain with qt-d-1222-nonff-mathieu.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

theorem sourceOrbit_m24_centralizer_residual_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (localResidual L z : Set G) ≤ D.sourceOrbit := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨hcomm,_,hcore,_,_,_,hTC,_⟩ :=
    D.sourceOrbit_m24_cocode_block_structure h hmany hV hq hnon a E hE
  let q := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have hsur : Function.Surjective q := a.surjective.comp
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq))
  have hk : q.ker = pCore 2 L := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    exact D.sourceOrbit_largeMathieu_component_kernel h.toHypothesis1221 (.inr hq)
  have hker : q.ker ≤ D.sourceOrbit.subgroupOf L := by
    rw [hk,hcore]
    intro l hl
    exact mem_map_of_mem L.subtype hl
  obtain ⟨S,hS⟩ := D.sourceOrbit_m24_central_sextet h hmany hV hq hnon a E hE z hz hne
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow _ (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right))
  intro d hd
  obtain ⟨w,hw,hwc⟩ := MathieuSextet.residual_fixed_coset D.sourceOrbit L
    D.sourceOrbit_component_normalizes q hsur (hk ▸ pCore_isPGroup) hker E
    (fun l w => hE (D.mathieuComponentAutomizer l) _) z S hS d
    (fun l hl => by rw [←hcomm,commutator_comm]; exact commutator_mem_commutator hl hd.1)
    ((show Q ≤ centralizer (D.sourceOrbit : Set G) from hV ▸ D.core_centralizes) hd.1) hd.2
  have he : w*d=1 := mem_bot.mp (hTC ▸
    ⟨(T : Subgroup G).mul_mem (D.sourceOrbit_weakClosure_setup.le_sylow hw) (hQT hd.1),hwc⟩)
  have hed : d = w⁻¹ := by simpa only [inv_mul_cancel_left,mul_one] using congrArg (fun x => w⁻¹*x) he
  exact hed ▸ D.sourceOrbit.inv_mem hw

theorem sourceOrbit_m24_centralizer_centers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (Y : Subgroup G)
    (hEY : (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype ≤ Y)
    (hYC : Y ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2) :
    Y ⊓ centralizer (Y : Set G) = zpowers (z : G) := by
  obtain ⟨_,hcenter,hfix⟩ := D.sourceOrbit_m24_centralizer_intersections_mod_centers
    h hmany hV hq hnon a E hE z hz hne Y hEY hYC
  have hcap := (D.sourceOrbit_m24_centralizer_module_core_intersections h hmany hV hq hnon a E hE z hz hne).2.1
  have hWY : commutatorSpace L D.sourceOrbit z ≤ Y :=
    (commutatorSpace_le_sourceClosure L D.sourceOrbit z z.property D.sourceOrbit_component_normalizes).trans hEY
  apply le_antisymm
  · intro x hx
    have hxR := hcenter.le hx
    have hxV := D.sourceOrbit_m24_centralizer_residual_fixed h hmany hV hq hnon a E hE z hz hne
      ⟨hxR.1.1,hxR.2⟩
    exact hfix.le ⟨hcap.le ⟨hxV,hYC hx.1⟩,hx.2⟩
  · exact hfix.ge.trans (inf_le_inf_right _ hWY)

/-- The full LT-core intersections with both the centralizer core and the
original closure are exactly the original seven-space. -/
theorem sourceOrbit_m24_centralizer_full_core_intersections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    let C := centralizer ({(z : G)} : Set G)
    Q ⊓ C.pCoreIn 2 = commutatorSpace L D.sourceOrbit z ∧
      Q ⊓ (sourceClosure L D.sourceOrbit z).map C.subtype = commutatorSpace L D.sourceOrbit z := by
  let C := centralizer ({(z : G)} : Set G)
  let F := (sourceClosure L D.sourceOrbit z).map C.subtype
  have hFQ : F ≤ C.pCoreIn 2 := map_mono
    (D.sourceOrbit_m24_centralizer_closure_core h hmany hV hq hnon a E hE z hz hne).1
  have hZW := (D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne).2.2.2.1.le
  have hcap (Y : Subgroup G) (hFY : F ≤ Y) (hYQ : Y ≤ C.pCoreIn 2) :
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ Y = commutatorSpace L D.sourceOrbit z := by
    have hh := (D.sourceOrbit_m24_centralizer_intersections_mod_centers
      h hmany hV hq hnon a E hE z hz hne Y hFY hYQ).1
    rw [D.sourceOrbit_m24_centralizer_centers h hmany hV hq hnon a E hE z hz hne Y hFY hYQ,
      sup_eq_left.mpr hZW] at hh
    exact hh
  exact ⟨hcap _ hFQ le_rfl,hcap _ le_rfl hFQ⟩

theorem sourceOrbit_m24_centralizer_core_eq_closure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    (centralizer ({(z : G)} : Set G)).pCoreIn 2 =
      (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype := by
  let C := centralizer ({(z : G)} : Set G)
  let F := (sourceClosure L D.sourceOrbit z).map C.subtype
  have hFQ : F ≤ C.pCoreIn 2 := map_mono
    (D.sourceOrbit_m24_centralizer_closure_core h hmany hV hq hnon a E hE z hz hne).1
  have hc := D.sourceOrbit_m24_centralizer_centers h hmany hV hq hnon a E hE z hz hne
    (C.pCoreIn 2) hFQ le_rfl
  have hp := (D.sourceOrbit_m24_centralizer_core_central_product h hmany hV hq hnon a E hE z hz hne).1
  rw [hc] at hp
  have hZF : zpowers (z : G) ≤ F :=
    (D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne).2.2.2.1.le.trans
      (commutatorSpace_le_sourceClosure L D.sourceOrbit z z.property D.sourceOrbit_component_normalizes)
  exact hp.trans (sup_eq_left.mpr hZF)

/-- The original closure is extraspecial of order 2^13, with its original
involution line as center and the original seven-space as a maximal elementary subgroup. -/
theorem sourceOrbit_m24_centralizer_extraspecial
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    IsExtraspecial 2 (sourceClosure L D.sourceOrbit z) ∧
      Nat.card (sourceClosure L D.sourceOrbit z) = 8192 ∧
      (center (sourceClosure L D.sourceOrbit z)).map
        ((centralizer ({(z : G)} : Set G)).subtype.comp (sourceClosure L D.sourceOrbit z).subtype) =
          zpowers (z : G) := by
  let C := centralizer ({(z : G)} : Set G)
  let F := sourceClosure L D.sourceOrbit z
  let F' := F.map C.subtype
  let f := C.subtype.comp F.subtype
  have hf : Function.Injective f := C.subtype_injective.comp F.subtype_injective
  have hFQ : F' ≤ C.pCoreIn 2 := map_mono
    (D.sourceOrbit_m24_centralizer_closure_core h hmany hV hq hnon a E hE z hz hne).1
  have hc := D.sourceOrbit_m24_centralizer_centers h hmany hV hq hnon a E hE z hz hne F' le_rfl hFQ
  have hmap : (center F).map f = zpowers (z : G) := by
    rw [←hc]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨mem_map_of_mem C.subtype y.property,?_⟩
      rintro b ⟨b,hb,rfl⟩
      exact congrArg f (mem_center_iff.mp hy ⟨b,hb⟩)
    · intro hx
      obtain ⟨y,hy,rfl⟩ := hx.1
      refine ⟨⟨y,hy⟩,mem_center_iff.mpr ?_,rfl⟩
      intro b
      apply hf
      exact hx.2 (f b) (mem_map_of_mem C.subtype b.property)
  have hcard : Nat.card (center F) = 2 := by
    rw [←card_map_of_injective hf,hmap,Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property)
      (fun hh => hne (Subtype.ext hh))
  obtain ⟨helem,hquot,_⟩ := D.sourceOrbit_m24_centralizer_center_quotients h hmany hV hq hnon a E hE z hz hne
  have hn : Nontrivial (F ⧸ center F) := by
    let := Fintype.ofFinite (F ⧸ center F)
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [←Nat.card_eq_fintype_card,hquot]
    decide
  have he : IsExtraspecial 2 F := ⟨hcard,helem,hn⟩
  refine ⟨he,?_,hmap⟩
  rw [card_eq_card_quotient_mul_card_subgroup (center F),hquot,hcard]

/-- The original centralizer two-core is the concrete central product of six
D8 groups. The original seven-space supplies the plus-type recognition. -/
theorem sourceOrbit_m24_centralizer_six_dihedral
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    Nonempty (sourceClosure L D.sourceOrbit z ≃* DihedralCentralProductSix.Model) ∧
      Nonempty (pCore 2 (centralizer ({(z : G)} : Set G)) ≃* DihedralCentralProductSix.Model) := by
  let C := centralizer ({(z : G)} : Set G)
  let F := sourceClosure L D.sourceOrbit z
  let W := commutatorSpace L D.sourceOrbit z
  have hWC : W ≤ C := commutatorSpace_le_centralizer L D.sourceOrbit z z.property D.sourceOrbit_component_normalizes
  let Wc := W.subgroupOf C
  have hWF : Wc ≤ F := le_normalClosure
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le
    (commutatorSpace_le L D.sourceOrbit z D.sourceOrbit_component_normalizes)
  let : IsElementaryAbelian 2 Wc := IsElementaryAbelian.subgroupOf hWC
  let : IsElementaryAbelian 2 (Wc.subgroupOf F) := IsElementaryAbelian.subgroupOf hWF
  obtain ⟨he,hcard,hcenter⟩ := D.sourceOrbit_m24_centralizer_extraspecial h hmany hV hq hnon a E hE z hz hne
  let := he
  have hWcard := (D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne).1
  have hcardA : Nat.card (Wc.subgroupOf F) = 128 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWF).toEquiv).trans
      ((Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv).trans hWcard)
  have hZA : center F ≤ Wc.subgroupOf F := by
    intro x hx
    exact (D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne).2.2.2.1.le
      (hcenter.le (mem_map_of_mem _ hx))
  let e := DihedralCentralProductFourSix.sixRecognition hcard (Wc.subgroupOf F) hcardA hZA
  have hcore : pCore 2 C = F := by
    apply map_injective C.subtype_injective
    exact D.sourceOrbit_m24_centralizer_core_eq_closure h hmany hV hq hnon a E hE z hz hne
  exact ⟨⟨e⟩,⟨(MulEquiv.subgroupCongr hcore).trans e⟩⟩

/-- The full point two-core is the original closure times the original module.
The perfect residual excludes the small core interval before cardinality removes
O₂(LT); no cancellation of the earlier product equality is used. -/
theorem sourceOrbit_m24_centralizer_closure_join_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype ⊔
      D.sourceOrbit = localTwoCore L z := by
  let C := centralizer ({(z : G)} : Set G)
  let F := (sourceClosure L D.sourceOrbit z).map C.subtype
  let R := localResidual L z
  let X := localTwoCore L z
  let W := commutatorSpace L D.sourceOrbit z
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let J := L ⊔ (T : Subgroup G)
  have hLN := D.sourceOrbit_component_normalizes
  have hVX : D.sourceOrbit ≤ X :=
    (D.sourceOrbit_m24_le_centralizer_residual h hmany hV hq hnon a E hE z hz hne).2.2
  have hVQ : D.sourceOrbit ≤ Q := hV ▸ D.le_core
  have hQC : Q ≤ centralizer (D.sourceOrbit : Set G) := hV ▸ D.core_centralizes
  have hcore : F = C.pCoreIn 2 :=
    (D.sourceOrbit_m24_centralizer_core_eq_closure h hmany hV hq hnon a E hE z hz hne).symm
  have hjoin := D.sourceOrbit_m24_centralizer_closure_join_core h hmany hV hq hnon a E hE z hz hne
  have hcap := (D.sourceOrbit_m24_centralizer_full_core_intersections h hmany hV hq hnon a E hE z hz hne).2
  have hRL : R ≤ L := (localResidual_le L z).trans inf_le_left
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hXR : X ≤ R := localTwoCore_le L z
  have hWV : W ≤ D.sourceOrbit := commutatorSpace_le L D.sourceOrbit z hLN
  have hWF : W ≤ F := commutatorSpace_le_sourceClosure L D.sourceOrbit z z.property hLN
  have hLQ : L ≤ normalizer (Q : Set G) := le_sup_left.trans
    (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hXQ : X ≤ normalizer (Q : Set G) := (hXR.trans hRL).trans hLQ
  have hCF : C ≤ normalizer (F : Set G) := by
    rw [hcore]
    exact C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hRF := hRC.trans hCF
  have hRX : R ≤ normalizer (X : Set G) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R (pCore 2 R))
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using
        pCoreIn_le_sylow J (T.subtype le_sup_right)
  obtain ⟨_,_,_,_,_,_,_,_,hTR⟩ :=
    D.sourceOrbit_m24_centralizer_residual h hmany hV hq hnon a E hE z hz hne
  have hFR : F ≤ normalizer (R : Set G) :=
    (le_sup_left.trans hjoin.le).trans
      (sup_le (hXR.trans R.le_normalizer) (hQT.trans hTR))
  have hFX : F ⊓ R ≤ X := by
    rw [hcore,inf_comm]
    exact inf_pCoreIn_le_of_le 2 hRC
  have hQX : Q ⊓ X = D.sourceOrbit := by
    apply le_antisymm ?_ (le_inf hVQ hVX)
    intro x hx
    exact (D.sourceOrbit_m24_centralizer_transvection_kernel h hmany hV hq hnon a E hE z hz hne).le
      ⟨hx.2,centralizer_le hWV (hQC hx.1)⟩
  obtain ⟨_,_,hWZ,hZW,_⟩ :=
    D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne
  let Y := D.sourceOrbit ⊔ (F ⊓ X)
  have hRY : R ≤ normalizer (Y : Set G) :=
    (le_inf (hRL.trans hLN) ((le_inf hRF hRX).trans inf_normalizer_le_normalizer_inf)).trans
      (normalizer_inf_normalizer_le_normalizer_sup D.sourceOrbit (F ⊓ X))
  have hXY : X ≤ F ⊔ D.sourceOrbit := by
    rcases D.sourceOrbit_m24_centralizer_core_interval h hmany hV hq hnon a E hE z hz hne Y
      le_sup_left (sup_le hVX inf_le_right) hRY with hy|hy
    · exfalso
      have hc : ⁅F,R⁆ ≤ D.sourceOrbit := by
        have hh : ⁅F,R⁆ ≤ F ⊓ R := le_inf
          (le_normalizer_iff_commutator_le_left.mp hRF)
          (le_normalizer_iff_commutator_le_right.mp hFR)
        exact ((le_inf (hh.trans inf_le_left) (hh.trans hFX)).trans
          (show F ⊓ X ≤ Y from le_sup_right)).trans hy.le
      have hclass : ⁅F,F⁆ ≤ zpowers (z : G) := by
        have hh := map_mono (f := C.subtype)
          (D.sourceOrbit_m24_centralizer_closure_core h hmany hV hq hnon a E hE z hz hne).2.1
        rw [map_commutator,map_subgroupOf_eq_of_le
          (hZW.le.trans (commutatorSpace_le_centralizer L D.sourceOrbit z z.property hLN))] at hh
        change ⁅F,C.pCoreIn 2⁆ ≤ _ at hh
        rwa [←hcore] at hh
      have hcenter : F ⊓ centralizer (F : Set G) ≤ zpowers (z : G) :=
        (D.sourceOrbit_m24_centralizer_centers h hmany hV hq hnon a E hE z hz hne F
          le_rfl hcore.le).le
      have hZR : zpowers (z : G) ≤ centralizer (R : Set G) := zpowers_le.mpr (by
        intro r hr
        exact mem_centralizer_singleton_iff.mp (hRC hr))
      let : Group.IsPerfect R := Group.IsPerfect.map _
      have hzero := commutator_eq_bot_of_perfect_abelian_classTwo_action F (zpowers (z : G)) R
        hRF hclass hcenter (commutator_eq_bot_iff_le_centralizer.mpr hZR)
        (le_bot_iff.mp ((commutator_mono hc hc).trans_eq (commutator_self_eq_bot_iff.mpr inferInstance)))
      have hZbot : zpowers (z : G) ≤ ⊥ :=
        hWZ.ge.trans ((commutator_mono hWF hXR).trans_eq hzero)
      exact hne (Subtype.ext (mem_bot.mp (hZbot (mem_zpowers (z : G)))))
    · exact hy.ge.trans (sup_le le_sup_right (inf_le_left.trans le_sup_left))
  have hFQ : F ≤ normalizer (Q : Set G) :=
    (le_sup_left.trans hjoin.le).trans (sup_le hXQ Q.le_normalizer)
  have hVF : D.sourceOrbit ≤ normalizer (F : Set G) := (hVX.trans (hXR.trans hRC)).trans hCF
  have hFV : F ⊓ D.sourceOrbit = W := le_antisymm
    (fun x hx => hcap.le ⟨hVQ hx.2,hx.1⟩) (le_inf hWF hWV)
  have h1 := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q F hFQ
  have h2 := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q X hXQ
  have h3 := card_mul_eq_card_inf_mul_card_sup_of_normalizes F D.sourceOrbit hVF
  rw [hcap,sup_comm Q F,hjoin,sup_comm X Q] at h1
  rw [hQX] at h2
  rw [hFV] at h3
  have hc : Nat.card (F ⊔ D.sourceOrbit : Subgroup G) = Nat.card X := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := W))
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q))
    nlinarith [congrArg (fun n => n*Nat.card D.sourceOrbit) h1,
      congrArg (fun n => n*Nat.card F) h2,
      congrArg (fun n => n*Nat.card Q) h3]
  exact (eq_of_le_of_card_ge hXY hc.le).symm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
