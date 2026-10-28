module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.MaximumFamily
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.BaumannAssembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PcQuotient.SylowCenter
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PcQuotient.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal

/-!
# The original local structure before the temporary replacement

This assembles the first five paragraphs of the proof of 15.3.67. The inputs
are the genuine earlier ordering, natural action, residual image and core
identities, the abelian span of 15.3.50, and the selected escaping singular
line. All the line-Sylow geometry and the conclusions of 15.3.66 used here
are proved from these inputs.

The actual maximum elementary family supplies Thompson and Baumann control.
The central Sylow-image movement supplies a noncentral element of `P_c`;
the residual argument and commuting quotient images construct the marked
product with first factor S₃ and second factor the actual centralizer image.
The same selected element is used for the fixed subgroups and the paired
section. The Frattini argument gives the escaping Thompson factor `I`.

`initialStructure` constructs all of this data. Its `paired` field feeds
`PairedModule.SourceInputs.pairedEquiv` and `pairedSection`, after installing
the proved `span_elementary` instance. No conclusion of 15.3.67 occurs in
`EarlierData`; the later offender argument and descent remain separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122, 1142, 1152–1153, especially the proof of 15.3.67 before the
temporary replacement on p.1153 (PDF p.1170).
-/

@[expose] public section

open Subgroup Stellmacher OrthogonalFourBinary
open CFSG.Quasithin.ChapterA.Section05To06
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
open GoldschmidtCore.LocalRelations Orthogonal Descent.QuotientIdentification

variable {G : Type*} [Group G] [Finite G]

/-- Earlier source conclusions and the selected line. The subgroups `V`, `Y`,
`Z`, `S`, and `Z_S` are the published constructions, not independent labels. -/
structure EarlierData (T : Sylow 2 G) (M Mc V₁ E : Subgroup G) where
  natural : NaturalAction (localModule T M) M
  ordering : IsOrderingMaximal T M
  module_le : localModule T M ≤ (T : Subgroup G)
  plane_le : V₁ ≤ localModule T M
  plane_card : Nat.card V₁ = 4
  plane_definite : ∀ v : V₁, v ≠ 1 →
    ¬ natural.singular ⟨v, plane_le v.property⟩
  central_fixed : centralInvolutions T =
    localModule T M ⊓ centralizer (T : Set G)
  central_card : Nat.card (centralInvolutions T) = 2
  other_centralizer : Mc = centralizer (centralInvolutions T : Set G)
  residual_image : actionImage natural (residualY M Mc) =
    pResidual 2 TerminalLines.IsometryGroup
  residual_core_module : twoCoreAmbient (residualY M Mc) =
    residualY M Mc ⊓ centralizer (localModule T M : Set G)
  residual_core_center : (residualY M Mc).pCoreIn 2 =
    residualY M Mc ⊓ centralizer (centralInvolutions T : Set G)
  core_movement : ⁅fixedPlane (localModule T M) (planeStabilizer T V₁), Mc.pCoreIn 2⁆ =
    centralInvolutions T
  local_span_abelian : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)
  line_le : E ≤ localModule T M
  line_card : Nat.card E = 4
  line_singular : ∀ e : E, natural.singular ⟨e, line_le e.property⟩
  selected : Sylow 2 (lineM M E)
  selected_map : (selected : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E
  escape : ¬ lineNormalizer E ≤ M

/-- The derived groups and compatible markings in the original line normalizer.
In particular `characteristic_control` uses the source's `C(G,B_E)`. -/
structure InitialStructure (T : Sylow 2 G) (M Mc E : Subgroup G) where
  thompson : elementaryAbelianMaxJ (lineT T E) =
    elementaryAbelianMaxJ (lineR T (localModule T M))
  baumann : lineB T E = ChapterB.baumann (lineR T (localModule T M))
  baumann_le : lineB T E ≤ lineR T (localModule T M)
  characteristic_control : (lineB T E).characteristicNormalizerClosure ≤ M
  normalizer_control : normalizer (lineT T E : Set G) ≤ M
  thompson_normalizer_control : normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M
  line_sylow : Sylow 2 (lineNormalizer E)
  line_sylow_map : (line_sylow : Subgroup (lineNormalizer E)).map
    (lineNormalizer E).subtype = lineT T E
  pc_noncentral : ¬ linePc Mc E ≤ lineC E
  residual_commutator : lineY (residualY M Mc) E =
    ⁅lineY (residualY M Mc) E, linePc Mc E⁆
  residual_span : lineY (residualY M Mc) E =
    twoResidualAmbient (conjugateSpanBy (linePc Mc E) (lineNormalizer E))
  residual_normal : ((lineY (residualY M Mc) E).subgroupOf (lineNormalizer E)).Normal
  span_commutator : lineV (localModule T M) E =
    ⁅lineV (localModule T M) E, lineY (residualY M Mc) E⁆
  span_centralizer : lineV (localModule T M) E =
    conjugateSpanBy (localModule T M) (lineC E)
  span_le_local : lineV (localModule T M) E ≤ conjugateSpanBy (localModule T M) Mc
  span_elementary : IsElementaryAbelian 2 (lineV (localModule T M) E)
  span_le_core : lineV (localModule T M) E ≤ lineQ E
  centralizer_sylow : Sylow 2 (lineC E)
  centralizer_sylow_map : (centralizer_sylow : Subgroup (lineC E)).map
    (lineC E).subtype = (T : Subgroup G) ⊓ lineC E
  sylow_kernel : lineS (residualY M Mc) T E = (T : Subgroup G) ⊓ lineC E
  quotient : MarkedDecomposition (residualY M Mc) T E
  tau_mem : quotient.tau ∈ linePc Mc E
  tau_outside : quotient.tau ∉ lineS (residualY M Mc) T E
  tau_fixed : E ⊓ centralizer ({quotient.tau} : Set G) = centralInvolutions T
  paired : PairedModule.SourceInputs (localModule T M) M (residualY M Mc) T E quotient
  thompson_product : (lineNormalizer E : Set G) = (lineI E : Set G) * (lineM M E : Set G)
  thompson_escape : ¬ lineI E ≤ M
  thompson_image : ((lineI E).subgroupOf (lineNormalizer E)).map
    (QuotientGroup.mk' (pCore 2 (lineNormalizer E))) ≠ ⊥

variable {T : Sylow 2 G} {M Mc V₁ E : Subgroup G}

/-- Construct the original local structure from earlier results and the selected
line, discharging the maximum-family, residual-action, quotient and module inputs. -/
noncomputable def initialStructure [IsElementaryAbelian 2 (localModule T M)]
    (s : EarlierData T M Mc V₁ E) : InitialStructure T M Mc E := by
  apply Classical.choice
  have hTM := s.ordering.1.2
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [s.other_centralizer]
    exact le_centralizer_iff.mp (s.central_fixed.le.trans inf_le_right)
  have hcore : twoCoreAmbient Mc ≤ (T : Subgroup G) := by
    have h := pCoreIn_le_sylow Mc (T.subtype hTMc)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTMc] at h
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hTY : (T : Subgroup G) ≤ normalizer (residualY M Mc : Set G) :=
    hTM.trans ((normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal M Mc))
  have hEne : E ≠ ⊥ := by
    intro he
    have hc := s.line_card
    rw [he, card_bot] at hc
    omega
  have hZne : centralInvolutions T ≠ ⊥ := by
    intro he
    have hc := s.central_card
    rw [he, card_bot] at hc
    omega
  let : IsKleinFour E := singularLine_isKleinFour s.natural E
    s.line_le s.line_card s.line_singular
  let := s.local_span_abelian
  obtain ⟨_, _, hklein, _, hZE, hseed⟩ := line_sylow_geometry_of_source s.natural T V₁ E
    hTM s.plane_le s.plane_card s.plane_definite s.line_le s.line_card
    s.line_singular s.central_fixed s.selected s.selected_map
  have hfull := residualY_lineProduct_full_action s.natural Mc T E
    s.line_le s.line_card s.line_singular s.residual_image s.selected s.selected_map
  obtain ⟨_, hVcomm, hQC, hkernel, hprod⟩ := residualY_lineNormalizer_consequences
    s.natural Mc T E hTM s.line_le s.line_card s.line_singular
    s.residual_image s.residual_core_module s.selected s.selected_map
  have hCMc := centralizer_line_le_of_Z_le E (centralInvolutions T) Mc hZE s.other_centralizer
  have hfamily := lineT_maximum_family_centralizes s.natural T E hTM s.module_le
    s.line_le s.line_card s.line_singular s.selected s.selected_map
  obtain ⟨hJ, hB, hBR, hcontrol, hNT, hNJ, U, hU⟩ :=
    line_control_of_maximum_family T M E s.ordering s.module_le s.line_le hEne
      s.selected s.selected_map hfamily
  have hnoncentral := linePc_noncentral_of_model normalSylowLineMovement s.natural T
    Mc E (fixedPlane (localModule T M) (planeStabilizer T V₁)) (centralInvolutions T)
    hTM hTMc hcore inf_le_left hZne s.core_movement s.line_le s.line_card
    s.line_singular s.selected s.selected_map
  have hcomm := lineY_commutator_of_noncentral_Pc Mc (residualY M Mc) E T
    hcore hTY hfull hkernel hnoncentral
  obtain ⟨hres, hnormal⟩ := lineY_residual_and_normal Mc (residualY M Mc) T E
    hTMc hCMc hcore hTY hprod hcomm
  have hmoved := lineV_eq_commutator (localModule T M) (residualY M Mc) E
    ((normal_subgroupOf_iff_le_normalizer
      ((lineY_le (residualY M Mc) E).trans inf_le_right)).mp hnormal) hVcomm
  obtain ⟨hspan, hspanle, helem, hspanQ⟩ := lineV_span_and_elementary
    M Mc (residualY M Mc) T (localModule T M) E s.line_le s.natural.normalizes
    hYM hTM hCMc hprod
  obtain ⟨hS, C, hC⟩ := lineS_and_centralizer_sylow (residualY M Mc) T E U hU hkernel
  have hPcT := linePc_le_lineT Mc T E hcore
  have houtside := linePc_not_le_lineS_of_noncentral Mc (residualY M Mc) T E hnoncentral hkernel
  obtain ⟨τ, hτ, hτS, _, hfixed⟩ := exists_tau_with_fixed_subgroup_of_source
    Mc (residualY M Mc) T E (centralInvolutions T) s.other_centralizer
    s.line_card s.central_card hZE hS hPcT houtside
  let d := markedDecompositionOfSource Mc (residualY M Mc) E (centralInvolutions T) T
    hTMc hCMc hcore hTY hfull hkernel hZE s.residual_core_center τ hτ hτS
  have hQCT : lineQ E ≤ (T : Subgroup G) ⊓ centralizer (E : Set G) :=
    le_inf (((hU ▸ pCoreIn_le_sylow (lineNormalizer E) U) : lineQ E ≤ lineT T E).trans
      inf_le_left) hQC
  have hpaired : PairedModule.SourceInputs (localModule T M) M (residualY M Mc) T E d :=
    { natural := s.natural
      sylow_le := hTM
      line_le := s.line_le
      line_card := s.line_card
      singular := s.line_singular
      sylow_image := hklein
      span_eq := hspan
      core_le := hQCT
      seed_commutator := hseed
      moved := hmoved
      residual_image := lineY_image_eq_alternating (residualY M Mc) E T hTY d
      tau_outside := fun h => hτS (hS.symm ▸ h) }
  have hJS : elementaryAbelianMaxJ (lineT T E) ≤ (T : Subgroup G) ⊓ lineC E :=
    le_inf ((sSup_le fun _ hA => hA.1).trans inf_le_left)
      ((sSup_le hfamily).trans (centralizer_le s.line_le))
  have hIprod := lineI_product M (T : Subgroup G) E U hU hJS hNJ
  have hIescape := lineI_escapes M E s.escape hIprod
  exact ⟨
    { thompson := hJ
      baumann := hB
      baumann_le := hBR
      characteristic_control := hcontrol
      normalizer_control := hNT
      thompson_normalizer_control := hNJ
      line_sylow := U
      line_sylow_map := hU
      pc_noncentral := hnoncentral
      residual_commutator := hcomm
      residual_span := hres
      residual_normal := hnormal
      span_commutator := hmoved
      span_centralizer := hspan
      span_le_local := hspanle
      span_elementary := helem
      span_le_core := hspanQ
      centralizer_sylow := C
      centralizer_sylow_map := hC
      sylow_kernel := hS
      quotient := d
      tau_mem := hτ
      tau_outside := hτS
      tau_fixed := hfixed
      paired := hpaired
      thompson_product := hIprod
      thompson_escape := hIescape
      thompson_image := lineI_image_ne_bot M T E hTM U hU hIescape }⟩

namespace InitialStructure
open PairedModule
variable [IsElementaryAbelian 2 (localModule T M)] (r : InitialStructure T M Mc E)

omit [Finite G] in
/-- The constructed cubic actor selects the two actual fixed-subgroup images;
these images are complementary and invariant under the original centralizer. -/
theorem fixed_decomposition :
    letI := r.span_elementary
    let y := r.paired.actionData.y
    (y : G) ∈ lineY (residualY M Mc) E ∧
      orderOf (r.quotient.equiv (quotientMap E y)).1 = 3 ∧
      (r.quotient.equiv (quotientMap E y)).2 = 1 ∧
      (fixedImage (localModule T M) E r.quotient.tau ⊔
        fixedImage (localModule T M) E ((y : G)⁻¹ * r.quotient.tau * y) = ⊤ ∧
       fixedImage (localModule T M) E r.quotient.tau ⊓
        fixedImage (localModule T M) E ((y : G)⁻¹ * r.quotient.tau * y) = ⊥) ∧
      ∀ c : lineC E,
        (fixedImage (localModule T M) E r.quotient.tau).map
          (sectionRepresentation (localModule T M) E
            (inclusion (centralizer_le_normalizer (E : Set G)) c)) =
          fixedImage (localModule T M) E r.quotient.tau ∧
        (fixedImage (localModule T M) E ((y : G)⁻¹ * r.quotient.tau * y)).map
          (sectionRepresentation (localModule T M) E
            (inclusion (centralizer_le_normalizer (E : Set G)) c)) =
          fixedImage (localModule T M) E ((y : G)⁻¹ * r.quotient.tau * y) := by
  let := r.span_elementary
  exact ⟨r.paired.cubic_actor.1, r.paired.cubic_actor.2.1,
    r.paired.cubic_actor.2.2, r.paired.fixedImages, r.paired.fixedImages_invariant⟩

omit [Finite G] in
/-- Right conjugation by the selected residual element sends the first summand
onto the second. This does not assert that an element of order three swaps both. -/
theorem fixedImage_right_conjugation :
    letI := r.span_elementary
    let y := r.paired.actionData.y
    (fixedImage (localModule T M) E r.quotient.tau).map
        (sectionRepresentation (localModule T M) E y⁻¹) =
      fixedImage (localModule T M) E ((y : G)⁻¹ * r.quotient.tau * y) := by
  let := r.span_elementary
  exact fixedImage_rightConjugate (localModule T M) E r.paired.actionData.y r.quotient.tau

/-- Binary coordinates on the actual relative quotient image of `V_E` in `G_E/E`.
The two coordinates carry the same action of `C_E` by
`SourceInputs.pairedEquiv_centralizer` and its quotient comparison. -/
noncomputable def pairedEquiv :
    letI := r.span_elementary
    Additive (ambientProjection (localModule T M) E r.paired.line_le).range ≃ₗ[ZMod 2]
      fixedImage (localModule T M) E r.quotient.tau ×
        fixedImage (localModule T M) E r.quotient.tau := by
  letI := r.span_elementary
  exact r.paired.ambientPairedEquiv

/-- The offender consumer receives the marked projection with kernel exactly `E`
and diagonal centralizer action in the genuine relative ambient group `G_E`. -/
noncomputable def pairedSection :
    letI := r.span_elementary
    letI := relativeSpan_normal (localModule T M) E r.paired.line_le
    letI := relativeSpan_elementary (localModule T M) E r.paired.line_le
    Offenders.PairedSection
      ((lineV (localModule T M) E).subgroupOf (lineNormalizer E))
      (E.subgroupOf (lineNormalizer E)) ((lineC E).subgroupOf (lineNormalizer E))
      (pCore 2 (lineNormalizer E))
      (QuotientGroup.mk' (centralizer
        (((lineV (localModule T M) E).subgroupOf (lineNormalizer E)) : Set (lineNormalizer E))))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) r.paired.sigma := by
  letI := r.span_elementary
  exact r.paired.pairedSection

end InitialStructure

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
