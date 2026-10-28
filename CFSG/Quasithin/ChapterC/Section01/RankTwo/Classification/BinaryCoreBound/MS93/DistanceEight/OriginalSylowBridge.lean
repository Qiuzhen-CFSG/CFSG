module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCentralFour

/-!
# What the original full-Sylow hypothesis supplies

The source four-group is constructed in the characteristic replacement.  Its
existing inclusions put it in the original commutator core, hence in the
ambient two-core.  If the original radical is identified with a full Sylow
subgroup, this gives containment in that Sylow.  To place the four-group in
`Ω₁ Z(P)`, one still needs its centralization by the original Sylow; the
replacement `Earlier` record does not contain that action statement.

The replacement edge omega-center is characteristic in the original radical
and has at least sixteen elements.  Its size follows from the disjoint natural
eight-group and fixed four-group in the vertex layer, whose edge layer has
index two.  On the actual input with original central omega of order at most
four, the whole replacement omega-center is therefore not central in the
original radical.  The included four-group remains a proper subproblem.

Source: MS93 (1993), (4.4), (4.5.1) and Section 7, printed pp.890--896,
932--933; Aschbacher--Smith C.1.34(4), pp.136--137, and 15.3.23--24.
-/

public section

open Subgroup Stellmacher Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup

universe u
variable {J : Type u} [Group J] [Finite J]
  {κ : GroupClass.{u}} {L R : Subgroup J} {h : Input κ L R}
  (t : InputSetup h)

include t

/-- Under the literal full-Sylow identification, the included factor lies in
the chosen Sylow subgroup. -/
theorem reducedCentralFour_le_sylow
    (P : Sylow 2 J) (hP : R = (P : Subgroup J))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    t.reducedCentralFour ≤ (P : Subgroup J) := by
  rw [← hP]
  exact (t.reducedCentralFour_le_commutatorCore common earlier).trans
    ((commutator_le_left _ _).trans h.radical.twoCore_le)

/-- The only missing step in the direct `Ω₁ Z(P)` route is the original
Sylow action.  Once that action is supplied, the elementary factor is in the
ambient omega-center. -/
theorem reducedCentralFour_le_omega_of_centralizes_sylow
    (P : Sylow 2 J) (hP : R = (P : Subgroup J))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (hcentral : t.reducedCentralFour ≤ centralizer ((P : Subgroup J) : Set J)) :
    t.reducedCentralFour ≤ omegaOneCenterAmbient (P : Subgroup J) := by
  let := t.reducedCentralFour_elementary common earlier
  intro x hx
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨t.reducedCentralFour_le_sylow P hP common earlier hx,
      elemPow_eq_one_of_isElementaryAbelian x hx, hcentral hx⟩

/-- For this literal factor, replacing original-core fixation by containment
in the original Sylow omega-center does not weaken the outstanding obligation. -/
theorem reducedCentralFour_le_omega_iff_centralizes_core
    (P : Sylow 2 J) (hP : R = (P : Subgroup J))
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    t.reducedCentralFour ≤ omegaOneCenterAmbient (P : Subgroup J) ↔
      t.reducedCentralFour ≤ centralizer (pCore 2 J : Set J) := by
  constructor
  · intro hO x hx q hq
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hO hx)).2.2 q
      (hP ▸ h.radical.twoCore_le hq)
  · intro hc
    apply t.reducedCentralFour_le_omega_of_centralizes_sylow P hP common earlier
    intro x hx y _
    exact mem_center_iff.mp
      (t.reducedCentralFour_le_center_of_centralizes_core earlier hc hx) y

/-- The source edge omega-center is large: the disjoint natural eight-group
and fixed four-group in the vertex layer, together with the source edge
index two, give at least sixteen elements. -/
theorem replacement_radical_omega_card_ge_sixteen
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    16 ≤ Nat.card (omegaCenter t.reduction.radical) := by
  let R₀ := t.reduction.radical
  let a := alpha R₀
  let b := beta R₀
  have hHZ : H R₀ a ≤ Z R₀ a :=
    DistanceEight.CoreFactors.H_le_Z_of_central common rfl (earlier.centrality a rfl)
  have hn : H R₀ a ≤ normalizer (U R₀ a : Set (FreeAmalgam R₀)) :=
    (hHZ.trans (Z_le_stabilizer R₀ a)).trans (U_normalized a)
  have hUH : 32 ≤ Nat.card (U R₀ a ⊔ H R₀ a : Subgroup (FreeAmalgam R₀)) := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn
      (earlier.factor_inclusions common).2.2, common.natural.card]
    have hH := DistanceEight.CoreFactors.Early.First.Layer.H_card_lower common earlier a rfl
    change 4 ≤ Nat.card (H R₀ a) at hH
    omega
  let := finite_Z R₀ a
  have hZ : 32 ≤ Nat.card (Z R₀ a) :=
    hUH.trans (card_le_of_le (sup_le (U_le_Z a) hHZ))
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R₀))
    (Z R₀ b) (Z R₀ a) bot_le
      (Escape.EdgeTransfer.edge_Z_le a b rfl (base_adjacent R₀))
  rw [relIndex_bot_left, relIndex_bot_left,
    earlier.edge_Z_index a b rfl (base_adjacent R₀)] at hcount
  have hE : 16 ≤ Nat.card (Z R₀ b) := by omega
  change 16 ≤ Nat.card (omegaCenter (Q R₀ (beta R₀))) at hE
  rwa [Q_beta, omegaCenter_map R₀ (embedM R₀) (embedM_injective R₀),
    card_map_of_injective (embedM_injective R₀)] at hE

/-- The replacement omega-center viewed intrinsically in the original radical. -/
@[expose] noncomputable def replacementOmega : Subgroup R :=
  omegaCenter t.reduction.subgroup

/-- Characteristicity survives the original characteristic replacement. -/
theorem replacementOmega_characteristic : t.replacementOmega.Characteristic := by
  let := t.reduction.characteristic
  let : (omega₁ (center t.reduction.subgroup) (p := 2)).Characteristic :=
    omega₁_characteristic _
  change (((omega₁ (center t.reduction.subgroup) (p := 2)).map
    (center t.reduction.subgroup).subtype).map t.reduction.subgroup.subtype).Characteristic
  infer_instance

/-- The two replacement carriers agree through their literal ambient inclusions. -/
theorem replacementOmega_map : t.replacementOmega.map R.subtype =
    (omegaCenter t.reduction.radical).map t.reduction.overgroup.subtype := by
  change (omegaCenter t.reduction.subgroup).map R.subtype = _
  rw [← omegaCenter_map _ R.subtype R.subtype_injective,
    ← omegaCenter_map _ t.reduction.overgroup.subtype
      t.reduction.overgroup.subtype_injective,
    map_subgroupOf_eq_of_le (show t.reduction.ambient ≤ t.reduction.overgroup from le_sup_right)]

/-- The included source four-group lies in the characteristic replacement
omega-center, with its image in the original group unchanged. -/
theorem reducedCentralFour_le_replacementOmega
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    t.reducedCentralFour ≤ t.replacementOmega.map R.subtype := by
  rw [t.replacementOmega_map]
  rintro x ⟨z, hz, rfl⟩
  have hzE := DistanceEight.CoreFactors.Early.H_le_edge_Z common earlier
    (a := alpha t.reduction.radical) (t := beta t.reduction.radical) rfl
    (base_adjacent t.reduction.radical) hz
  change embedM t.reduction.radical z ∈ omegaCenter
    (Q t.reduction.radical (beta t.reduction.radical)) at hzE
  rw [Q_beta, omegaCenter_map _ _ (embedM_injective _)] at hzE
  obtain ⟨w, hw, he⟩ := hzE
  have hwz : w = z := embedM_injective _ he
  exact mem_map_of_mem t.reduction.overgroup.subtype (hwz ▸ hw)

/-- Both intrinsic replacement carriers give the same cardinality. -/
theorem replacementOmega_card_ge_sixteen
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    16 ≤ Nat.card t.replacementOmega := by
  have hcard := congrArg (fun W : Subgroup J => Nat.card W) t.replacementOmega_map
  rw [card_map_of_injective R.subtype_injective,
    card_map_of_injective t.reduction.overgroup.subtype_injective] at hcard
  exact hcard.symm ▸ t.replacement_radical_omega_card_ge_sixteen common earlier

/-- On the actual small-omega input, the original radical cannot centralize
the entire replacement omega-center.  Thus characteristicity alone cannot
transport that whole edge group into the original central omega. -/
theorem replacementOmega_not_le_center
    (hsmall : Nat.card (omegaOneCenterAmbient R) ≤ 4)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    ¬ t.replacementOmega ≤ center R := by
  intro hc
  let : IsElementaryAbelian 2 t.replacementOmega :=
    omegaCenter_elementary t.reduction.subgroup
  have hmap : t.replacementOmega.map R.subtype ≤ omegaOneCenterAmbient R := by
    rintro x ⟨y, hy, rfl⟩
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨y.property, ?_, ?_⟩
    · exact congrArg R.subtype (elemPow_eq_one_of_isElementaryAbelian y hy)
    · intro r hr
      exact congrArg Subtype.val (mem_center_iff.mp (hc hy) ⟨r, hr⟩)
  have hb := (card_le_of_le hmap).trans hsmall
  rw [card_map_of_injective R.subtype_injective] at hb
  have hl := t.replacementOmega_card_ge_sixteen common earlier
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup

