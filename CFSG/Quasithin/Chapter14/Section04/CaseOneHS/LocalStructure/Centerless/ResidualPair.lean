module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Conjugator
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.FaithfulSeed

/-!
# Residual generation and the disjoint shifted centers

The original ordered-parabolic generation theorem gives a point-fixing
residual pair. Full L-action replaces its LT-conjugator by an element of L;
the difference centralizes V and normalizes the residual. Conjugating the
pair by the omitted-point element gives the source's displaced-point fixer.
The same element supplies both plane identities and generates L with the
original omitted-point residual.

Sylow-center detection turns Z(LT) ∩ U = 1 into C_U(L) = 1. The residual
pair then proves Z(U) ∩ Z(I₂ˡ) = 1. Relative normality in the plane
normalizers shows that these disjoint subgroups normalize one another,
hence Z(I₂ˡ) centralizes Z(U).

The explicit seed premise is source 14.3.25, still owned by
qt-d-hs-centerless-source; this module does not assert that exclusion or
centerlessness. Its actual amalgam application is in ShiftedAmalgam.
Source: Aschbacher--Smith, 14.3.28 and the opening of 14.3.31,
printed pp.1001--1003; 12.8.10(5), printed p.854.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem conjugate_mul (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  simp only [conjugate, map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
private theorem residual_normalized (P : Subgroup G) :
    P ≤ normalizer ((pResidual 2 P).map P.subtype : Set G) := by
  have h := (pResidual 2 P).le_normalizer_map P.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h

/-- The actual omitted-point residual and a point-fixing conjugate generate L. -/
theorem source_point_fixed_residual_pair (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    ∃ k ∈ L, k ∈ F.H ∧ L = F.orderedResidual L 1 ⊔
      conjugate (F.orderedResidual L 1) k := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨_, hs⟩ := F.ordered_generation_of_full_binary_action (by decide) L
    chosen.normalizes h.full_L_action (h.centralizer_LT structural)
  obtain ⟨k, hk, he⟩ := hs 1 (by decide) (by decide)
  have ht := F.initialResiduals_terminal_of_full_binary_action (by decide) L
    chosen.normalizes ((pResidual_eq_top_iff 2 L).mp h.residual)
    (h.sylow_normalizes structural) h.full_L_action
  change F.initialResiduals L 2 = L at ht
  rw [ht, F.initialResiduals_one] at he
  let f := F.naturalFlagAction L chosen.normalizes
  let k' : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨k, hk.1⟩
  obtain ⟨x, hxL, hx⟩ := h.full_L_action (f k')
  have hc : k * x⁻¹ ∈ centralizer (V : Set G) := by
    have hx' : x⁻¹ * k ∈ centralizer (V : Set G) := by
      intro v hv
      have hh := hx ⟨v, hv⟩
      change x * v * x⁻¹ = k * v * k⁻¹ at hh
      have hh' := congrArg (fun y : G => x⁻¹ * y * k) hh
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh'
    have hxN := chosen.normalizes hxL
    have hn := normalizer_le_normalizer_centralizer V hxN
    have hh := (mem_normalizer_iff.mp hn (x⁻¹ * k)).mp hx'
    simpa only [mul_inv_cancel_left] using hh
  have hcP : k * x⁻¹ ∈ F.P L := by
    refine ⟨(L ⊔ (T : Subgroup G)).mul_mem hk.1 (mem_sup_left (L.inv_mem hxL)), ?_⟩
    apply Subgroup.mem_iInf.mpr
    intro i
    apply Subgroup.mem_iInf.mpr
    intro _
    exact Subgroup.centralizer_le_normalizer _ (centralizer_le (F.le_seed i) hc)
  have hcR : k * x⁻¹ ∈ normalizer (F.orderedResidual L 1 : Set G) := by
    rw [orderedResidual, F.orderedParabolic_one]
    exact residual_normalized _ hcP
  have hconj : conjugate (F.orderedResidual L 1) k =
      conjugate (F.orderedResidual L 1) x := by
    have hh := conjugate_mul (F.orderedResidual L 1) (k * x⁻¹) x
    rw [(conjugate_eq_iff _ _).mpr hcR, inv_mul_cancel_right] at hh
    exact hh
  have hxH : x ∈ F.H := by
    have hkH := F.orderedParabolic_le_H (by decide) L (by decide : 2 ≤ 1 + 1) hk
    have hcH : k * x⁻¹ ∈ F.H := Subgroup.centralizer_le_normalizer _
      (centralizer_le (F.le_seed 1) hc)
    have hh := F.H.mul_mem (F.H.inv_mem hcH) hkH
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
  exact ⟨x, hxL, hxH, he.trans (congrArg (_ ⊔ ·) hconj)⟩

/-- The same residual generation with the source displaced point fixed. -/
theorem source_shifted_residual_pair (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (g : G) (hgL : g ∈ L) (hgP : g ∈ F.P L) :
    ∃ l ∈ L, l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l := by
  obtain ⟨k, hkL, hkH, hgen⟩ :=
    source_point_fixed_residual_pair d earlier hq chosen structural F
  let l := g⁻¹ * k * g
  have hgR : conjugate (F.orderedResidual L 1) g = F.orderedResidual L 1 := by
    apply (conjugate_eq_iff _ _).mpr
    rw [orderedResidual, F.orderedParabolic_one]
    exact residual_normalized _ hgP
  have hlC : l ∈ centralizer (conjugate (F.Vi 1) g : Set G) := by
    have hkC : k ∈ centralizer (F.Vi 1 : Set G) :=
      normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)) hkH
    have hh := map_centralizer_le_centralizer_image (F.Vi 1 : Set G)
      (MulAut.conj g⁻¹).toMonoidHom (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hkC)
    simpa only [l, conjugate, coe_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hh
  refine ⟨l, L.mul_mem (L.mul_mem (L.inv_mem hgL) hkL) hgL, hlC, ?_⟩
  have he := congrArg (fun A : Subgroup G => conjugate A g) hgen
  have hgN := (conjugate_eq_iff L g).mpr (L.le_normalizer hgL)
  change conjugate L g = (F.orderedResidual L 1 ⊔
    conjugate (F.orderedResidual L 1) k).map (MulAut.conj g⁻¹).toMonoidHom at he
  rw [hgN, Subgroup.map_sup] at he
  change L = conjugate (F.orderedResidual L 1) g ⊔
    conjugate (conjugate (F.orderedResidual L 1) k) g at he
  rw [hgR] at he
  apply he.trans
  apply congrArg (F.orderedResidual L 1 ⊔ ·)
  rw [show l = g⁻¹ * k * g from rfl, conjugate_mul, conjugate_mul,
    show conjugate (F.orderedResidual L 1) g⁻¹ = F.orderedResidual L 1 from
      (conjugate_eq_iff _ _).mpr ((normalizer _).inv_mem ((conjugate_eq_iff _ _).mp hgR))]

/-- The omitted-point residual is contained in the actual I₂. -/
theorem source_ordered_residual_le_parabolic (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    F.orderedResidual L 1 ≤ F.I₂ L ∧
      F.Gi 2 ≤ normalizer (F.I₂ L : Set G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨g, hgP, hgH⟩ := source_conjugator d earlier hq chosen structural F
  obtain ⟨hc, hs⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F alternatives)
  obtain ⟨_, hI, _, _, hIG, hIN, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural) hc hs
    (source_seed_geometry d earlier hq chosen F).2.1 hne g hgP hgH
  refine ⟨?_, (normal_subgroupOf_iff_le_normalizer hIG).mp hIN⟩
  rw [orderedResidual, F.orderedParabolic_one, hI]
  exact le_sup_left

/-- Source 14.3.25 removes the whole fixed subgroup C_U(L), by Sylow-center detection. -/
theorem source_closure_centralizer_of_seed (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hseed : centralLTSeed F L = ⊥) :
    F.U ⊓ centralizer (L : Set G) = ⊥ := by
  have hUT := CaseOneGeometry.source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hn : (T : Subgroup G) ≤ normalizer
      (F.U ⊓ centralizer (L : Set G) : Set G) :=
    (le_inf ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
      (((higherRankHypothesis d earlier hq chosen).sylow_normalizes structural).trans
        (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
  apply eq_bot_of_normalized_of_omega_center_disjoint (T : Subgroup G) _
    T.isPGroup' (inf_le_left.trans hUT) hn
  apply le_bot_iff.mp
  rintro x ⟨hxZ, hxU, hxL⟩
  have hxT : x ∈ (T : Subgroup G) := hUT hxU
  have hxC : x ∈ Chapter12.Section08.centerIn (L ⊔ (T : Subgroup G)) := by
    rw [centerIn_eq_inf_centralizer]
    refine ⟨mem_sup_right hxT, ?_⟩
    have hz : zpowers x ≤ centralizer (T : Set G) :=
      zpowers_le.mpr (omega_centralizes_sylow (show x ∈ sylowOmega T from hxZ))
    have hl : zpowers x ≤ centralizer (L : Set G) := zpowers_le.mpr hxL
    have hj : L ⊔ (T : Subgroup G) ≤ centralizer (zpowers x : Set G) :=
      sup_le (le_centralizer_iff.mp hl) (le_centralizer_iff.mp hz)
    exact le_centralizer_iff.mp hj (mem_zpowers x)
  exact hseed ▸ (show x ∈ centralLTSeed F L from ⟨hxC, hxU⟩)

/-- Literal 14.3.28(2), once the preceding faithful-family exclusion is proved. -/
theorem source_shifted_disjoint_of_residual_pair (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hgen : L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l) :
    F.ZU ⊓ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) = ⊥ := by
  have hI := source_ordered_residual_le_parabolic d earlier hq chosen structural alternatives F hne
  have hgen' : L ≤ F.I₂ L ⊔ conjugate (F.I₂ L) l := by
    conv_lhs => rw [hgen]
    exact sup_le_sup hI.1 (map_mono hI.1)
  have hmeet : F.ZU ⊓ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) =
      Chapter12.Section08.centerIn (F.I₂ L) ⊓
        Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) := by
    rw [source_shifted_center_intersection d earlier hq chosen structural alternatives F hne
      g hgP hgH l hl, ← inf_assoc,
      (source_center_intersections d earlier hq chosen structural alternatives F hne g hgP hgH).1]
    have hle : Chapter12.Section08.centerIn (F.I₂ L) ≤ conjugate F.ZU g :=
      ((source_center_intersections d earlier hq chosen structural alternatives F hne g hgP hgH).1.ge).trans inf_le_right
    rw [← inf_assoc, inf_eq_left.mpr hle]
  apply le_bot_iff.mp
  rw [← source_closure_centralizer_of_seed d earlier hq chosen structural alternatives F hseed]
  refine le_inf (inf_le_left.trans (map_subtype_le (center F.U))) ?_
  rw [hmeet]
  apply le_centralizer_iff.mp
  apply hgen'.trans
  apply sup_le
  · exact le_centralizer_iff.mp (inf_le_left.trans (centerIn_le_centralizer _))
  · exact le_centralizer_iff.mp (inf_le_right.trans (centerIn_le_centralizer _))

/-- All point and plane clauses hold for the same pair that generates L. -/
theorem source_shifted_generating_geometry (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    ∃ g l : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      F.Vi 2 = F.Vi 1 ⊔ conjugate (F.Vi 1) g ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      conjugate (F.Vi 2) l = conjugate (F.Vi 1) g ⊔ conjugate (F.Vi 1) l ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l := by
  let := chosen.elementary
  obtain ⟨g, k, hgL, hgP, hgH, hkL, _, hplane, hspace, _⟩ :=
    source_shifted_conjugator d earlier hq chosen F
  have hnot : ¬ L ≤ F.Gi 2 := by
    intro hL
    have hkP : conjugate (F.Vi 1) k ≤ F.Vi 2 :=
      conjugate_le_of_normalizes (F.monotone (by decide)) k (hL hkL)
    have he : V = F.Vi 2 := hspace.trans (sup_eq_left.mpr hkP)
    have hvcard : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [he, F.card 2 (by decide)] at hvcard
    norm_num at hvcard
  obtain ⟨l, hlL, hlC, hgen⟩ :=
    source_shifted_residual_pair d earlier hq chosen structural F g hgL hgP
  have hlfix : conjugate (conjugate (F.Vi 1) g) l = conjugate (F.Vi 1) g :=
    (conjugate_eq_iff _ _).mpr (Subgroup.centralizer_le_normalizer _ hlC)
  have hshift : conjugate (F.Vi 2) l =
      conjugate (F.Vi 1) g ⊔ conjugate (F.Vi 1) l := by
    conv_lhs => rw [hplane]
    rw [conjugate, Subgroup.map_sup]
    change conjugate (F.Vi 1) l ⊔ conjugate (conjugate (F.Vi 1) g) l = _
    rw [hlfix, sup_comm]
  have hnle : ¬ conjugate (F.Vi 1) l ≤ F.Vi 2 := by
    intro hle
    have hpg : conjugate (F.Vi 1) g ≤ F.Vi 2 := hplane ▸ le_sup_right
    have hpl : conjugate (F.Vi 2) l = F.Vi 2 :=
      eq_of_le_of_card_ge (hshift ▸ sup_le hpg hle) (by
        rw [conjugate, card_map_of_injective (MulAut.conj l⁻¹).injective])
    have hlP := (conjugate_eq_iff _ _).mp hpl
    have hR : F.orderedResidual L 1 ≤ F.Gi 2 :=
      (F.orderedResidual_le L 1).trans (by
        rw [F.orderedParabolic_one]
        exact F.P_le_G₂ (by decide) L chosen.normalizes)
    apply hnot
    conv_lhs => rw [hgen]
    exact sup_le hR (conjugate_le_of_normalizes hR l
      ((F.Gi 2).le_normalizer hlP))
  have hPV : conjugate (F.Vi 1) l ≤ V :=
    conjugate_le_of_normalizes (F.le_seed 1) l (chosen.normalizes hlL)
  have hspace' : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l := by
    obtain ⟨y, hy, hyout⟩ := Set.not_subset.mp hnle
    have hy2 : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian y (hPV hy)
    have hy1 : y ≠ 1 := fun he => hyout (he ▸ (F.Vi 2).one_mem)
    have he : zpowers y = conjugate (F.Vi 1) l := eq_of_le_of_card_ge
      (zpowers_le.mpr hy) (by
        rw [Nat.card_zpowers, orderOf_eq_prime_iff.mpr ⟨hy2, hy1⟩,
          conjugate, card_map_of_injective (MulAut.conj l⁻¹).injective]
        simpa using (F.card 1 (by decide)).le)
    symm
    apply eq_of_le_of_card_ge (sup_le (F.le_seed 2) hPV)
    rw [← he, card_sup_zpowers_of_normalizing_involution _ y hy2 hyout]
    · have hvcard : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
      norm_num [hvcard, F.card 2 (by decide)]
    · apply Subgroup.centralizer_le_normalizer _
      intro z hz
      exact congrArg Subtype.val (mul_comm' (⟨z, F.le_seed 2 hz⟩ : V) ⟨y, hPV hy⟩)
  exact ⟨g, l, hgL, hgP, hgH, hlL, hlC, hplane, hspace', hshift, hgen⟩

/-- The shifted center centralizes Z(U), as required for the actual Ke construction. -/
theorem source_shifted_center_centralizes (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) (hlL : l ∈ L)
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hgen : L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l) :
    Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ centralizer (F.ZU : Set G) := by
  have hdis := source_shifted_disjoint_of_residual_pair d earlier hq chosen structural
    alternatives F hne hseed g hgP hgH l hl hgen
  let A := Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)
  have hAH : A ≤ F.H := by
    change Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ F.H
    rw [source_shifted_center_intersection d earlier hq chosen structural alternatives F hne
      g hgP hgH l hl]
    exact inf_le_left.trans ((F.conjugate_ZU_le_X g).trans
      (F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)))
  have hAN : A ≤ normalizer (F.ZU : Set G) := hAH.trans F.H_normalizes_ZU
  have hplaneV : conjugate (F.Vi 2) l ≤ V :=
    conjugate_le_of_normalizes (F.le_seed 2) l (chosen.normalizes hlL)
  have hZN : F.ZU ≤ normalizer (conjugate (F.Vi 2) l : Set G) :=
    ((centerIn_le_centralizer F.U).trans
      (centralizer_le (hplaneV.trans (le_conjugateSpanBy V F.H)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hZGi : F.ZU ≤ conjugate (F.Gi 2) l := by
    simpa only [Gi, conjugate, map_equiv_normalizer_eq] using hZN
  have hGI := (source_ordered_residual_le_parabolic d earlier hq chosen structural alternatives F hne).2
  have hconj : conjugate (F.Gi 2) l ≤ normalizer (conjugate (F.I₂ L) l : Set G) := by
    simpa only [conjugate, map_equiv_normalizer_eq] using
      map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hGI
  have hNA : F.ZU ≤ normalizer (A : Set G) :=
    (hZGi.trans hconj).trans
      (normalizer_le_normalizer_characteristic_image _ (center (conjugate (F.I₂ L) l)))
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  exact (le_inf (le_normalizer_iff_commutator_le_right.mp hAN)
    (le_normalizer_iff_commutator_le_left.mp hNA)).trans hdis.le

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
