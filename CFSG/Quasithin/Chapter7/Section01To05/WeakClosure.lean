module

public import CFSG.Quasithin.Chapter7.Section01To05.FixedSpaceSpan

/-!
# The weak-closure deductions in §§7.3–7.5

These deductions concern the genuine parameters and automizer action of an
internal elementary abelian subgroup. E.3.28–31 supply the fundamental
inequality and its equality case; E.3.10 gives the lower bound s ≤ w + a.
The literal fixed-space bridge supplies the terminal Mathieu contradictions.

The named family deductions are conditional on their representation bounds.
They are not the source classifications 7.1.1/7.2.1, the Cartan calculation
7.3.4, or the global lower bounds 7.3.2/7.4.1. Those premises must be
constructed from Hypotheses 7.0.2 and 7.3.1 by the source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§§7.3–7.5, printed pp.698–700, and E.3.10,28–31.
-/

public section
namespace CFSG.Quasithin.Chapter7
open Subgroup Representation.BinaryOffender ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}

/-- The equality-case subgroup conclusions used in 7.5.3, with w < s explicit.
In particular the final rank is that of the actual quotient W/C_V(A). -/
theorem offender_equality_conclusions
    (hT : HypothesisE322 V T) (hFF : ¬ IsFFModule (automizerRepresentation V))
    {g : G} (hg : IsWOffenderAt V T g)
    (hs : globalW V T < globalS V)
    (heq : globalR V = globalW V T + (primeRank 2 (Automizer V) : ℕ∞)) :
    let Vg := V.map (MulAut.conj g).toMonoidHom
    let A := offenderNormalizer V g
    let W := offenderFixedSpan V g
    let U := V ⊓ centralizer (A : Set G)
    rank (inducedAutomizer V A) = primeRank 2 (Automizer V) ∧
      globalR V = (subgroupCorank Vg (A ⊓ centralizer (V : Set G)) : ℕ∞) ∧
      W ≤ V ⊓ normalizer (Vg : Set G) ∧
      globalW V T ≤ (subgroupCorank V W : ℕ∞) ∧
      U = V ⊓ centralizer (Vg : Set G) ∧
      ((subgroupCorank V W : ℕ∞) = globalW V T →
        W = V ⊓ normalizer (Vg : Set G) ∧
        IsWOffender Vg (g • T : Sylow 2 G) W ∧
        subgroupCorank W U = primeRank 2 (Automizer V)) := by
  dsimp only
  let I := inducedAutomizer V (offenderNormalizer V g)
  let _ : IsElementaryAbelian 2 I := offender_inducedAutomizer_elementary V g
  have h31 := lemma_E_3_31 hT (Or.inr hFF) hg heq
  have hpos : 0 < rank I := by
    change 0 < rank (inducedAutomizer V (offenderNormalizer V g))
    rw [h31.1.1]
    exact automizer_primeRank_pos_of_globalW_ne_top hT hg.globalW_ne_top
  have hcore := automizerDualCore_eq_fixedSpaceSpan V I hpos
  change automizerDualCore V I (rank I - 1) = offenderFixedSpan V g at hcore
  change _ ∧ _ at h31
  rw [hcore] at h31
  have hc := (offender_fixedSpaceFamily_of_lt_globalS hg hs).1
  refine ⟨h31.1.1, h31.1.2.1, h31.1.2.2, h31.2.1, hc, ?_⟩
  intro heW
  obtain ⟨_, hW, hrev, hrank⟩ := h31.2.2 heW
  refine ⟨hW, hrev, ?_⟩
  rw [rank_inducedAutomizer _ _ (hW ▸ inf_le_right)] at hrank
  have hcent : offenderFixedSpan V g ⊓
      centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) =
      V ⊓ centralizer (offenderNormalizer V g : Set G) := by
    rw [hc, hW, inf_assoc, inf_eq_right.mpr (centralizer_le_normalizer _)]
  rwa [hcent] at hrank

/-- Upper bounds on two-rank and w bound the actual global parameter r. -/
theorem fwci_upper_bound (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V)) {q w : ℕ}
    (hq : primeRank 2 (Automizer V) ≤ q) (hw : globalW V T ≤ w) :
    globalR V ≤ ((q + w : ℕ) : ℕ∞) := by
  have hq' : (primeRank 2 (Automizer V) : ℕ∞) ≤ q := by exact_mod_cast hq
  simpa only [ENat.natCast_add] using
    (lemma_E_3_29 hT (Or.inr hFF)).trans (add_le_add hq' hw)

/-- The strict numerical obstruction used in 7.5.2. -/
theorem impossible_parameter_bounds (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V)) {q w r : ℕ}
    (hq : primeRank 2 (Automizer V) ≤ q) (hw : globalW V T ≤ w)
    (hr : (r : ℕ∞) ≤ globalR V) (hbad : q + w < r) : False := by
  have hn : r ≤ q + w := by exact_mod_cast hr.trans (fwci_upper_bound hT hFF hq hw)
  omega

/-- The SU₃ row of 7.2.1 contradicts FWCI after the r bound is supplied. -/
theorem unitary_parameter_contradiction (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V)) {n : ℕ} (hn : 2 ≤ n)
    (hq : primeRank 2 (Automizer V) ≤ n + 1) (hw : globalW V T ≤ n)
    (hr : ((4 * n : ℕ) : ℕ∞) ≤ globalR V) : False :=
  impossible_parameter_bounds hT hFF hq hw hr (by omega)

/-- The Suzuki row, preserving its bound r ≥ 8n/3 without rounding. -/
theorem suzuki_parameter_contradiction (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V)) {n : ℕ} (hn : 0 < n)
    (hq : primeRank 2 (Automizer V) ≤ n) (hw : globalW V T ≤ n)
    (hr : ((8 * n : ℕ) : ℕ∞) ≤ 3 * globalR V) : False := by
  have hupper := fwci_upper_bound hT hFF hq hw
  have htriple := add_le_add (add_le_add hupper hupper) hupper
  have hr' := hr.trans (show 3 * globalR V ≤ 3 * (((n + n : ℕ) : ℕ∞)) by
    simpa only [show (3 : ℕ∞) = 1 + 1 + 1 from rfl, add_mul, one_mul] using htriple)
  have hnat : 8 * n ≤ 3 * (n + n) := by exact_mod_cast hr'
  omega

/-- The genuine triple-M₂₂ row has 5 + 2 < 8. -/
theorem triple_m22_parameter_contradiction (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hq : primeRank 2 (Automizer V) ≤ 5) (hw : globalW V T ≤ 2)
    (hr : 8 ≤ globalR V) : False :=
  impossible_parameter_bounds hT hFF hq hw hr (by decide)

/-- The natural/dual SL₃ row is excluded when its r ≥ 4n bound applies.
The source supplies that bound only outside the exceptional n = 1 case. -/
theorem natural_dual_parameter_contradiction (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V)) {n : ℕ} (hn : 0 < n)
    (hq : primeRank 2 (Automizer V) ≤ 2 * n) (hw : globalW V T ≤ n)
    (hr : ((4 * n : ℕ) : ℕ∞) ≤ globalR V) : False :=
  impossible_parameter_bounds hT hFF hq hw hr (by omega)

/-- The M₁₂/M₂₃-code rows force w = 2, m₂ = 4 and r = 6. -/
theorem mathieu_forced_parameters (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hq : primeRank 2 (Automizer V) ≤ 4) (hw : globalW V T ≤ 2)
    (hr : 6 ≤ globalR V) :
    globalW V T = 2 ∧ primeRank 2 (Automizer V) = 4 ∧ globalR V = 6 ∧
      globalR V = globalW V T + (primeRank 2 (Automizer V) : ℕ∞) := by
  have hfw := lemma_E_3_29 hT (Or.inr hFF)
  have hR : globalR V = 6 := le_antisymm (fwci_upper_bound hT hFF hq hw) hr
  have hwt : globalW V T ≠ ⊤ := ne_top_of_le_ne_top (by simp) hw
  have hcast := ENat.natCast_toNat hwt
  have hn : 6 ≤ primeRank 2 (Automizer V) + (globalW V T).toNat := by
    rw [hR, ← hcast, ← ENat.natCast_add] at hfw
    exact_mod_cast hfw
  have hwn : (globalW V T).toNat ≤ 2 := by
    rw [← hcast] at hw
    exact_mod_cast hw
  have hqeq : primeRank 2 (Automizer V) = 4 := by omega
  have hweq : globalW V T = 2 := by
    rw [← hcast, show (globalW V T).toNat = 2 by omega]
    rfl
  exact ⟨hweq, hqeq, hR, by rw [hweq, hqeq, hR]; rfl⟩


/-- The lower weak-closure bound uses the actual fixed-space family. -/
theorem globalS_le_globalW_add_localA (hT : HypothesisE322 V T) :
    globalS V ≤ globalW V T + localA V := by
  by_cases hs : globalS V ≤ globalW V T
  · exact hs.trans (le_add_of_nonneg_right bot_le)
  · have hws : globalW V T < globalS V := lt_of_not_ge hs
    have hwt : globalW V T ≠ ⊤ := ne_top_of_lt hws
    obtain ⟨g, hg⟩ := exists_isWOffenderAt_of_globalW_ne_top hT hwt
    have hf := (offender_fixedSpaceFamily_of_lt_globalS hg hws).2
    have ha : (((globalS V).toNat - (globalW V T).toNat : ℕ) : ℕ∞) ≤ localA V :=
      le_moduleA_of_mem (automizerRepresentation V) hf
    have hsn := ENat.natCast_toNat (globalS_ne_top V)
    have hwn := ENat.natCast_toNat hwt
    have hle : (globalW V T).toNat ≤ (globalS V).toNat := by
      rw [← hsn, ← hwn] at hws
      exact (ENat.natCast_lt_natCast.mp hws).le
    have he : globalS V = globalW V T +
        (((globalS V).toNat - (globalW V T).toNat : ℕ) : ℕ∞) := by
      have hsum : ((globalS V).toNat : ℕ∞) = ((globalW V T).toNat : ℕ∞) +
          (((globalS V).toNat - (globalW V T).toNat : ℕ) : ℕ∞) := by
        rw [← ENat.natCast_add, Nat.add_sub_of_le hle]
      exact hsn.symm.trans (hsum.trans (congrArg
        (fun x : ℕ∞ => x + (((globalS V).toNat - (globalW V T).toNat : ℕ) : ℕ∞)) hwn))
    exact he.trans_le (add_le_add le_rfl ha)

/-- Once r ≥ m, the lower bound in 7.3.3 follows for the actual parameters. -/
theorem localM_le_globalW_add_localA (hT : HypothesisE322 V T)
    (hr : (localM V : ℕ∞) ≤ globalR V) :
    (localM V : ℕ∞) ≤ globalW V T + localA V := by
  simpa only [globalS, min_eq_right hr] using globalS_le_globalW_add_localA hT

/-- The strict a < 2n bound excludes the Sp₄ row as in 7.3.5. -/
theorem symplectic_parameter_contradiction (hT : HypothesisE322 V T)
    (hr : (localM V : ℕ∞) ≤ globalR V) {n : ℕ}
    (hm : 3 * n ≤ localM V) (ha : localA V < ((2 * n : ℕ) : ℕ∞))
    (hw : globalW V T ≤ n) : False := by
  have hlo : ((3 * n : ℕ) : ℕ∞) ≤ globalW V T + localA V :=
    (show ((3 * n : ℕ) : ℕ∞) ≤ (localM V : ℕ∞) by exact_mod_cast hm).trans (localM_le_globalW_add_localA hT hr)
  have hhi : globalW V T + localA V < ((3 * n : ℕ) : ℕ∞) := by
    calc
      _ ≤ (n : ℕ∞) + localA V := add_le_add hw le_rfl
      _ < (n : ℕ∞) + ((2 * n : ℕ) : ℕ∞) := (ENat.add_lt_add_iff_left (by simp)).mpr ha
      _ = ((3 * n : ℕ) : ℕ∞) := by rw [← ENat.natCast_add]; congr 1; omega
  exact (not_lt_of_ge hlo) hhi

/-- The 7.5.4 M₂₃ contradiction from the H.16.8 fixed-space-span bound.
The actual parameter bounds from 7.2–7.4 remain explicit. -/
theorem m23_exclusion_of_fixedSpan_bound
    (hT : HypothesisE322 V T) (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hq : primeRank 2 (Automizer V) ≤ 4) (hw : globalW V T ≤ 2)
    (hr : 6 ≤ globalR V) (hm : 2 < localM V)
    (hspan : ∀ I : Subgroup (Automizer V), IsElementaryAbelian 2 I → rank I = 4 →
      Module.finrank (ZMod 2) (Additive V ⧸ fixedSpaceSpan (automizerRepresentation V) I) ≤ 1) :
    False := by
  obtain ⟨hweq, hqeq, hreq, heq⟩ := mathieu_forced_parameters hT hFF hq hw hr
  obtain ⟨g, hg⟩ := exists_isWOffenderAt_of_globalW_ne_top hT (by rw [hweq]; simp)
  have hs : globalW V T < globalS V := by
    rw [hweq, globalS, lt_min_iff, hreq]
    exact ⟨by decide, by exact_mod_cast hm⟩
  have hc := offender_equality_conclusions hT hFF hg hs heq
  have hI : rank (inducedAutomizer V (offenderNormalizer V g)) = 4 := hc.1.trans hqeq
  have hdim := hspan _ (offender_inducedAutomizer_elementary V g) hI
  have hlo := hc.2.2.2.1
  rw [hweq, offenderFixedSpan_corank] at hlo
  have hlo' : 2 ≤ Module.finrank (ZMod 2) (Additive V ⧸
      fixedSpaceSpan (automizerRepresentation V) (inducedAutomizer V (offenderNormalizer V g))) :=
    by exact_mod_cast hlo
  omega

/-- The 7.5.4 M₁₂ contradiction from the two H.11.1(4) dimensions.
Equal corank makes the reverse normalizer quotient have rank four, whereas
the supplied dimensions force rank at least five. -/
theorem m12_exclusion_of_fixedSpace_bounds
    (hT : HypothesisE322 V T) (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hq : primeRank 2 (Automizer V) ≤ 4) (hw : globalW V T ≤ 2)
    (hr : 6 ≤ globalR V) (hm : 2 < localM V)
    (hV : Module.finrank (ZMod 2) (Additive V) = 10)
    (hfixed : ∀ I : Subgroup (Automizer V), IsElementaryAbelian 2 I → rank I = 4 →
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) I) ≤ 3 ∧
        8 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan (automizerRepresentation V) I)) :
    False := by
  obtain ⟨hweq, hqeq, hreq, heq⟩ := mathieu_forced_parameters hT hFF hq hw hr
  obtain ⟨g, hg⟩ := exists_isWOffenderAt_of_globalW_ne_top hT (by rw [hweq]; simp)
  have hs : globalW V T < globalS V := by
    rw [hweq, globalS, lt_min_iff, hreq]
    exact ⟨by decide, by exact_mod_cast hm⟩
  have hc := offender_equality_conclusions hT hFF hg hs heq
  let I := inducedAutomizer V (offenderNormalizer V g)
  have hI : rank I = 4 := hc.1.trans hqeq
  obtain ⟨hUdim, hWdim⟩ := hfixed I (offender_inducedAutomizer_elementary V g) hI
  have hsum := (fixedSpaceSpan (automizerRepresentation V) I).finrank_quotient_add_finrank
  have hlo := hc.2.2.2.1
  have hcor : subgroupCorank V (offenderFixedSpan V g) = 2 := by
    rw [hweq, offenderFixedSpan_corank] at hlo
    have hlo' : 2 ≤ Module.finrank (ZMod 2) (Additive V ⧸
        fixedSpaceSpan (automizerRepresentation V) I) := by exact_mod_cast hlo
    rw [offenderFixedSpan_corank]
    change Module.finrank (ZMod 2) (Additive V ⧸ fixedSpaceSpan (automizerRepresentation V) I) = 2
    omega
  obtain ⟨hW, _, hquot⟩ := hc.2.2.2.2.2 (by rw [hcor, hweq]; rfl)
  have hUle : V ⊓ centralizer (offenderNormalizer V g : Set G) ≤ offenderFixedSpan V g := by
    rw [hc.2.2.2.2.1, hW]
    exact inf_le_inf_left V (centralizer_le_normalizer _)
  let _ : IsElementaryAbelian 2 (offenderFixedSpan V g) :=
    offender_elementary_of_le (offenderFixedSpan_le V g)
  rw [subgroupCorank, ← Subgroup.log_card_sub_log_card_eq_log_relIndex _ _ hUle] at hquot
  have hU : Nat.log 2 (Nat.card ↥(V ⊓ centralizer (offenderNormalizer V g : Set G))) =
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) I) := by
    rw [← ambientSubmodule_fixedSpace V _ (show offenderNormalizer V g ≤ _ from inf_le_right)]
    exact ambientSubmodule_log_card V _
  have hWlog : Nat.log 2 (Nat.card (offenderFixedSpan V g)) =
      Module.finrank (ZMod 2) (fixedSpaceSpan (automizerRepresentation V) I) :=
    ambientSubmodule_log_card V _
  rw [hU, hWlog, hqeq] at hquot
  omega


end CFSG.Quasithin.Chapter7
