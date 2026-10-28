module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Terminal
public import CFSG.Quasithin.ChapterG.Section10.FittingSource
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.SourceCubic
public import Theory.LinearAlgebra.QuadraticForm.BinarySixSingular
public import Theory.Representation.NormalInvariants

/-!
# Excluding solvable actors in the original large extraspecial branch

G.10 makes the actual terminal action irreducible above degree four.
The solved solvable G.9 cases then leave only degree six with an elementary
actor of rank two. The exact G.10 rank equation forces the source intersection
to be a singular three-space. Its quadratic form consequently has 36 zeros.

The degree-six Fitting theorem constructs a normal cubic subgroup. Faithful
irreducibility makes that subgroup fixed-free, so its action on the zeros of
the same invariant form forces their count to be 1 modulo 3, a contradiction.
The square form, terminal hypothesis, irreducibility and SQTK cover are all
constructed from the original counterexample and flag. No local model
classification or further geometry premise is assumed.

The final transport gives nonsolvability of the literal H/O₂(H) used by
14.4.2 and the subsequent marked model branches. Exhaustion of those
nonsolvable branches remains with this large-case source owner.

Source: Aschbacher--Smith, 14.4.2, printed p.1006; G.9.4 and G.10.4--5,
printed pp.354--355,358--359.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
universe u v

private theorem false_of_solvable_large_quadratic
    {A : Type u} [Group A] [Finite A]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) A W} {B : LinearMap.BilinForm (ZMod 2) W}
    {v : W} {E : Submodule (ZMod 2) W} {X : Subgroup A}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple A))
    (hs : Group.IsSolvable A) (hi : IsIrreducible ρ)
    (hd : 4 < finrank (ZMod 2) W)
    (q : QuadraticForm (ZMod 2) W) (hq : q.polarBilin.Nondegenerate)
    (hqs : ∀ e ∈ E, q e = 0) (hqi : ∀ a w, q (ρ a w) = q w) : False := by
  let := hi
  have hX : X ≠ ⊥ := by
    intro he
    have hb := h.dimension_bound.1
    have hr : Group.rank (X ⧸ X₀) ≤ Group.rank X :=
      Group.rank_le_of_surjective (QuotientGroup.mk' X₀) (QuotientGroup.mk'_surjective X₀)
    have hz : Group.rank X = 0 := by rw [he]; exact Group.rank_eq_zero _
    omega
  have h6 : finrank (ZMod 2) (Additive X) = 2 ∧ finrank (ZMod 2) W = 6 := by
    rcases h.solvable_irreducible_cases cover hs hi hX with h1 | h2 | h3 | h4 | h6
    · have := h1.2.1; omega
    · have := h2.2.1; omega
    · have := h3.2.1; omega
    · have := h4.2.1; omega
    · exact h6
  have hr := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
  have he : finrank (ZMod 2) E = 3 := by
    have heq := h.dimension
    have hb := B.twice_finrank_le_of_isotropic h.nondegenerate E h.isotropic
    omega
  let d := h.fittingHypothesis_of_solvable cover hs hi
  have d2 : ChapterG.Section09.FittingHypothesis KnownSimple.IsKnownSimple ρ X 2 := h6.1 ▸ d
  have hc : IsPGroup 3 (⁅fittingSubgroup A, X⁆ : Subgroup A) := by
    by_contra hn
    have hb := (ChapterG.Section09.FittingRecognition.caseTwo_from_source d2 (by decide) hn).1
    omega
  obtain ⟨C, hCn, hCc⟩ :=
    ChapterG.Section09.FittingRecognition.Six.normal_cubic_of_source_degree_six d2 hc h6.2
  let := hCn
  have hfix : Representation.invariants (ρ.comp C.subtype) = ⊥ := by
    by_contra hn
    have hk := le_ker_of_normal_invariants_ne_bot ρ C hn
    have hbot : C = ⊥ := bot_unique (hk.trans_eq ((MonoidHom.ker_eq_bot_iff ρ).mpr h.faithful))
    simp [hbot] at hCc
  exact QuadraticForm.BinarySix.false_of_fixed_free_cubic (ρ.comp C.subtype) hCc hfix
    q hq h6.2 E he hqs (fun c w => hqi c w)

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original large extraspecial source has a nonsolvable dotted actor.
This removes the solvable G.11 branch without an assumed model catalogue. -/
theorem source_large_terminal_not_solvable (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U) :
    ¬ Group.IsSolvable F.TerminalHdot := by
  let := chosen.elementary
  let c := source_closure_geometry F d earlier hq chosen structural alternatives hne
  let := F.uhat_elementary_of_point (by decide) c.two c.frattini_point
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_, heX, B, v, hyp⟩ :=
    source_terminal_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hirr := source_large_terminal_irreducible F d earlier hq chosen structural alternatives hne hZ hlarge
  let q := F.uhatQuadraticForm (by decide) c.two c.frattini_point
    (center_frattini_bot_of_center_point F c hZ)
  obtain ⟨hqs, hqi, hqn⟩ := quadratic_intersection_of_center_point F c (by decide) hZ g
    (disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L chosen.normalizes
      c.seed_center g hgP hgH).1)
  have hterminal (a : F.TerminalHdot) (w : Additive F.Uhat) :
      q (F.terminalRepresentation a w) = q w := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hqi a w.toMul
  have hdim : 4 < finrank (ZMod 2) (Additive F.Uhat) := by
    have hcenter := (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1.center_order_p
    have hcard : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
      rw [card_eq_card_quotient_mul_card_subgroup (center F.U), hcenter]
      change Nat.card (Additive F.Uhat) * 2 = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, pow_succ]
    by_contra hh
    have hb := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 5)
    rw [← hcard] at hb
    norm_num at hb
    omega
  intro hs
  exact false_of_solvable_large_quadratic hyp (source_terminal_cover F d chosen)
    hs hirr hdim q hqn hqs hterminal

/-- The same exclusion on the literal H/O₂(H) quotient used by 14.4.2
and every marked-model branch. -/
theorem source_large_core_quotient_not_solvable (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U) :
    ¬ Group.IsSolvable (F.H ⧸ pCore 2 F.H) := by
  let := chosen.elementary
  let c := source_closure_geometry F d earlier hq chosen structural alternatives hne
  let e := terminalStarEquiv_of_center_point F c hZ
  intro hs
  let := hs
  exact source_large_terminal_not_solvable d earlier hq chosen structural alternatives F hne hZ hlarge
    (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
