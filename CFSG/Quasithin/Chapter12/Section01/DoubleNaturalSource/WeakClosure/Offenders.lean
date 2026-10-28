module

public import CFSG.Quasithin.ChapterE.Section03.Offenders

/-!
# The actual conjugate configuration in the doubled-orbit argument

A finite weak-closure minimum is attained by a noncentralizing conjugate.
E.3.28 bounds its action-image rank and the reverse-normalizer corank;
E.3.32 places every permitted generated core inside that proper normalizer.
The integer form uses a finite lower bound for r and never truncates infinity.

This reduction supplies the inputs to the separate natural-plus-dual geometry
in 12.1.8 and 12.1.10. It does not assert either weak-closure conclusion.
Source: Aschbacher--Smith, E.3.28,32 and 12.1.8,10, pp.237--238,792--794.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G}
  [IsElementaryAbelian 2 W] {T : Sylow 2 G}

/-- The geometric consequences of an actual minimizing conjugate. Every group,
automizer, and generated core here uses its literal ambient action. -/
structure ConjugateConfiguration (W : Subgroup G) (g : G) (j r : ℕ) : Prop where
  noncentralizing : ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥
  corank : subgroupCorank (W.map (MulAut.conj g).toMonoidHom) (offenderNormalizer W g) = j
  not_normalized : ¬ W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)
  not_normalizes : ¬ W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G)
  rank_lower : r - j ≤ rank (inducedAutomizer W (offenderNormalizer W g))
  reverse_corank : j ≤ subgroupCorank W
    (W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
  core_le : ∀ k : ℕ, j + k < r →
    automizerDualCore W (inducedAutomizer W (offenderNormalizer W g)) k ≤
      W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)

/-- E.3.28 and E.3.32 with a finite lower bound on r. No subtraction of
infinity or assumed W₁/W₂ centralization enters this reduction. -/
theorem conjugateConfiguration (hT : HypothesisE322 W T) {g : G}
    (hg : IsWOffenderAt W T g) {j r : ℕ} (hw : globalW W T = j)
    (hj : 0 < j) (hjr : j < r) (hr : (r : ℕ∞) ≤ globalR W) :
    ConjugateConfiguration W g j r := by
  have hwpos : 0 < globalW W T := by rw [hw]; exact_mod_cast hj
  have hwr : globalW W T < globalR W := by
    rw [hw]
    exact lt_of_lt_of_le (by exact_mod_cast hjr) hr
  have h28 := lemma_E_3_28 hT (Or.inl hwpos) hg
  have hc : subgroupCorank (W.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer W g) = j := by exact_mod_cast hg.2.symm.trans hw
  refine ⟨hg.1, hc, h28.2.2.2.1, h28.2.2.2.2 hwpos, ?_, ?_, ?_⟩
  · have hb := hr.trans h28.2.1.1
    rw [hw, ← ENat.natCast_add] at hb
    have hb' : r ≤ j + rank (inducedAutomizer W (offenderNormalizer W g)) := by
      exact_mod_cast hb
    omega
  · have hb := hg.le_reverse_normalizer_corank hT hwr
    rw [hw] at hb
    exact_mod_cast hb
  · intro k hk
    apply automizerDualCore_le_conjugate_normalizer
    rw [hc, ← ENat.natCast_add]
    exact lt_of_lt_of_le (by exact_mod_cast hk) hr

/-- Failure of a strict natural-number bound realizes that exact value when
the preceding bound is already known. -/
theorem exists_configuration (hT : HypothesisE322 W T) {j r : ℕ}
    (hj : 0 < j) (hprev : ((j - 1 : ℕ) : ℕ∞) < globalW W T)
    (hfail : ¬ (j : ℕ∞) < globalW W T)
    (hjr : j < r) (hr : (r : ℕ∞) ≤ globalR W) :
    ∃ g : G, IsWOffenderAt W T g ∧ globalW W T = j ∧
      ConjugateConfiguration W g j r := by
  have hle : globalW W T ≤ (j : ℕ∞) := le_of_not_gt hfail
  have hfin : globalW W T ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  have hnat : (globalW W T).toNat = j := by
    rw [← ENat.natCast_toNat hfin] at hprev hle
    have hp : j - 1 < (globalW W T).toNat := by exact_mod_cast hprev
    have hl : (globalW W T).toNat ≤ j := by exact_mod_cast hle
    omega
  have hw : globalW W T = j := (ENat.natCast_toNat hfin).symm.trans (by rw [hnat])
  obtain ⟨g, hg⟩ := exists_isWOffenderAt_of_globalW_eq_nat hT hw
  exact ⟨g, hg, hw, conjugateConfiguration hT hg hw hj hjr hr⟩

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
variable {G : Type*} [Group G] {W : Subgroup G} {g : G} {j r : ℕ}

/-- The E.3.32 core is a proper subgroup of the original orbit. -/
theorem ConjugateConfiguration.core_ne_orbit (C : ConjugateConfiguration W g j r)
    {k : ℕ} (hk : j + k < r) :
    automizerDualCore W (inducedAutomizer W (offenderNormalizer W g)) k ≠ W := by
  intro he
  have hle := C.core_le k hk
  rw [he] at hle
  exact C.not_normalized (hle.trans inf_le_right)

/-- The reverse-normalizer corank also bounds every contained dual core.
This is the numerical contradiction used in the degree-four second stage. -/
theorem ConjugateConfiguration.corank_core_ge [Finite G] [IsElementaryAbelian 2 W]
    (C : ConjugateConfiguration W g j r) {k : ℕ} (hk : j + k < r) :
    j ≤ subgroupCorank W
      (automizerDualCore W (inducedAutomizer W (offenderNormalizer W g)) k) := by
  have ha := offender_corank_add (C.core_le k hk)
    (show W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G) ≤ W from inf_le_left)
  have hb := C.reverse_corank
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
