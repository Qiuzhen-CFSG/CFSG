module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SourceInputs
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.Normalizers
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SolvableActions
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.FittingCore

/-!
# Maximal-prime core containment and source inputs for 15.4.3

The original Hypothesis 15.4.1 and complete earlier 15.4.2(1–3) implication
are retained with the full known-simple catalogue. Clause (2) is proved:
every maximal two-local M containing XT satisfies X ≤ O₂,p(M), with
O₂(X) ≤ O₂(M). The proof combines noncircular prime comparison, both local
automorphism calculations with their prime-group kernels, and the
Fitting-centralizer argument on the literal quotient M/O₂(M).

Containment in an iterated core is not used to assert normality of X in M.
The later source-family completion uses the normalizer setup and the exact
universal C.2.6 parameter for uniqueness and noncentrality. The parent owns
final earlier-source discharge and the independent 15.4.3(4) argument.

Source: Aschbacher–Smith, combined manuscript, printed pp.1155–1157.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
variable {G : Type*} [Group G] [Finite G]

/-- The prime comparison under all original source boundary clauses. -/
theorem source_prime_bound (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M)
    (q : ℕ) (hq : q.Prime) (ho : Odd q) (hd : q ∣ Nat.card M) :
    q ≤ (pCore 2 X).index :=
  maximal_twoLocal_odd_prime_le h.simpleQTKE T (h42 T h).solvable
    (fun Y hY => ((h42 T h).uppercase Y hY).2.2.2) hX hp hmax hM hXM q hq ho hd

/-- Other-prime cores in M/O₂(M) are centralized by the selected original X. -/
theorem source_other_prime_core_centralization (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M)
    (q : ℕ) (hq : q.Prime) (ho : Odd q) (hne : q ≠ (pCore 2 X).index) :
    quotientImage M X ≤ centralizer (pCore q (M ⧸ pCore 2 M) : Set (M ⧸ pCore 2 M)) :=
  xi_centralizes_other_prime_core h.simpleQTKE T (h42 T h).solvable
    (fun Y hY => ((h42 T h).uppercase Y hY).2.2.2) hX hp hmax hM hXM q hq ho hne

/-- The defining-prime calculation on the actual p-core of M/O₂(M),
with the original actor and literal conjugation map. -/
theorem source_defining_prime_core_action (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    let p := (pCore 2 X).index
    let P := pCore p (M ⧸ pCore 2 M)
    let a : X →* MulAut P := MulAut.conjNormal.comp
      ((QuotientGroup.mk' (pCore 2 M)).comp (inclusion (le_sup_left.trans hXM)))
    IsPGroup p a.range := by
  dsimp only
  let : Fact (pCore 2 X).index.Prime := ⟨hX.2.2.2.1⟩
  have hr : primeRank (pCore 2 X).index (pCore (pCore 2 X).index (M ⧸ pCore 2 M)) ≤ 2 :=
    (primeRank_subgroup_le _ _).trans
      ((primeRank_quotient_le_of_isTwoGroup _ hX.2.2.2.2 (pCore 2 M) pCore_isPGroup).trans
        ((h.simpleQTKE.twoLocal_sqtk hM.1).stronglyQuasithin _ hX.2.2.2.1 hX.2.2.2.2))
  exact xi_defining_prime_action_isPGroup hX (le_sup_left.trans hXM)
    ((h42 T h).solvable M hM (le_sup_right.trans hXM)) hp pCore_isPGroup hr _

/-- The actual X-action lies in the p-core of the full M*-action on
O_p(M*). This uses p-closedness of the whole solvable automorphism image,
not just the fact that the X-action is a p-group. -/
theorem source_defining_prime_action_le_core (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    let p := (pCore 2 X).index
    let Q := M ⧸ pCore 2 M
    let P := pCore p Q
    let rho : Q →* MulAut P := MulAut.conjNormal
    let a : X →* MulAut P := rho.comp
      ((QuotientGroup.mk' (pCore 2 M)).comp (inclusion (le_sup_left.trans hXM)))
    a.range ≤ (pCore p rho.range).map rho.range.subtype := by
  dsimp only
  let p := (pCore 2 X).index
  let : Fact p.Prime := ⟨hX.2.2.2.1⟩
  let Q := M ⧸ pCore 2 M
  let P := pCore p Q
  let rho : Q →* MulAut P := MulAut.conjNormal
  let a : X →* MulAut P := rho.comp
    ((QuotientGroup.mk' (pCore 2 M)).comp (inclusion (le_sup_left.trans hXM)))
  have ha : IsPGroup p a.range := source_defining_prime_core_action T h h42 hX hp hM hXM
  have hle : a.range ≤ rho.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨QuotientGroup.mk' (pCore 2 M) (inclusion (le_sup_left.trans hXM) x), rfl⟩
  let : Group.IsSolvable M := (h42 T h).solvable M hM (le_sup_right.trans hXM)
  have hs : Group.IsSolvable rho.range := Group.isSolvable_of_surjective rho.rangeRestrict_surjective
  have hr : primeRank p P ≤ 2 := (primeRank_subgroup_le p P).trans
    ((primeRank_quotient_le_of_isTwoGroup p hX.2.2.2.2 (pCore 2 M) pCore_isPGroup).trans
      ((h.simpleQTKE.twoLocal_sqtk hM.1).stronglyQuasithin p hX.2.2.2.1 hX.2.2.2.2))
  have hc := solvable_small_rank_pGroup_le_core hp pCore_isPGroup hr rho.range hs
    (a.range.subgroupOf rho.range) ha.comap_subtype
  have hm := map_mono (f := rho.range.subtype) hc
  simpa only [map_subgroupOf_eq_of_le hle] using hm
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
variable {G : Type*} [Group G] [Finite G]

/-- Clause 15.4.3(2), for every maximal two-local overgroup of XT, on the
literal quotient. The source hypotheses are unchanged. -/
theorem source_quotient_image_le_core (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    quotientImage M X ≤ pCore (pCore 2 X).index (M ⧸ pCore 2 M) := by
  let p := (pCore 2 X).index
  let : Fact p.Prime := ⟨hX.2.2.2.1⟩
  let Q := M ⧸ pCore 2 M
  let f : X →* Q := (QuotientGroup.mk' (pCore 2 M)).comp
    (inclusion (le_sup_left.trans hXM))
  have hf : f.range = quotientImage M X := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.val, (le_sup_left.trans hXM) x.property⟩, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.val, hx⟩, rfl⟩
  have h2 : pCore 2 Q = ⊥ := pCore_quotient_pCore_eq_bot 2
  have hc (q : ℕ) (hq : q.Prime) (hne : q ≠ p) :
      quotientImage M X ≤ centralizer (pCore q Q : Set Q) := by
    rcases hq.eq_two_or_odd with rfl | ho
    · rw [h2]
      intro x hx y hy
      have he : y = 1 := hy
      simp [he]
    · exact source_other_prime_core_centralization T h h42 hX hp hmax hM hXM q hq (Nat.odd_iff.mpr ho) hne
  let : Group.IsSolvable M := (h42 T h).solvable M hM (le_sup_right.trans hXM)
  have hF : quotientImage M X ≤ fittingSubgroup Q := by
    apply le_fitting_of_other_core_centralization (p := p) inferInstance _ hc
    rw [← hf, MonoidHom.map_range]
    exact source_defining_prime_action_le_core T h h42 hX hp hM hXM
  apply le_pCore_of_fitting_and_prime_support h2 hF
  intro q hq hd
  rw [← hf] at hd
  exact xi_prime_support hX q hq (hd.trans (card_range_dvd f))

/-- The iterated-core containment and its two-core consequence, with all
clauses of the original earlier 15.4.2(1–3) retained at the boundary. -/
theorem source_iterated_core_containment (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    X ≤ twoPrimePreimage (pCore 2 X).index M ∧ X.pCoreIn 2 ≤ M.pCoreIn 2 := by
  let : Fact (pCore 2 X).index.Prime := ⟨hX.2.2.2.1⟩
  have hc := (le_twoPrimePreimage_iff (pCore 2 X).index (le_sup_left.trans hXM)).mpr
    (source_quotient_image_le_core T h h42 hX hp hmax hM hXM)
  exact ⟨hc, twoCore_le_of_le_twoPrimePreimage hX.2.2.2.2 hc⟩
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
