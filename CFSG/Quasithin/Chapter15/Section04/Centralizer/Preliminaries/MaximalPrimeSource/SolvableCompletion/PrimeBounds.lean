module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeFive
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SolvableCompletion

/-!
# The maximal prime and source 15.4.4 without a C.2.6 premise

The proved solvable maximal-prime family supplies uniqueness and noncentrality.
The same original reduced module, literal centralizer quotient, 15.4.2(4)
application and prime extraction then give the prime-five bound and the
maximal-two-local prime restriction. Only Earlier1542 and Earlier1542Four
remain explicit earlier-source implications.
-/

noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.SolvableCompletion
open MaximalPrimeFive
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Genuine 15.4.3(4), conditional only on the preceding universal source
implications. All selected-module, quotient, kernel and ratio applicability
conditions are constructed from the original maximal-prime hypotheses. -/
public theorem source_prime_eq_five (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    (h44 : Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) :
    (pCore 2 X).index = 5 := by
  obtain ⟨hxstar, hcore, hnc, _⟩ := source_lemma_15_4_3_one_to_three T h h42 hX hp hmax
  obtain ⟨M, ⟨hM, hXM⟩, huniq⟩ := hxstar.2
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hXM
  have he : M ∈ Chapter1.He G :=
    Chapter1.mem_He_iff.mpr (h.simpleQTKE.evenCharacteristic T M hM hTM)
  have hc : X.pCoreIn 2 ≤ M.pCoreIn 2 := (hcore M hM hXM).2
  let H := sourceGroup (T : Subgroup G) X
  let W := sourceModule (T : Subgroup G) X
  have hred : IsPReduced 2 W := sourceModule_reduced T hX hXM hc he hnc
  let : IsElementaryAbelian 2 W := hred.elementary
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let P := (X.subgroupOf H).map q
  let ρ := Representation.NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hq : cubicRatio ρ ≤ 2 := h44 T h H M hX.2.2.1 hM hXM
    (fun N hN hHN => huniq N ⟨hN, hHN⟩) W hred
    (source_kernel_identity T hX hXM hc he hnc).2
    (sourceModule_core_and_elementary T hXM he).1
  obtain ⟨hP, hnP, hCP, _⟩ := source_prime_image T hX hXM hc he hnc
  let : P.Normal := hnP
  have hfaith : Function.Injective ρ :=
    Representation.NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hf := prime_three_or_five_of_cubicRatio hX.2.2.2.1 (by omega) P hP hCP.le ρ hfaith hq
  exact hf.resolve_left (by omega)

/-- The complete maximal-prime source family 15.4.3(1–4). The final clause
uses the actual source action; no prime-five conclusion is an input. -/
public theorem source_lemma_15_4_3 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    (h44 : Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) :
    X ∈ XiStar (T : Subgroup G) ∧
    (∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M →
      X ≤ twoPrimePreimage (pCore 2 X).index M ∧ X.pCoreIn 2 ≤ M.pCoreIn 2) ∧
    (¬ X ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) ∧
    ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), X⁆ ≠ ⊥ ∧
    (pCore 2 X).index = 5 := by
  obtain ⟨ha, hb, hc, hd⟩ := source_lemma_15_4_3_one_to_three T h h42 hX hp hmax
  exact ⟨ha, hb, hc, hd, source_prime_eq_five T h h42 h44 hX hp hmax⟩
/-- Actual 15.4.4 application: every maximal two-local overgroup of the
original Sylow subgroup has prime divisors only two, three and five. -/
public theorem source_maximal_twoLocal_prime_divisors
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    (h44 : Earlier1542Four (G := G)) :
    ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3 ∨ p = 5 := by
  apply PrimeExtraction.maximal_twoLocal_prime_divisors_of_earlier_source h.simpleQTKE T
    (h42 T h).solvable (fun X hX => ((h42 T h).uppercase X hX).2.2.2)
  intro X hX hm hp
  exact source_prime_eq_five T h h42 h44 hX hp hm

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.SolvableCompletion
