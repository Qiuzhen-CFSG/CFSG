module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.PrimeExtraction
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeFive.SourceAction
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeFive.SmallRatio

/-!
# The original maximal prime is five

This applies genuine 15.4.3(1–3), constructs the original elementary reduced
module V=⟨Ω₁Z(T)^X⟩ and its exact centralizer quotient, and proves every
applicability condition of 15.4.2(4). The small-involution witness and the
proved D.2.11 support bound then force the maximal odd prime to be five.

`Earlier1542Four` is the separate universal earlier-source theorem, not a
conclusion about the selected X. It remains with the original centralizer
and prime-reduction owners, together with `Earlier1542` and `EarlierC26`.
The final theorem assumes neither reducedness, an action model, nor a ratio
bound for the selected action.

Source: Aschbacher–Smith, printed pp.1156–1157, 15.4.2(4) and 15.4.3(4).
-/
noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeFive
open MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The complete, separate earlier 15.4.2(4) implication for the literal
centralizer quotient. Its proof is retained with the original source owners;
15.4.2(1–3), recorded by `Earlier1542`, do not assert this clause. -/
@[expose] public def Earlier1542Four : Prop :=
  ∀ (T : Sylow 2 G), SourceHypotheses T →
  ∀ (M₀ M : Subgroup G), M₀ ∈ Chapter1.HOver G (T : Set G) →
    IsMaximalTwoLocal M → M₀ ≤ M →
    (∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M) →
  ∀ (V : Subgroup M₀) (hV : IsPReduced 2 V),
    let := hV.normal
    let := hV.elementary
    (T : Subgroup G).subgroupOf M₀ ⊓ centralizer (V : Set M₀) =
      (centralizer (V : Set M₀)).pCoreIn 2 →
    V.map M₀.subtype ≤ M.pCoreIn 2 →
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2

/-- Genuine 15.4.3(4), conditional only on the preceding universal source
implications. All selected-module, quotient, kernel and ratio applicability
conditions are constructed from the original maximal-prime hypotheses. -/
public theorem source_prime_eq_five (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) :
    (pCore 2 X).index = 5 := by
  obtain ⟨hxstar, hcore, hnc, _⟩ := source_lemma_15_4_3_one_to_three T h h42 h26 hX hp hmax
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
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
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
  obtain ⟨ha, hb, hc, hd⟩ := source_lemma_15_4_3_one_to_three T h h42 h26 hX hp hmax
  exact ⟨ha, hb, hc, hd, source_prime_eq_five T h h42 h26 h44 hX hp hmax⟩
/-- Actual 15.4.4 application: every maximal two-local overgroup of the
original Sylow subgroup has prime divisors only two, three and five. -/
public theorem source_maximal_twoLocal_prime_divisors
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G)) :
    ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3 ∨ p = 5 := by
  apply PrimeExtraction.maximal_twoLocal_prime_divisors_of_earlier_source h.simpleQTKE T
    (h42 T h).solvable (fun X hX => ((h42 T h).uppercase X hX).2.2.2)
  intro X hX hm hp
  exact source_prime_eq_five T h h42 h26 h44 hX hp hm

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeFive
