module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Local
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Maximal
public import Theory.GroupAction.ElementaryTwoOddHyperplane

/-!
# Odd cores of escaping centralizers

E.6.9(2) produces a hyperplane A of V containing U such that C_{O(H)}(A)
escapes M, where H = C_G(U), and concludes r(G,V) = 1. The odd core is formed
inside H and embedded into G through H's subtype homomorphism.

Normality of O(H) and V ≤ H give the conjugation action of V on O(H).
E.6.9(1), together with C_G(V) ≤ M, makes its full fixed subgroup trivial.
Coprime fixed-point generation then supplies the hyperplane containing U.
For maximal escaping U of corank greater than one, that hyperplane strictly
contains U, contradicting maximality. This proves O(H) = 1 at the start of
E.6.11.

The earlier Chapter 1 inputs are exactly `EarlierLocalFacts`, as in E.6.9(1).
Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.9(2) and the
opening of E.6.11, printed pp.248–249 (PDF pp.259–260).
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}

/-- E.6.9(2): a nonidentity odd core gives an escaping hyperplane containing U
and forces the global weak-closure parameter to be one. -/
theorem HypothesisE61.lemma_E_6_9_2
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hodd : pPrimeCore 2 (centralizer (U : Set G)) ≠ ⊥) :
    ∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ subgroupCorank V A = 1 ∧
      ¬ (pPrimeCore 2 (centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ⊓ centralizer (A : Set G) ≤ M ∧
      globalR V = 1 := by
  let _ := h.elementary
  let H := centralizer (U : Set G)
  let R := (pPrimeCore 2 H).map H.subtype
  have hRM : R ⊓ M = ⊥ := h.lemma_E_6_9_1 earlier hU
  have hHR : H ≤ normalizer (R : Set G) := by
    have hN := (pPrimeCore 2 H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] using hN
  have hVR : V ≤ normalizer (R : Set G) :=
    (V.le_centralizer.trans (Subgroup.centralizer_le hU.1)).trans hHR
  have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right ((pPrimeCore 2 H).card_map_dvd H.subtype)
      pPrimeCore_coprime_card)
  have hRne : R ≠ ⊥ := fun he =>
    hodd ((map_eq_bot_iff_of_injective (pPrimeCore 2 H) H.subtype_injective).mp he)
  have hfix : R ⊓ centralizer (V : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left R h.centralizer_le).trans hRM.le)
  obtain ⟨A, hUA, hAV, hindex, hnon⟩ :=
    exists_hyperplane_containing_of_odd_centralizer V R U hVR hRodd hRne hU.1
      (map_subtype_le _) hfix
  have hcor : subgroupCorank V A = 1 := by
    rw [subgroupCorank, hindex]
    decide
  have he : ¬ R ⊓ centralizer (A : Set G) ≤ M := by
    intro hle
    exact hnon (le_bot_iff.mp ((le_inf inf_le_left hle).trans hRM.le))
  exact ⟨A, hUA, hAV, hcor, he,
    globalR_eq_one_of_hyperplane h.normalizer_le hAV hcor
      (fun hle => he (inf_le_right.trans hle))⟩

/-- The first deduction in E.6.11: maximal escape of corank greater than one
forces the intrinsic odd core of C_G(U) to be trivial. The maximality hypothesis
is the interface supplied by `exists_maximal_escape`. -/
theorem HypothesisE61.oddCore_eq_bot_of_maximal_escape
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → centralizer (W : Set G) ≤ M)
    (hn : 1 < subgroupCorank V U) :
    pPrimeCore 2 (centralizer (U : Set G)) = ⊥ := by
  by_contra hodd
  obtain ⟨A, hUA, hAV, hcor, he, _⟩ := h.lemma_E_6_9_2 earlier hU hodd
  have hlt : U < A := lt_of_le_of_ne hUA (by
    intro heq
    rw [heq, hcor] at hn
    exact (lt_irrefl 1) hn)
  exact he (inf_le_right.trans (hmax A hlt hAV))

end CFSG.Quasithin.ChapterE.Section06
