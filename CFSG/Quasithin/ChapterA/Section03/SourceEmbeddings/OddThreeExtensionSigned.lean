module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionProjectiveModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionProjectiveKernel
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionUnitary
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The signed ternary nonquasisimple extension

The full Sylow normalizes the actual elementary Fitting kernel. In the
unitary case its order q² contradicts the defining-Sylow product theorem.
Consequently the nonquasisimple branch is linear and has the actual
q²-by-SL₂(q) extension asserted in A.3.12(10).

Source: Aschbacher--Smith A.3.12(10),A.3.21, pp.47,55--56.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels

theorem odd_three_local_signed_extension
    {A : Type*} [Group A] [Finite A] {κ : GroupClass} (hA : IsSQTK κ A)
    {q : ℕ} [Fact q.Prime] (ho : Odd q)
    (S : Sylow 2 A) {B : Subgroup A} (hB : B ∈ localCComponents S)
    (hnS : (S : Subgroup A) ≤ normalizer (B : Set A))
    (hn : ¬ IsQuasisimple (B ⧸ pCore 2 B))
    (unitary : Bool) (hm : IsPSLSign A unitary 3 q ∨ IsSLSign A unitary 3 q) :
    3 < q ∧ unitary = false ∧ ElementaryModel q 2 (fittingSubgroup B) ∧
      HasExtension B (ElementaryModel q 2) (fun X _ => IsSL X 2 q) := by
  obtain ⟨r,H,_,_,hR,f,hf,hc,h3⟩ := odd_three_cubic_carrier ho unitary hm
  obtain ⟨hq,hel,hext⟩ := rankThree_cubic_local_extension hA ho hR f hf hc h3
    (odd_three_two_rank ho unitary hm) S hB hnS hn unitary hm
  refine ⟨hq,?_,hel,hext⟩
  cases unitary
  · rfl
  · exfalso
    let U := (fittingSubgroup B).map B.subtype
    have hU : Nat.card U = q^2 := by
      rw [card_map_of_injective B.subtype_injective,Nat.card_congr hel.some.toEquiv]
      change Nat.card (Fin 2 → ZMod q) = q^2
      rw [Nat.card_fun,Nat.card_zmod,Nat.card_fin]
    have hSU : (S : Subgroup A) ≤ normalizer (U : Set A) :=
      hnS.trans (normalizer_le_normalizer_characteristic_image B (fittingSubgroup B))
    rcases hm with hh | hh
    · exact not_psu_of_normalized_prime_square ho hq S U hU hSU hh
    · exact not_su_of_normalized_prime_square ho hq S U hU hSU hh

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
