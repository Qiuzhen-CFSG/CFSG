module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.Transport
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.ElementaryFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.NormalizerFusion

/-!
# Ambient class distributions from involution normalizers

The local coordinate classes are merged only after proving that their images
are ambient conjugates. The seven target classes are distinct by element
orders and the unequal centralizer orders of the two order-four classes.
The finite certificates then count each fiber, and Sylow conjugacy transports
the second count to the original Sylow subgroup.

The normalizer of `E` supplies the two last order-four fusion inputs.
Combining them with the given involution and order-three fusion proves both
distributions from `InvolutionNormalizerData` and order-three fusion.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 5, pp.8–10, and Lemma 13, p.14.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII.Distribution
universe u
variable {G : Type u} [Group G] [Finite G]
variable (D : LocalData G) (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
private theorem conj_order {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hy : (MulAut.conj g) x = y := hg
  rw [← hy]
  exact ((MulAut.conj g).orderOf_eq x).symm

/-- The seven displayed ambient classes are pairwise distinct. -/
public theorem representative_class_injective {i j : Fin 7}
    (h : IsConj (into D k (classRepresentative i))
      (into D k (classRepresentative j))) : i = j := by
  have ho := conj_order h
  simp only [orderOf_injective (into D k) (into_injective D k),
    classRepresentative_order] at ho
  have hf : ∀ i j : Fin 7, ![1, 2, 3, 4, 4, 6, 8] i = ![1, 2, 3, 4, 4, 6, 8] j →
      i = j ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) := by decide
  rcases hf i j ho with hij | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hij
  · exact False.elim (four_not_fused D k h)
  · exact False.elim (four_not_fused D k h.symm)

private theorem localRepresentative_fusion
    (h2 : ∀ x : G, orderOf x = 2 → IsConj x D.z)
    (hthree : ∀ x : G, orderOf x = 3 → IsConj x (into D k c))
    (hza : IsConj (into D k (z 1 * a)) (into D k (z 1 * d)))
    (swap : Bool)
    (h14 : IsConj (into D k (z 3 * d))
      (into D k (classRepresentative (if swap then 4 else 3))))
    (h15 : IsConj (into D k (z 1 * z 3 * d))
      (into D k (classRepresentative (if swap then 3 else 4)))) :
    ∀ i : Fin 17, IsConj (into D k (localRepresentative i))
      (into D k (classRepresentative (mergedClass swap i))) := by
  have ho (i : Fin 17) : orderOf (into D k (localRepresentative i)) =
      ![1, 2, 2, 2, 2, 2, 3, 6, 6, 6, 4, 4, 4, 4, 4, 4, 8] i := by
    rw [orderOf_injective (into D k) (into_injective D k), localRepresentative_order]
  have hinv (i : Fin 17) (hi : orderOf (into D k (localRepresentative i)) = 2) :
      IsConj (into D k (localRepresentative i)) (into D k (z 0)) := by
    rw [into_z_zero D k]
    exact h2 _ hi
  intro i
  fin_cases i
  · exact IsConj.refl _
  · exact IsConj.refl _
  · exact hinv 2 (ho 2)
  · exact hinv 3 (ho 3)
  · exact hinv 4 (ho 4)
  · exact hinv 5 (ho 5)
  · exact hthree _ (ho 6)
  · exact IsConj.refl _
  · exact six_fusion D k h2 _ (ho 8)
  · exact six_fusion D k h2 _ (ho 9)
  · exact IsConj.refl _
  · exact hza
  · exact bd_fusion D k h2
  · exact IsConj.refl _
  · exact h14
  · exact h15
  · exact IsConj.refl _

/-- The last two order-four classes receive opposite labels. Together with
`z 1 * a` fusion this specifies every ambient class in the centralizer. -/
public theorem exists_merged_fusion
    (h2 : ∀ x : G, orderOf x = 2 → IsConj x D.z)
    (hthree : ∀ x : G, orderOf x = 3 → IsConj x (into D k c))
    (hza : IsConj (into D k (z 1 * a)) (into D k (z 1 * d)))
    (hpair : ¬ IsConj (into D k (z 3 * d)) (into D k (z 1 * z 3 * d))) :
    ∃ swap : Bool, ∀ x : TwistedModel, IsConj (into D k x)
      (into D k (classRepresentative (mergedClass swap (localClass x)))) := by
  have h14o : orderOf (into D k (z 3 * d)) = 4 := by
    rw [orderOf_injective (into D k) (into_injective D k)]
    exact localRepresentative_order 14
  have h15o : orderOf (into D k (z 1 * z 3 * d)) = 4 := by
    rw [orderOf_injective (into D k) (into_injective D k)]
    exact localRepresentative_order 15
  have hf : ∃ swap : Bool, ∀ i : Fin 17, IsConj (into D k (localRepresentative i))
      (into D k (classRepresentative (mergedClass swap i))) := by
    rcases four_fusion_of_involution_fusion D k h2 _ h14o with h14 | h14 <;>
      rcases four_fusion_of_involution_fusion D k h2 _ h15o with h15 | h15
    · exact False.elim (hpair (h14.trans h15.symm))
    · exact ⟨false, localRepresentative_fusion D k h2 hthree hza false h14 h15⟩
    · exact ⟨true, localRepresentative_fusion D k h2 hthree hza true h14 h15⟩
    · exact False.elim (hpair (h14.trans h15.symm))
  obtain ⟨swap, hs⟩ := hf
  exact ⟨swap, fun x => ((into D k).map_isConj (localClass_conjugate x)).trans (hs _)⟩

end CaseII.Distribution
open CaseII CaseII.Distribution
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The precise two extra fusion inputs suffice for both ambient class counts.
The normalizer argument must supply these inputs before using the source
statement with only `InvolutionNormalizerData` and order-three fusion. -/
public theorem localClassDistributions_of_remaining_four_fusion
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (h2 : ∀ x : G, orderOf x = 2 → IsConj x D.z)
    (hthree : ∀ x : G, orderOf x = 3 → IsConj x (into D k c))
    (hza : IsConj (into D k (z 1 * a)) (into D k (z 1 * d)))
    (hpair : ¬ IsConj (into D k (z 3 * d)) (into D k (z 1 * z 3 * d))) :
    LocalClassDistributions D k := by
  obtain ⟨swap, hs⟩ := exists_merged_fusion D k h2 hthree hza hpair
  have hi (x : TwistedModel) (i : Fin 7) :
      IsConj (into D k x) (into D k (classRepresentative i)) ↔
        mergedClass swap (localClass x) = i := by
    constructor
    · intro h
      exact representative_class_injective D k ((hs x).symm.trans h)
    · rintro rfl
      exact hs x
  constructor
  · intro i
    rw [centralizer_class_card D k]
    calc
      _ = Nat.card {x : TwistedModel // mergedClass swap (localClass x) = i} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => hi x i))
      _ = _ := mergedClass_card swap i
  · intro i
    rw [sylow_class_card D k]
    calc
      _ = Nat.card {x : modelSylow // mergedClass swap (localClass x.val) = i} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => hi x.val i))
      _ = _ := mergedClass_sylow_card swap i

/-- Janko's centralizer and Sylow distributions follow from the genuine
involution-normalizer data and ambient order-three fusion. The order-four
fusion premises of the counting reduction are discharged by the action of
the normalizer of `E`. -/
public theorem localClassDistributions_of_involution_normalizers [IsSimpleGroup G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (h2 : InvolutionNormalizerData D k)
    (hthree : ∀ x : G, orderOf x = 3 → IsConj x (into D k c)) :
    LocalClassDistributions D k := by
  obtain ⟨hza, hpair⟩ := remaining_four_fusion_of_involution_normalizers D k h2
  exact localClassDistributions_of_remaining_four_fusion D k
    h2.involution_fusion hthree hza hpair

end Theory.GroupTheory.HeldM22A10.M22Identification
