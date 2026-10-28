module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootCoordinates.SourceApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.BruhatCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas

/-!
# Ordered roots and Bruhat coordinates on the original source quotient

Apply Carter's split-root recurrence to the same marked source quotient Q.
The ordered positive factors are conjugates of its two panel roots, lie in
the literal Q.q-image of the original S and are normalized by the entire H.
Their multiplication gives unique coordinates on that original image.
The refined Bruhat coordinates retain Q's actual Borel and supplied lifts.
The even and odd order formulas are expressed in terms of the original
parabolic/common-Borel indices; odd m makes those indices equal.
Normal containment supplies the root-generation premise of the recognition
owner's whole-quotient argument, without assuming either factor perfect.

Sources: Carter 2.5.10–2.5.17, `refs/KGroup/GLS3/Chapter2Ca2.tex`;
DGS, *Groups and Graphs*, Part II, Theorem D, printed p.224.
-/

public noncomputable section
open scoped Pointwise
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.RootCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Unique refined Bruhat coordinates with the root written in the original S image. -/
theorem quotient_bruhat_originalS_unique (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (w : Weyl Q) (n₀ nw : Q.tits.N)
    (h₀ : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n₀ = longest Q)
    (hw : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) nw = w)
    (x : (generated L S) ⧸ Q.D) (hx : x ∈ Q.tits.bruhatCell w) :
    ∃! p : Q.tits.B × (((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
        ((n₀ : (generated L S) ⧸ Q.D)*(nw : (generated L S) ⧸ Q.D)) :
          Subgroup ((generated L S) ⧸ Q.D)),
      (p.1 : (generated L S) ⧸ Q.D)*nw*p.2 = x := by
  have he : rootIntersection split (longest Q) w =
      ((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          ((n₀ : (generated L S) ⧸ Q.D)*(nw : (generated L S) ⧸ Q.D)) :=
    quotient_rootIntersection_originalS h Q split (longest Q) w n₀ nw h₀ hw
  rw [← he]
  let e := bruhatCoordinates Q split w nw hw
  let z : Q.tits.bruhatCell w := ⟨x,hx⟩
  refine ⟨e.symm z, ?_, ?_⟩
  · exact (bruhatCoordinates_apply Q split w nw hw (e.symm z).1 (e.symm z).2).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply z))
  · intro p hp
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext ((bruhatCoordinates_apply Q split w nw hw p.1 p.2).trans hp)

/-- Each positive factor uses one of the same two roots and the same full torus. -/
theorem quotient_originalS_positive_factors (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (b : Bool) (A : Subgroup ((generated L S) ⧸ Q.D))
    (hA : A ∈ orderedRoots Q split b (rotationOrder Q)) :
    ∃ i : Fin 2, ∃ ni : Q.tits.N,
      A = rightConjugate (simpleRoot Q split i) (ni : (generated L S) ⧸ Q.D) ∧
      A ≤ (S.subgroupOf (generated L S)).map Q.q ∧
      Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set ((generated L S) ⧸ Q.D)) := by
  obtain ⟨i,ni,he⟩ := orderedRoots_are_simple_conjugates Q split b _ A hA
  have hle := orderedRoots_le Q split b _ le_rfl A hA
  rw [alternatingWord_longest, longest_inv, rootIntersection_longest] at hle
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  exact ⟨i,ni,he,hle,orderedRoots_torus_normalizes Q split b _ A hA⟩

/-- The literal original S image is the ordered product of these positive roots. -/
theorem quotient_originalS_ordered_product (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (b : Bool) :
    ((orderedRoots Q split b (rotationOrder Q)).map
      (fun A => (A : Set ((generated L S) ⧸ Q.D)))).prod =
      ((S.subgroupOf (generated L S)).map Q.q : Set ((generated L S) ⧸ Q.D)) := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  exact unipotent_ordered_product Q split b

/-- Multiplication gives unique coordinates on the original S image. -/
theorem quotient_originalS_ordered_unique (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (b : Bool) (x : (generated L S) ⧸ Q.D)
    (hx : x ∈ (S.subgroupOf (generated L S)).map Q.q) :
    ∃! p : RootTuple (orderedRoots Q split b (rotationOrder Q)),
      rootProduct (orderedRoots Q split b (rotationOrder Q)) p = x := by
  rw [quotient_sourceS_image_eq_unipotent h Q split] at hx
  let e := unipotentOrderedCoordinates Q split b
  let z : split.U := ⟨x,hx⟩
  refine ⟨e.symm z, ?_, ?_⟩
  · exact (unipotentOrderedCoordinates_apply Q split b (e.symm z)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply z))
  · intro p hp
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext ((unipotentOrderedCoordinates_apply Q split b p).trans hp)

/-- The original S image lies in any normal subgroup containing the actual two roots. -/
theorem quotient_originalS_le_normal_of_simpleRoots_le (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (K : Subgroup ((generated L S) ⧸ Q.D)) [K.Normal]
    (hK : ∀ i, simpleRoot Q split i ≤ K) : (S.subgroupOf (generated L S)).map Q.q ≤ K := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  exact unipotent_le_normal_of_simpleRoots_le Q split K hK

/-- Odd m forces equality of the original endpoint degrees over the full overlap. -/
theorem original_commonBorel_indices_eq_of_odd (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hm : Odd (rotationOrder Q)) :
    ((commonBorel L S).subgroupOf (parabolic L S 0)).index =
      ((commonBorel L S).subgroupOf (parabolic L S 1)).index := by
  rw [original_commonBorel_root_index h Q split 0, original_commonBorel_root_index h Q split 1,
    simpleRoot_card_eq_of_odd Q split hm]

/-- The even order formula uses the two literal original endpoint indices. -/
theorem quotient_originalS_card_even (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (k : ℕ) (hm : rotationOrder Q = 2*k) :
    Nat.card ((S.subgroupOf (generated L S)).map Q.q) =
      ((((commonBorel L S).subgroupOf (parabolic L S 0)).index-1)*
        (((commonBorel L S).subgroupOf (parabolic L S 1)).index-1))^k := by
  rw [quotient_sourceS_image_eq_unipotent h Q split,
    original_commonBorel_root_index h Q split 0, original_commonBorel_root_index h Q split 1]
  simpa only [Nat.add_sub_cancel_left] using unipotent_card_even Q split k hm

/-- The odd order formula uses the same original S image and endpoint index. -/
theorem quotient_originalS_card_odd (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (hm : Odd (rotationOrder Q)) :
    Nat.card ((S.subgroupOf (generated L S)).map Q.q) =
      (((commonBorel L S).subgroupOf (parabolic L S 0)).index-1)^rotationOrder Q := by
  rw [quotient_sourceS_image_eq_unipotent h Q split, original_commonBorel_root_index h Q split 0]
  simpa only [Nat.add_sub_cancel_left] using unipotent_card_odd_pow Q split hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.RootCoordinates
