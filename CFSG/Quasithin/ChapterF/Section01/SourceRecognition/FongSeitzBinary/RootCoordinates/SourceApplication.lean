module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.SimplePanels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.NormalGeneration

/-!
# Original source application of split intersection coordinates

For the same marked quotient Q and split datum, the index of the entire
original common Borel in either original parabolic is
`1 + [U : U ∩ U^n_i]`. The proof transports both literal inclusions through
`originalMarkedIso`. The specified U is then rewritten as the image of
the original S under Q.q, without changing either endpoint or the overlap.
The constructed longest element identifies the opposite Borel and its
unipotent subgroup. The simple root intersections are nontrivial, give
unique multiplication coordinates on the original S image, and replace
the last index by their actual orders. Their literal root charts give
bijections onto each punctured endpoint panel, with the entire Borel retained.

Source: DGS, *Groups and Graphs*, Part II, Theorem D, printed p.224;
Carter §2.5.9 and the singleton Bruhat decomposition. The marked dihedral
coordinates and longest element are constructed, not assumed. The general
ordered-root recurrence and marked Lie recognition are separate remaining
steps. No perfectness or finiteness of the original ambient group is required
by these applications.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.RootCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Count either original parabolic over its entire original common Borel. -/
theorem original_commonBorel_index (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (i : Fin 2) :
    ((commonBorel L S).subgroupOf (parabolic L S i)).index =
      1 + ((split.U ⊓ unipotentConjugate split (Q.simple i)).subgroupOf split.U).index := by
  have hi := marked_amalgam_indices Q split (originalMarkedIso Q)
  rw [← lemma_F_1_3_6 h]
  have casesi : i = 0 ∨ i = 1 := by omega
  rcases casesi with rfl | rfl
  · simpa only [RankTwoAmalgam.ofSubgroups, inclusion_range] using hi.1
  · simpa only [RankTwoAmalgam.ofSubgroups, inclusion_range] using hi.2

/-- The endpoint formula with U literally replaced by the original S image. -/
theorem original_sourceS_index (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    ((commonBorel L S).subgroupOf (parabolic L S i)).index =
      1 + ((((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          (n : (generated L S) ⧸ Q.D)).subgroupOf
            ((S.subgroupOf (generated L S)).map Q.q)).index := by
  rw [quotient_sourceS_image_eq_unipotent h Q split, original_commonBorel_index h Q split i,
    unipotentConjugate_eq split (Q.simple i) n hn]

/-- The root intersections use the actual quotient map and right-conjugation order. -/
theorem quotient_rootIntersection_originalS (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (w₀ w : Weyl Q) (n₀ n : Q.tits.N)
    (h₀ : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n₀ = w₀)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = w) :
    rootIntersection split w₀ w = ((S.subgroupOf (generated L S)).map Q.q) ⊓
      (((S.subgroupOf (generated L S)).map Q.q).comap
        (MulAut.conj ((n₀ : (generated L S) ⧸ Q.D) * (n : (generated L S) ⧸ Q.D))).toMonoidHom) := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  exact rootIntersection_eq split w₀ w n₀ n h₀ hn

/-- Unique coordinates on the original S image and the entire torus. -/
theorem quotient_borel_intersection_originalS_unique (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (n : Q.tits.N)
    (x : (Q.tits.B ⊓ rightConjugate Q.tits.B (n : (generated L S) ⧸ Q.D) :
      Subgroup ((generated L S) ⧸ Q.D))) :
    ∃! p : ((((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          (n : (generated L S) ⧸ Q.D) : Subgroup ((generated L S) ⧸ Q.D)) ×
        (Q.tits.B ⊓ Q.tits.N : Subgroup ((generated L S) ⧸ Q.D))),
      (p.1 : (generated L S) ⧸ Q.D) * (p.2 : (generated L S) ⧸ Q.D) = x := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  let e := intersectionCoordinates split n
  refine ⟨e.symm x, ?_, ?_⟩
  · have he := congrArg Subtype.val (e.apply_symm_apply x)
    exact (intersectionCoordinates_apply split n (e.symm x).1 (e.symm x).2).symm.trans he
  · intro p hp
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext ((intersectionCoordinates_apply split n p.1 p.2).trans hp)

/-- The same source quotient has the constructed dihedral coordinates and both generator images. -/
theorem quotient_marked_dihedral_coordinates (Q : SourceQuotient L S) :
    2 ≤ rotationOrder Q ∧
      weylEquiv Q (Q.simple 0) = DihedralGroup.sr 0 ∧
      weylEquiv Q (Q.simple 1) = DihedralGroup.sr 1 ∧
      Nat.card (Weyl Q) = 2 * rotationOrder Q :=
  ⟨rotationOrder_ge_two Q, weylEquiv_simple_zero Q, weylEquiv_simple_one Q, weyl_card Q⟩

/-- The exact simple-root order counts either original endpoint over its full Borel. -/
theorem original_commonBorel_root_index (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (i : Fin 2) :
    ((commonBorel L S).subgroupOf (parabolic L S i)).index =
      1 + Nat.card (simpleRoot Q split i) := by
  rw [original_commonBorel_index h Q split i]
  exact congrArg (1 + ·) (simpleRemainder_index Q split i)

/-- The root order formula uses the literal original S image and both original lifts. -/
theorem original_sourceS_root_index (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (i : Fin 2) (n₀ n : Q.tits.N)
    (h₀ : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n₀ = longest Q)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    ((commonBorel L S).subgroupOf (parabolic L S i)).index =
      1 + Nat.card (((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          ((n₀ : (generated L S) ⧸ Q.D) * (n : (generated L S) ⧸ Q.D)) :
            Subgroup ((generated L S) ⧸ Q.D)) := by
  rw [original_commonBorel_root_index h Q split i]
  exact congrArg (fun R : Subgroup ((generated L S) ⧸ Q.D) => 1 + Nat.card R)
    (quotient_rootIntersection_originalS h Q split (longest Q) (Q.simple i) n₀ n h₀ hn)

/-- The opposite Sylow image is disjoint from the entire original quotient Borel. -/
theorem quotient_originalS_opposite (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (n₀ : Q.tits.N)
    (h₀ : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n₀ = longest Q) :
    Q.tits.B ⊓ rightConjugate Q.tits.B (n₀ : (generated L S) ⧸ Q.D) = Q.tits.B ⊓ Q.tits.N ∧
    Q.tits.B ⊓ rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
      (n₀ : (generated L S) ⧸ Q.D) = ⊥ := by
  rw [quotient_sourceS_image_eq_unipotent h Q split,
    ← borelConjugate_eq (longest Q) n₀ h₀, ← unipotentConjugate_eq split (longest Q) n₀ h₀]
  exact ⟨borel_inf_opposite Q split, borel_inf_opposite_unipotent Q split⟩

/-- Unique simple-root coordinates for every element of the original S image. -/
theorem quotient_originalS_simple_unique (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (i : Fin 2) (u : (generated L S) ⧸ Q.D)
    (hu : u ∈ (S.subgroupOf (generated L S)).map Q.q) :
    ∃! p : simpleRoot Q split i × simpleRemainder Q split i,
      (p.1 : (generated L S) ⧸ Q.D) * p.2 = u := by
  rw [quotient_sourceS_image_eq_unipotent h Q split] at hu
  let x : split.U := ⟨u, hu⟩
  let e := simpleCoordinates Q split i
  refine ⟨e.symm x, ?_, ?_⟩
  · exact (simpleCoordinates_apply Q split i (e.symm x).1 (e.symm x).2).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply x))
  · intro p hp
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext ((simpleCoordinates_apply Q split i p.1 p.2).trans hp)

/-- The same nontrivial root lies in the original S image and charts the literal panel. -/
theorem quotient_originalS_simple_panel (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    simpleRoot Q split i ≠ ⊥ ∧
      simpleRoot Q split i ≤ (S.subgroupOf (generated L S)).map Q.q ∧
      Q.tits.B ⊓ Q.tits.N ≤ normalizer (simpleRoot Q split i : Set ((generated L S) ⧸ Q.D)) ∧
      Function.Bijective (simplePanelMap Q split i n hn) := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  exact ⟨simpleRoot_ne_bot Q split i, simpleRoot_le Q split i,
    torus_normalizes_simpleRoot Q split i, simplePanelMap_bijective Q split i n hn⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.RootCoordinates
