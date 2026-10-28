module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PolygonGonality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PolygonParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TriangleStructure.Recognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Catalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearEndpointRecognition

/-!
# Exhaustive marked split recognition at an original linear endpoint

Feit--Higman and the original characteristic-two hypothesis restrict the
same marked quotient to rotations 3, 4, 6 and 8. The proved triangle,
quadrangle, hexagon and octagon comparisons exhaust these alternatives.
Thus an original linear factor supplies the concrete amalgam comparison
without a selected Weyl order, opposite factor or source-equation premise.
Quasithinness restricts the unitary-five row to its catalogue field four.

Reversing the original pair changes only its indexing: the normal subgroup,
quotient map, Tits system and split structure are unchanged. The full Borel
and both inclusion squares are transported explicitly. Both orientations,
all positive linear degrees, the binary case and Ree parameter zero remain.

The quotient and split structure are genuine earlier inputs, supplied on
the regular apartment branch by qt-dgs85-apartment-exchange. Selecting a
linear endpoint in the unrestricted source family and the unconditional
source assembly remain separate obligations; no ambient completion is
identified here.

Source: Fong--Seitz I (1J), (3E), (6A)--(6H), and II Sections 8--10;
DGS, Groups and Graphs, Theorem D, printed p.224; AS F.1.1--12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SplitRecognition
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The actual left linear factor recognizes the full original amalgam across
all allowed rotations. No Weyl-order selection is supplied by the caller. -/
theorem marked_catalogue_of_linear_left
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso (Global.sourceParabolicAmalgam L S) Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (hqt : IsQuasithin G) {n : ℕ} (hn : 0 < n)
    (hi : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n)) :
    Global.ConcreteAmalgamComparison (Global.sourceParabolicAmalgam L S) := by
  rcases PolygonGonality.marked_rotationOrder_allowed Q mark h split with hm|hm|hm|hm
  · obtain ⟨F,hF,hfin,hchar,_,j,⟨rd⟩⟩ :=
      TriangleStructure.original_rootData Q mark h split hm 0 hi
    exact A2Source.linear_catalogue_of_flagIso j
      (LinearThreePresentation.comparison Q mark h split rd)
  · obtain ⟨K,hK,hfin,hcard,⟨μ⟩⟩ := hi
    let := Fintype.ofFinite K
    let : NeZero n := ⟨hn.ne'⟩
    let : CharP K 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact QuadrangleRecognition.marked_quadrangle_catalogue_of_linear_left
      Q mark h split hqt hm μ
  · exact HexagonRecognition.marked_hexagon_catalogue_of_rotation_six Q mark h split hm
  · obtain ⟨m,_,he⟩ :=
      OctagonStructure.original_linear_octagon_comparison Q mark h split hm hn hi
    exact .ree m he

/-- Apply exhaustive recognition through the canonical marking of the literal
quotient of the generated original carrier. -/
theorem original_catalogue_of_linear_left
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hqt : IsQuasithin G) {n : ℕ} (hn : 0 < n)
    (hi : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n)) :
    Global.ConcreteAmalgamComparison (Global.sourceParabolicAmalgam L S) :=
  marked_catalogue_of_linear_left Q (originalMarkedIso Q) h split hqt hn hi

private def reversedQuotient (Q : MarkedQuotient P) :
    MarkedQuotient (fun i => P i.rev) where
  D := Q.D
  disjoint i := Q.disjoint i.rev
  tits := Q.tits
  simple i := Q.simple i.rev
  simple_injective := Q.simple_injective.comp Fin.rev_injective
  simple_range := by
    rw [←Q.simple_range]
    ext s
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨i.rev,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨i.rev,by simp⟩
  parabolic_image i := Q.parabolic_image i.rev
  borel_image := by
    change (P 1 ⊓ P 0).map (QuotientGroup.mk' Q.D) = Q.tits.B
    rw [inf_comm]; exact Q.borel_image

omit [Finite G] in
private theorem reversed_hypothesis (h : HypothesisF11 L S) :
    HypothesisF11 (fun i => L i.rev) S := by
  refine ⟨h.finite_S,h.S_isP,(fun i => h.S_normalizes i.rev),
    (fun i => h.sylow i.rev),(fun i => h.quotient i.rev),?_,?_,?_⟩
  · intro i; fin_cases i
    · exact h.cross 1
    · exact h.cross 0
  · change pCore 2 (L 1 ⊔ L 0 ⊔ S : Subgroup G) = ⊥
    rw [sup_comm (L 1) (L 0)]; exact h.twoCore_free
  · intro i; fin_cases i
    · exact h.characteristic_two 1
    · exact h.characteristic_two 0

private def subgroupReverseIso (A B : Subgroup G) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right)
    (RankTwoAmalgam.ofSubgroups B (B ⊓ A) A inf_le_left inf_le_right).reverse where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (inf_comm _ _)
  right := MulEquiv.refl _
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

omit [Finite G] in
private theorem parabolic_reverse (i : Fin 2) :
    parabolic (fun i => L i.rev) S i = parabolic L S i.rev := by
  fin_cases i <;> rfl

private def sourceReverseIso : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam L S)
    (Global.sourceParabolicAmalgam (fun i => L i.rev) S).reverse := by
  exact subgroupReverseIso (parabolic L S 0) (parabolic L S 1)

private def quotientReverseIso (Q : MarkedQuotient P) :
    RankTwoAmalgam.Iso Q.standardAmalgam.reverse (reversedQuotient Q).standardAmalgam where
  left := MulEquiv.refl _
  middle := MulEquiv.refl _
  right := MulEquiv.refl _
  left_commutes b := by
    apply Subtype.ext
    change Subtype.val (Q.standardAmalgam.right b) =
      Subtype.val ((reversedQuotient Q).standardAmalgam.left b)
    rw [standardAmalgam_right_eq_inclusion,standardAmalgam_left_eq_inclusion]
    rfl
  right_commutes b := by
    apply Subtype.ext
    change Subtype.val (Q.standardAmalgam.left b) =
      Subtype.val ((reversedQuotient Q).standardAmalgam.right b)
    rw [standardAmalgam_left_eq_inclusion,standardAmalgam_right_eq_inclusion]
    rfl

private theorem reverse_comparisons
    {A B C A' B' C' U V W : Type*}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    [Group U] [Group V] [Group W]
    {α : RankTwoAmalgam A B C} {β : RankTwoAmalgam A' B' C'}
    {γ : RankTwoAmalgam U V W} (e : RankTwoAmalgam.Iso α β.reverse)
    (he : Nonempty (RankTwoAmalgam.Iso β γ) ∨
      Nonempty (RankTwoAmalgam.Iso β γ.reverse)) :
    Nonempty (RankTwoAmalgam.Iso α γ) ∨
      Nonempty (RankTwoAmalgam.Iso α γ.reverse) := by
  rcases he with he | he
  · obtain ⟨f⟩ := he
    exact Or.inr ⟨e.trans f.reverse⟩
  · obtain ⟨f⟩ := he
    exact Or.inl ⟨e.trans f.reverse⟩

private theorem catalogue_of_reverse_iso
    {A B C A' B' C' : Type*}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    {α : RankTwoAmalgam A B C} {β : RankTwoAmalgam A' B' C'}
    (e : RankTwoAmalgam.Iso α β.reverse)
    (hc : Global.ConcreteAmalgamComparison β) : Global.ConcreteAmalgamComparison α := by
  cases hc with
  | linear F m hm hF he => exact .linear F m hm hF (reverse_comparisons e he)
  | symplectic F m hm hF he => exact .symplectic F m hm hF (reverse_comparisons e he)
  | g2 F he => exact .g2 F (reverse_comparisons e he)
  | triality m hm he => exact .triality m hm (reverse_comparisons e he)
  | ree m he => exact .ree m (reverse_comparisons e he)
  | unitary m hm he => exact .unitary m hm (reverse_comparisons e he)
  | unitaryExtension m hm he => exact .unitaryExtension m hm (reverse_comparisons e he)
  | unitaryFive M he => exact .unitaryFive M (reverse_comparisons e he)
  | exceptional c he =>
    apply Global.ConcreteAmalgamComparison.exceptional c
    cases c <;> rcases he with he | he
    all_goals obtain ⟨f⟩ := he
    all_goals first
      | exact Or.inr ⟨e.reverse.toParabolicEquiv.trans f⟩
      | exact Or.inl ⟨e.toParabolicEquiv.trans f⟩

/-- Either original linear endpoint suffices. Reversal preserves the same
quotient and full overlap, and transports both inclusion squares. -/
theorem marked_catalogue_of_linear_factor
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso (Global.sourceParabolicAmalgam L S) Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (hqt : IsQuasithin G) (i : Fin 2) {n : ℕ} (hn : 0 < n)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    Global.ConcreteAmalgamComparison (Global.sourceParabolicAmalgam L S) := by
  fin_cases i
  · exact marked_catalogue_of_linear_left Q mark h split hqt hn hi
  · let e : RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam (fun i => L i.rev) S)
        (reversedQuotient Q).standardAmalgam :=
      ((sourceReverseIso (L := L) (S := S)).reverse.symm.trans mark.reverse).trans
        (quotientReverseIso Q)
    exact catalogue_of_reverse_iso sourceReverseIso
      (marked_catalogue_of_linear_left (reversedQuotient Q) e
        (reversed_hypothesis h) split hqt hn hi)

/-- The original source quotient is recognized at either linear endpoint,
including the binary field and without endpoint perfectness. -/
theorem original_catalogue_of_linear_factor
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hqt : IsQuasithin G) (i : Fin 2) {n : ℕ} (hn : 0 < n)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    Global.ConcreteAmalgamComparison (Global.sourceParabolicAmalgam L S) :=
  marked_catalogue_of_linear_factor Q (originalMarkedIso Q) h split hqt i hn hi

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SplitRecognition

