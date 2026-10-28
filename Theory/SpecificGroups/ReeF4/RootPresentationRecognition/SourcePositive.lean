module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.PositivePresentation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts

/-!
# Positive evaluation on the same marked source quotient

Local field charts on the eight actual Carter root factors, together with
the finite native root-pair equations, construct an abstract evaluation in
the given quotient. Carter's proved ordered coordinates show that its range
is exactly the original split U; generation is not a separate premise. Every
word then lifts uniquely through the literal quotient map on the original
whole overlap. The evaluation is not claimed injective: the full abstract
collection and source kernel arguments remain part of Ree recognition.

Source: Carter 2.5.10–17 (`refs/KGroup/GLS3/Chapter2Ca2.tex`), GLS3 2.4.5,
and the marked quotient in DGS, Groups and Graphs, Theorem D, p.224.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SourcePositive
open Subgroup PositiveTables PositivePresentation
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Local positive-root parameters and their exact marked placements. The order
field matches a literal reduced alternating word in the same quotient. -/
structure Charts (m : ℕ) where
  orientation : Bool
  rotation_eight : rotationOrder Q = 8
  index : Fin 8 ≃ PositiveTables.Root
  root : PositiveTables.Root → Subgroup (X ⧸ Q.D)
  order_eq : orderedRoots Q split orientation 8 = List.ofFn (fun j => root (index j))
  chart : (i : PositiveTables.Root) → Parameter m i ≃ root i
  equations : PositivePresentation.Equations (fun i a => (chart i a : X ⧸ Q.D))

variable {m : ℕ} (d : Charts Q split m)

/-- Each specified root is one of the actual positive factors. -/
theorem root_mem_ordered (i : PositiveTables.Root) :
    d.root i ∈ orderedRoots Q split d.orientation (rotationOrder Q) := by
  rw [d.rotation_eight, d.order_eq]
  exact List.mem_ofFn.mpr ⟨d.index.symm i, by rw [Equiv.apply_symm_apply]⟩

/-- Positivity follows from the existing Carter coordinates, not from an extra
membership premise on the charts. -/
theorem root_le_unipotent (i : PositiveTables.Root) : d.root i ≤ split.U := by
  have h := orderedRoots_le Q split d.orientation (rotationOrder Q) le_rfl
    (d.root i) (root_mem_ordered Q split d i)
  simpa only [alternatingWord_longest, longest_inv, rootIntersection_longest] using h

/-- The finite equations construct the source evaluation in the same Y = X/D. -/
def eval : PositivePresentation.Presentation m →* X ⧸ Q.D :=
  PositivePresentation.lift d.equations

@[simp] theorem eval_generator (i : PositiveTables.Root) (a : Parameter m i) :
    eval Q split d (PositivePresentation.generator m i a) = d.chart i a :=
  PositivePresentation.lift_generator d.equations i a

/-- Native finite relators have source image contained in the original U. -/
theorem eval_range_le : (eval Q split d).range ≤ split.U := by
  rintro x ⟨g, rfl⟩
  apply PresentedGroup.generated_by _ (split.U.comap (eval Q split d)) ?_ g
  rintro ⟨i,a⟩
  change eval Q split d (PositivePresentation.generator m i a) ∈ split.U
  rw [eval_generator]
  exact root_le_unipotent Q split d i (d.chart i a).property

/-- Every root factor occurs in the constructed image. -/
theorem root_le_range (i : PositiveTables.Root) : d.root i ≤ (eval Q split d).range := by
  intro x hx
  obtain ⟨a,ha⟩ := (d.chart i).surjective ⟨x,hx⟩
  exact ⟨PositivePresentation.generator m i a,
    (eval_generator Q split d i a).trans (congrArg Subtype.val ha)⟩

/-- Carter's actual product of positive roots proves surjectivity onto all U. -/
theorem eval_range : (eval Q split d).range = split.U := by
  apply le_antisymm (eval_range_le Q split d)
  intro u hu
  obtain ⟨p,hp⟩ := (unipotentOrderedCoordinates Q split d.orientation).surjective ⟨u,hu⟩
  have hfactor : ∀ A ∈ orderedRoots Q split d.orientation (rotationOrder Q),
      A ≤ (eval Q split d).range := by
    intro A hA
    rw [d.rotation_eight, d.order_eq] at hA
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hA
    exact root_le_range Q split d (d.index j)
  have hm := rootProduct_mem _ (eval Q split d).range hfactor p
  have he : rootProduct (orderedRoots Q split d.orientation (rotationOrder Q)) p = u :=
    (unipotentOrderedCoordinates_apply Q split d.orientation p).symm.trans
      (congrArg Subtype.val hp)
  rwa [he] at hm

/-- Every evaluated positive word lifts uniquely on the original whole overlap,
through exactly Q.q. This applies to the literal marked quotient, independently
of whether its numerator was the generated group or a universal completion. -/
theorem existsUnique_borel_lift (g : PositivePresentation.Presentation m) :
    ∃! a : (P 0 ⊓ P 1 : Subgroup X), Q.q a = eval Q split d g := by
  have hu : eval Q split d g ∈ split.U := eval_range_le Q split d ⟨g,rfl⟩
  let b : Q.tits.B := ⟨eval Q split d g, split.U_le hu⟩
  refine ⟨Q.borelEquiv.symm b, ?_, ?_⟩
  · simpa only [Q.borelEquiv_apply] using
      congrArg Subtype.val (Q.borelEquiv.apply_symm_apply b)
  · intro a ha
    apply Q.borelEquiv.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simpa only [Q.borelEquiv_apply] using ha

end ReeF4.RootPresentationRecognition.SourcePositive
