module

public import Theory.Representation.BinaryDuadStructure.QuotientClassification

/-!
# The universal three-point line relations

A vector configuration on the fifteen duads extends uniquely by linearity.
It factors through the line quotient exactly when its three-point line sums
vanish; spanning and equivariance pass to this explicit factor map. The
construction recovers the polar projection and classifies every spanning
equivariant configuration satisfying these relations. Deriving the relations
from the original orbit-plane hypothesis remains a separate geometric step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.3,
printed pp.343–345 (PDF pp.354–356).
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
namespace BinaryDuadStructure

section Universal
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Evaluate the permutation basis at a prescribed configuration of vectors. -/
def pointEvaluation (v : Duad → W) : Full Duad →ₗ[ZMod 2] W :=
  Fintype.linearCombination (ZMod 2) v

@[simp] theorem pointEvaluation_single (v : Duad → W) (d : Duad) :
    pointEvaluation v (Pi.single d 1) = v d := by
  simp [pointEvaluation, Fintype.linearCombination_apply_single]

theorem pointEvaluation_line (v : Duad → W) (s : Syntheme) :
    pointEvaluation v (line s) = ∑ d ∈ Finset.univ.filter (fun d => incident d s), v d := by
  simp [pointEvaluation, Fintype.linearCombination_apply, line, ite_smul,
    Finset.sum_filter]

/-- The universal quotient imposes precisely the three-point line relations. -/
def lineQuotientLift (v : Duad → W)
    (hline : ∀ s : Syntheme, ∑ d ∈ Finset.univ.filter (fun d => incident d s), v d = 0) :
    LineQuotient →ₗ[ZMod 2] W :=
  lineSpan.liftQ (pointEvaluation v) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact (pointEvaluation_line v s).trans (hline s))

@[simp] theorem lineQuotientLift_point (v : Duad → W)
    (hline : ∀ s : Syntheme, ∑ d ∈ Finset.univ.filter (fun d => incident d s), v d = 0)
    (d : Duad) : lineQuotientLift v hline (pointClass d) = v d :=
  pointEvaluation_single v d

theorem lineQuotientLift_surjective (v : Duad → W)
    (hline : ∀ s : Syntheme, ∑ d ∈ Finset.univ.filter (fun d => incident d s), v d = 0)
    (hspan : Submodule.span (ZMod 2) (Set.range v) = ⊤) :
    Function.Surjective (lineQuotientLift v hline) := by
  have hs : Function.Surjective (pointEvaluation v) := by
    apply LinearMap.range_eq_top.mp
    exact (Fintype.range_linearCombination (ZMod 2) v).trans hspan
  intro w
  obtain ⟨u, hu⟩ := hs w
  exact ⟨lineSpan.mkQ u, hu⟩

theorem lineQuotientLift_unique (v : Duad → W)
    (hline : ∀ s : Syntheme, ∑ d ∈ Finset.univ.filter (fun d => incident d s), v d = 0)
    (f : LineQuotient →ₗ[ZMod 2] W) (hf : ∀ d, f (pointClass d) = v d) :
    f = lineQuotientLift v hline := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ u =>
    have hu : u = ∑ d : Duad, u d • (Pi.single d (1 : ZMod 2) : Full Duad) := by
      ext e; simp [Pi.single_apply, mul_ite]
    change f (lineSpan.mkQ u) = pointEvaluation v u
    rw [hu, map_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [map_smul, pointEvaluation_single]
    exact congrArg (u d • ·) (hf d)

theorem lineQuotientLift_equivariant (ρ : Representation (ZMod 2) A6 W)
    (v : Duad → W)
    (hline : ∀ s : Syntheme, ∑ d ∈ Finset.univ.filter (fun d => incident d s), v d = 0)
    (hv : ∀ g d, v (g • d) = ρ g (v d)) (g : A6) (q : LineQuotient) :
    lineQuotientLift v hline (lineQuotientAction g q) = ρ g (lineQuotientLift v hline q) := by
  have he : (lineQuotientLift v hline).comp (lineQuotientAction g) =
      (ρ g).comp (lineQuotientLift v hline) := by
    have hl (d : Duad) :
        ((lineQuotientLift v hline).comp (lineQuotientAction g)) (pointClass d) = v (g • d) := by
      change lineQuotientLift v hline (lineQuotientAction g (pointClass d)) = _
      rw [← pointClass_equivariant, lineQuotientLift_point]
    have hr (d : Duad) :
        ((ρ g).comp (lineQuotientLift v hline)) (pointClass d) = v (g • d) := by
      change ρ g (lineQuotientLift v hline (pointClass d)) = _
      rw [lineQuotientLift_point, hv]
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ u =>
      have hu : u = ∑ d : Duad, u d • (Pi.single d (1 : ZMod 2) : Full Duad) := by
        ext e; simp [Pi.single_apply, mul_ite]
      change ((lineQuotientLift v hline).comp (lineQuotientAction g)) (lineSpan.mkQ u) =
        ((ρ g).comp (lineQuotientLift v hline)) (lineSpan.mkQ u)
      rw [hu, map_sum, map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [map_smul]
      exact congrArg (u d • ·) ((hl d).trans (hr d).symm)
  exact LinearMap.congr_fun he q

end Universal
/-- The actual polar vectors satisfy the defining universal line relations. -/
theorem polar_line_relation (s : Syntheme) :
    ∑ d ∈ Finset.univ.filter (fun d => incident d s), (polarVector d).val = 0 := by
  rw [← pointEvaluation_line]
  exact pointSum_line s

/-- The universal construction recovers the literal map onto the marked natural module. -/
theorem naturalProjection_eq_lift : naturalProjection =
    lineQuotientLift (fun d => (polarVector d).val) polar_line_relation :=
  lineQuotientLift_unique _ _ naturalProjection pointSum_single

/-- Recognition for a spanning equivariant configuration satisfying the actual line relations.
The source's orbit-plane hypotheses must still be used to establish these relations. -/
theorem lineConfiguration_alternatives {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Nontrivial W] (ρ : Representation (ZMod 2) A6 W) (v : Duad → W)
    (hline : ∀ s : Syntheme, ∑ d ∈ Finset.univ.filter (fun d => incident d s), v d = 0)
    (hspan : Submodule.span (ZMod 2) (Set.range v) = ⊤)
    (hv : ∀ g d, v (g • d) = ρ g (v d)) :
    Nonempty (Representation.Equiv alternatingNaturalAction ρ) ∨
      Nonempty (coreQuotientAction.Equiv ρ) := by
  let f : lineQuotientAction.IntertwiningMap ρ :=
    (lineQuotientLift v hline).intertwiningMap_of_isIntertwiningMap _ _
      (lineQuotientLift_equivariant ρ v hline hv)
  rcases nonzero_quotient_alternatives ρ f (lineQuotientLift_surjective v hline hspan)
    with h | h
  · exact Or.inl h
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨coreLineRepresentationEquiv.trans e⟩

end BinaryDuadStructure
