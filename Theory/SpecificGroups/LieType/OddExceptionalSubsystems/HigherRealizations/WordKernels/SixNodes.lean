module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.Words

/-!
# The common six-node word alphabet

Expand the four folded nodes into the same six E6 nodes in all three integral
matrix realizations. The E6 diagram permutation acts on this free alphabet;
a folded word has the same evaluation as its diagram transform because the
two paired simple roots commute. This statement concerns evaluations, not an
automorphism of an unproved universal group.

Source: GLS3 §§2.5--2.6 (`refs/KGroup/GLS3/chapter2.tex`), for the folded
subsystems used in Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations

attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

variable (F : Type*) [Field F]

abbrev SixNodeWord := FreeGroup (Bool × Fin 6 × F)

/-- Evaluate all six signed E6 nodes in the source adjoint matrix carrier. -/
def sourceSix : SixNodeWord F →* splitCarrier F :=
  FreeGroup.lift fun x => simpleRoot F x.1 x.2.1 x.2.2

/-- Evaluate the first six signed nodes in the E7 matrix carrier. -/
def e7Six : SixNodeWord F →* ExceptionalSplit.e7Cover F :=
  FreeGroup.lift fun x => e7Simple F x.1 (x.2.1.castLE (by decide)) x.2.2

/-- Evaluate the first six signed nodes in the E8 matrix carrier. -/
def e8Six : SixNodeWord F →* ExceptionalSplit.e8Cover F :=
  FreeGroup.lift fun x => e8Simple F x.1 (x.2.1.castLE (by decide)) x.2.2

/-- Expand folded nodes in exactly the F4 order used by `f4Simple`. -/
def expandFolded : FoldedWord F →* SixNodeWord F :=
  FreeGroup.lift fun x =>
    ![FreeGroup.of (x.1, 3, x.2.2), FreeGroup.of (x.1, 2, x.2.2),
      FreeGroup.of (x.1, 1, x.2.2) * FreeGroup.of (x.1, 4, x.2.2),
      FreeGroup.of (x.1, 0, x.2.2) * FreeGroup.of (x.1, 5, x.2.2)] x.2.1

/-- Apply the pinned E6 diagram permutation to the free six-node alphabet. -/
def diagramWord : SixNodeWord F →* SixNodeWord F :=
  FreeGroup.lift fun x => FreeGroup.of (x.1, typeE6DiagramPermutation x.2.1, x.2.2)

@[simp] theorem sourceSix_of (s : Bool) (i : Fin 6) (t : F) :
    sourceSix F (FreeGroup.of (s, i, t)) = simpleRoot F s i t :=
  FreeGroup.lift_apply_of

@[simp] theorem e7Six_of (s : Bool) (i : Fin 6) (t : F) :
    e7Six F (FreeGroup.of (s, i, t)) =
      e7Simple F s (i.castLE (by decide)) t := FreeGroup.lift_apply_of

@[simp] theorem e8Six_of (s : Bool) (i : Fin 6) (t : F) :
    e8Six F (FreeGroup.of (s, i, t)) =
      e8Simple F s (i.castLE (by decide)) t := FreeGroup.lift_apply_of

omit [Field F] in
@[simp] theorem diagramWord_of (s : Bool) (i : Fin 6) (t : F) :
    diagramWord F (FreeGroup.of (s, i, t)) =
      FreeGroup.of (s, typeE6DiagramPermutation i, t) := FreeGroup.lift_apply_of

omit [Field F] in
theorem diagramWord_involutive : Function.Involutive (diagramWord F) := by
  have h : (diagramWord F).comp (diagramWord F) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    rintro ⟨s, i, t⟩
    simp
  exact fun w => DFunLike.congr_fun h w

@[simp] theorem sourceSix_expandFolded (w : FoldedWord F) :
    sourceSix F (expandFolded F w) = (sourceWord F w).val := by
  have h : (sourceSix F).comp (expandFolded F) =
      (splitSubgroup F).subtype.comp (sourceWord F) := by
    apply FreeGroup.ext_hom
    rintro ⟨s, i, t⟩
    fin_cases i <;>
      simp [expandFolded, f4Simple, foldedSimple, Fin.rev]
  exact DFunLike.congr_fun h w

@[simp] theorem e7Six_expandFolded (w : FoldedWord F) :
    e7Six F (expandFolded F w) = e7Word F w := by
  have h : (e7Six F).comp (expandFolded F) = e7Word F := by
    apply FreeGroup.ext_hom
    rintro ⟨s, i, t⟩
    fin_cases i <;> simp [expandFolded, e7FoldedSimple]
  exact DFunLike.congr_fun h w

@[simp] theorem e8Six_expandFolded (w : FoldedWord F) :
    e8Six F (expandFolded F w) = e8Word F w := by
  have h : (e8Six F).comp (expandFolded F) = e8Word F := by
    apply FreeGroup.ext_hom
    rintro ⟨s, i, t⟩
    fin_cases i <;> simp [expandFolded, e8FoldedSimple]
  exact DFunLike.congr_fun h w

omit [Field F] in
/-- Only the two orthogonal pair commutations are needed for diagram invariance. -/
theorem eval_diagram_expandFolded {G : Type*} [Group G]
    (v : SixNodeWord F →* G)
    (h05 : ∀ s t, Commute (v (FreeGroup.of (s, 0, t)))
      (v (FreeGroup.of (s, 5, t))))
    (h14 : ∀ s t, Commute (v (FreeGroup.of (s, 1, t)))
      (v (FreeGroup.of (s, 4, t)))) (w : FoldedWord F) :
    v (diagramWord F (expandFolded F w)) = v (expandFolded F w) := by
  have h : (v.comp (diagramWord F)).comp (expandFolded F) =
      v.comp (expandFolded F) := by
    apply FreeGroup.ext_hom
    rintro ⟨s, i, t⟩
    fin_cases i
    · simp [expandFolded, typeE6DiagramPermutation]
    · simp [expandFolded, typeE6DiagramPermutation]
    · simpa [expandFolded, typeE6DiagramPermutation] using (h14 s t).eq.symm
    · simpa [expandFolded, typeE6DiagramPermutation] using (h05 s t).eq.symm
  exact DFunLike.congr_fun h w

@[simp] theorem e7Six_diagram_expandFolded (w : FoldedWord F) :
    e7Six F (diagramWord F (expandFolded F w)) = e7Word F w := by
  rw [eval_diagram_expandFolded, e7Six_expandFolded]
  · intro s t
    simp only [e7Six_of]
    apply signedSimple_commute
    · exact typeE7RootPairing_baseEquiv.injective.ne (by decide)
    · rw [typeE7RootPairing_base_cartan_apply]
      decide
  · intro s t
    simp only [e7Six_of]
    apply signedSimple_commute
    · exact typeE7RootPairing_baseEquiv.injective.ne (by decide)
    · rw [typeE7RootPairing_base_cartan_apply]
      decide

@[simp] theorem e8Six_diagram_expandFolded (w : FoldedWord F) :
    e8Six F (diagramWord F (expandFolded F w)) = e8Word F w := by
  rw [eval_diagram_expandFolded, e8Six_expandFolded]
  · intro s t
    simp only [e8Six_of]
    apply signedSimple_commute
    · exact typeE8RootPairing_baseEquiv.injective.ne (by decide)
    · rw [typeE8RootPairing_base_cartan_apply]
      decide
  · intro s t
    simp only [e8Six_of]
    apply signedSimple_commute
    · exact typeE8RootPairing_baseEquiv.injective.ne (by decide)
    · rw [typeE8RootPairing_base_cartan_apply]
      decide

end TwistedE6.FoldedSubsystem.HigherRealizations
