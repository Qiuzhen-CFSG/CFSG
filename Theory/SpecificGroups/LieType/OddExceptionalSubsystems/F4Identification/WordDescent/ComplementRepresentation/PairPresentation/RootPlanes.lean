module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.LocalWords

/-!
# All-root words and literal F4 plane relations

The all-root word group evaluates in the same Geck matrix cover as `Word`.
A plane consists of every root in the real span of two specified roots, so
its words include all intermediate roots of a B2 commutator. Rank-one spans
are allowed and include the opposite-root and torus relations.

The normal closure of the literal plane identity words is contained in the
all-root evaluation kernel. The reverse inclusion is a separate normal-form
obligation, following Steinberg, *Lectures on Chevalley Groups*, §3 and
Theorem 8 (`refs/KGroup/GLS3/Chapter2St1.tex`). Its proof must compare the
universal version with this actual matrix group. The root transport from
GLS3 §2.9.3 independently constructs a marked map from these words to the
two-node completion that kills every plane relation.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

variable (F : Type*) [Field F]

/-- Formal letters for all 48 roots, with their original parameters. -/
abbrev RootWord := FreeGroup (typeF4Roots × F)

def rootEvaluation : RootWord F →* Cover F :=
  FreeGroup.lift fun x => ExceptionalSplit.elementaryRoot
    typeF4RootPairing typeF4RootPairing_base F x.1 x.2

@[simp] theorem rootEvaluation_of (r : typeF4Roots) (t : F) :
    rootEvaluation F (FreeGroup.of (r, t)) =
      ExceptionalSplit.elementaryRoot typeF4RootPairing typeF4RootPairing_base F r t :=
  FreeGroup.lift_apply_of

def signedRoot (s : Bool) (i : Fin 4) : typeF4Roots :=
  let := typeF4RootPairing.indexNeg
  if s then sourceIndex i else -(sourceIndex i)

def simpleRootInclusion : Word F →* RootWord F :=
  FreeGroup.lift fun x => FreeGroup.of (signedRoot x.1 x.2.1, x.2.2)

omit [Field F] in
@[simp] theorem simpleRootInclusion_of (s : Bool) (i : Fin 4) (t : F) :
    simpleRootInclusion F (FreeGroup.of (s, i, t)) =
      FreeGroup.of (signedRoot s i, t) :=
  FreeGroup.lift_apply_of

@[simp] theorem rootEvaluation_simpleRootInclusion (w : Word F) :
    rootEvaluation F (simpleRootInclusion F w) = coverEvaluation F w := by
  have he : (rootEvaluation F).comp (simpleRootInclusion F) = coverEvaluation F := by
    apply FreeGroup.ext_hom
    rintro ⟨s, i, t⟩
    cases s <;> rfl
  exact DFunLike.congr_fun he w

theorem rootEvaluation_surjective : Function.Surjective (rootEvaluation F) := by
  intro g
  obtain ⟨w, rfl⟩ := coverEvaluation_surjective F g
  exact ⟨simpleRootInclusion F w, rootEvaluation_simpleRootInclusion F w⟩

/-- All roots in the real span of the two specified roots. This includes every
intermediate root in a B2 commutator, and also allows a rank-one span. -/
def rootPlane (a b : typeF4Roots) : Set typeF4Roots :=
  {r | typeF4RootPairing.root r ∈
    Submodule.span ℝ {typeF4RootPairing.root a, typeF4RootPairing.root b}}

abbrev RootPlaneWord (a b : typeF4Roots) := FreeGroup (rootPlane a b × F)

def rootPlaneInclusion (a b : typeF4Roots) : RootPlaneWord F a b →* RootWord F :=
  FreeGroup.lift fun x => FreeGroup.of (x.1.val, x.2)

omit [Field F] in
@[simp] theorem rootPlaneInclusion_of (a b : typeF4Roots) (r : rootPlane a b) (t : F) :
    rootPlaneInclusion F a b (FreeGroup.of (r, t)) = FreeGroup.of (r.val, t) :=
  FreeGroup.lift_apply_of

def rootPlaneEvaluation (a b : typeF4Roots) : RootPlaneWord F a b →* Cover F :=
  (rootEvaluation F).comp (rootPlaneInclusion F a b)

/-- The actual subsystem subgroup, including all roots in the plane. -/
def rootPlaneSubgroup (a b : typeF4Roots) : Subgroup (Cover F) :=
  (rootPlaneEvaluation F a b).range

def rootPlaneEvaluationRange (a b : typeF4Roots) :
    RootPlaneWord F a b →* rootPlaneSubgroup F a b :=
  (rootPlaneEvaluation F a b).rangeRestrict

def rootPlaneGenerator (a b : typeF4Roots) (r : rootPlane a b) (t : F) :
    rootPlaneSubgroup F a b :=
  rootPlaneEvaluationRange F a b (FreeGroup.of (r, t))

@[simp] theorem rootPlaneGenerator_val (a b : typeF4Roots) (r : rootPlane a b) (t : F) :
    (rootPlaneGenerator F a b r t).val =
      ExceptionalSplit.elementaryRoot typeF4RootPairing typeF4RootPairing_base F r.val t := by
  change rootEvaluation F (rootPlaneInclusion F a b (FreeGroup.of (r, t))) = _
  rw [rootPlaneInclusion_of, rootEvaluation_of]

theorem rootPlaneEvaluationRange_surjective (a b : typeF4Roots) :
    Function.Surjective (rootPlaneEvaluationRange F a b) := by
  rintro ⟨g, v, hv⟩
  exact ⟨v, Subtype.ext hv⟩

/-- The identity words supported on a root subsystem of rank at most two. -/
def rootPlaneRelators : Set (RootWord F) :=
  {w | ∃ (a b : typeF4Roots) (v : RootPlaneWord F a b),
    rootPlaneEvaluation F a b v = 1 ∧ rootPlaneInclusion F a b v = w}

def rootPlaneRelationSubgroup : Subgroup (RootWord F) :=
  Subgroup.normalClosure (rootPlaneRelators F)

theorem rootPlaneRelationSubgroup_le :
    rootPlaneRelationSubgroup F ≤ (rootEvaluation F).ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨a, b, v, hv, rfl⟩
  exact hv

theorem kills_rootPlaneRelators {G : Type*} [Group G] (ψ : RootWord F →* G)
    (hplanes : ∀ (a b : typeF4Roots) (v : RootPlaneWord F a b),
      rootPlaneEvaluation F a b v = 1 → ψ (rootPlaneInclusion F a b v) = 1) :
    rootPlaneRelationSubgroup F ≤ ψ.ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨a, b, v, hv, rfl⟩
  exact hplanes a b v hv

/-- Marked homomorphisms from the actual plane subgroups certify all plane
relations, retaining the literal root parameters. -/
theorem rootPlane_relations_of_local_homs {G : Type*} [Group G]
    (ψ : RootWord F →* G)
    (ρ : ∀ a b : typeF4Roots, rootPlaneSubgroup F a b →* G)
    (hρ : ∀ (a b : typeF4Roots) (r : rootPlane a b) (t : F),
      ρ a b (rootPlaneGenerator F a b r t) = ψ (FreeGroup.of (r.val, t)))
    (a b : typeF4Roots) (v : RootPlaneWord F a b)
    (hv : rootPlaneEvaluation F a b v = 1) :
    ψ (rootPlaneInclusion F a b v) = 1 := by
  have he : (ρ a b).comp (rootPlaneEvaluationRange F a b) =
      ψ.comp (rootPlaneInclusion F a b) := by
    apply FreeGroup.ext_hom
    rintro ⟨r, t⟩
    simpa only [MonoidHom.comp_apply, rootPlaneInclusion_of, rootPlaneGenerator] using
      hρ a b r t
  have hv' : rootPlaneEvaluationRange F a b v = 1 := Subtype.ext hv
  change (ψ.comp (rootPlaneInclusion F a b)) v = 1
  rw [← he]
  change ρ a b (rootPlaneEvaluationRange F a b v) = 1
  rw [hv', map_one]

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
