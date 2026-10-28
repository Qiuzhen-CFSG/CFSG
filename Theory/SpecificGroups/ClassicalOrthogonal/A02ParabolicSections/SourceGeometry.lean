module
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry.Root

/-!
# Actual split orthogonal sections in proper root normalizers

Complement extension fixes the first hyperbolic plane and embeds the literal
smaller Siegel-generated group. Iteration and the injective characteristic-two
scalar quotient give the same embedding on the projective carriers. Its image
normalizes the singular-direction root group, whose proper normalizer and
nontrivial two-group certificate are constructed in `SourceGeometry.Root`.

`splitTailSection` retains this actual numerator and its marking, for the
A.2.15(2) consumer in `EvenLie.OrthogonalSections.Source`.
Source: Aschbacher–Smith A.2.18, printed p.40; GLS3 §2.6.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.A02ParabolicSections
open Theory.AlgebraicGroup Quadratic ReflectionGeneration Subgroup
open Theory.SpecificGroups.LieType TheoremDRootNormalizer
universe u
variable {F : Type u} [Field F]

def tailFull (r : ℕ) : quadraticIsometrySubgroup (formD r F) →*
    quadraticIsometrySubgroup (formD (r+1) F) :=
  (complementLift (formD (r+1) F) (e 0) (f 0) (formD_e 0) (formD_f 0)
    (polarD_ef 0)).comp (isometryGroupTransport (standardComplementD (F:=F) (n:=r)).symm).toMonoidHom

theorem tailFull_injective (r : ℕ) : Function.Injective (tailFull (F:=F) r) :=
  (complementLift_injective (formD (r+1) F) (e 0) (f 0)
    (formD_e 0) (formD_f 0) (polarD_ef 0)).comp
    (isometryGroupTransport (standardComplementD (F:=F) (n:=r)).symm).injective

theorem tailFull_mem (r : ℕ) (g : OmegaPlus r F) :
    tailFull r g.val ∈ elementarySubgroup (formD (r+1) F) :=
  complementLift_mem_elementary (formD (r+1) F) (e 0) (f 0)
    (formD_e 0) (formD_f 0) (polarD_ef 0) _
    (isometryTransport_mem_elementary (standardComplementD (F:=F) (n:=r)).symm g.val g.prop)

def tailHom (r : ℕ) : OmegaPlus r F →* OmegaPlus (r+1) F :=
  ((tailFull r).comp (elementarySubgroup (formD r F)).subtype).codRestrict _ (tailFull_mem r)

theorem tailHom_injective (r : ℕ) : Function.Injective (tailHom (F:=F) r) := by
  intro g h hgh
  apply Subtype.ext
  have he : tailFull r g.val = tailFull r h.val := congrArg (fun x : OmegaPlus (r+1) F => x.val) hgh
  exact tailFull_injective r he

theorem tailHom_fix (r : ℕ) (g : OmegaPlus r F) :
    (tailHom r g).val.val (e 0) = e 0 :=
  complementLift_fix_e (formD (r+1) F) (e 0) (f 0)
    (formD_e 0) (formD_f 0) (polarD_ef 0) _

def tailIter (r : ℕ) : (n : ℕ) → OmegaPlus r F →* OmegaPlus (r+n+1) F
  | 0 => tailHom r
  | n+1 => (tailHom (r+n+1)).comp (tailIter r n)

theorem tailIter_injective (r n : ℕ) : Function.Injective (tailIter (F:=F) r n) := by
  induction n with
  | zero => exact tailHom_injective r
  | succ n ih => exact (tailHom_injective _).comp ih

theorem tailIter_fix (r n : ℕ) (g : OmegaPlus r F) :
    (tailIter r n g).val.val (e 0) = e 0 := by
  cases n <;> exact tailHom_fix _ _

variable [CharP F 2]

def projectiveRootGroup {r : ℕ} (i : Fin r) : Subgroup (POmegaPlus r F) :=
  (splitRootGroup i).map (projectiveElementaryMap (formD r F))

theorem projectiveRootGroup_two {r : ℕ} (i : Fin r) : IsPGroup 2 (projectiveRootGroup (F:=F) i) :=
  (rootGroup_two (formD r F) (e i) (formD_e i)).of_equiv
    ((splitRootGroup i).equivMapOfInjective _ (elementaryProjective_injective _))

theorem projectiveRootGroup_ne_bot {r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    projectiveRootGroup (F:=F) i ≠ ⊥ := by
  intro h
  exact splitRootGroup_ne_bot (F:=F) hij
    ((Subgroup.map_eq_bot_iff_of_injective _ (elementaryProjective_injective _)).mp h)

theorem projectiveRootNormalizer_ne_top {r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    normalizer (projectiveRootGroup (F:=F) i : Set (POmegaPlus r F)) ≠ ⊤ := by
  intro ht
  apply splitRootNormalizer_ne_top (F:=F) hij
  apply Subgroup.map_injective (elementaryProjective_injective (formD r F))
  rw [map_normalizer_eq_of_bijective _
    ⟨elementaryProjective_injective _, projectiveElementaryMap_surjective _⟩,
    Subgroup.map_top_of_surjective _ (projectiveElementaryMap_surjective _)]
  exact ht

def projectiveTail (r n : ℕ) : POmegaPlus r F →* POmegaPlus (r+n+1) F :=
  (projectiveElementaryMap (formD (r+n+1) F)).comp
    ((tailIter r n).comp (elementaryProjectiveEquiv (formD r F)).symm.toMonoidHom)

theorem projectiveTail_injective (r n : ℕ) : Function.Injective (projectiveTail (F:=F) r n) :=
  (elementaryProjective_injective _).comp
    ((tailIter_injective r n).comp (elementaryProjectiveEquiv _).symm.injective)

theorem projectiveTail_range_le (r n : ℕ) : (projectiveTail (F:=F) r n).range ≤
    normalizer (projectiveRootGroup (F:=F) (0:Fin (r+n+1)) : Set (POmegaPlus (r+n+1) F)) := by
  rintro _ ⟨g,rfl⟩
  rw [projectiveRootGroup, ← map_normalizer_eq_of_bijective _
    ⟨elementaryProjective_injective _, projectiveElementaryMap_surjective _⟩]
  refine ⟨tailIter r n ((elementaryProjectiveEquiv _).symm g), ?_, rfl⟩
  exact fix_mem_rootNormalizer _ _ _ _ (tailIter_fix _ _ _)

/-- The literal smaller projective orthogonal carrier is a section of the
normalizer of the first singular-vector root group. -/
def splitTailSection (r n : ℕ) (hr : 1 ≤ r) :
    NormalizerSection (POmegaPlus (r+n+1) F) (POmegaPlus r F) :=
  NormalizerSection.ofEmbedding (projectiveRootGroup (0:Fin (r+n+1)))
    (projectiveRootGroup_ne_bot (j:=⟨1,by omega⟩) (by simp))
    (projectiveRootGroup_two _) (projectiveRootNormalizer_ne_top (j:=⟨1,by omega⟩) (by simp))
    (projectiveTail r n) (projectiveTail_injective r n) (projectiveTail_range_le r n)

end ClassicalOrthogonal.A02ParabolicSections
