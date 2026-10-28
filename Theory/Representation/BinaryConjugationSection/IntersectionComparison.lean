module
public import Theory.Representation.BinaryConjugationSection.Comparison
public import Theory.Representation.BinaryConjugationSection.QuotientSection

/-!
# The common actor on an intersection comparison

Two literal binary sections restrict to the intersection of their numerators.
The intersection of their actor groups preserves this domain, the second
image of the first kernel, and the first image of the second kernel. Thus
the coordinate comparison is an intertwiner for the entire common actor,
with the exact original intersection kernel. No extra normalizer hypotheses
are needed. The construction is used on U_L ∩ V₀ in the maximal-quotient
argument of Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.30, printed p.964.
-/

@[expose] public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W Z : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup Z] [Module (ZMod 2) Z]
  {H A N J B U : Subgroup G}
  {ρ : Representation (ZMod 2) H W} {σ : Representation (ZMod 2) J Z}
  (q : BinaryConjugationSection H A N ρ)
  (p : BinaryConjugationSection J B U σ)

include q p in
/-- The common actor preserves the intersection of the two numerators. -/
theorem intersection_normalized : H ⊓ J ≤ normalizer (A ⊓ B : Set G) :=
  fun _ ha => inf_normalizer_le_normalizer_inf ⟨q.normalized ha.1,p.normalized ha.2⟩

/-- The second image of the full intersection, with every common actor. -/
def intersectionSubrepresentation :
    Subrepresentation (σ.comp (inclusion (show H ⊓ J ≤ J from inf_le_right))) where
  toSubmodule := p.imageSpace (A ⊓ B)
  apply_mem_toSubmodule a w hw := p.imageSpace_apply_mem _ _
    (q.intersection_normalized p a.property) w hw

/-- The first image of the second kernel, with every common actor. -/
def otherKernelSubrepresentation :
    Subrepresentation (ρ.comp (inclusion (show H ⊓ J ≤ H from inf_le_left))) where
  toSubmodule := q.imageSpace U
  apply_mem_toSubmodule a w hw := q.imageSpace_apply_mem _ _
    (p.kernel_normalized a.property.2) w hw

/-- The first kernel's second image is invariant under the whole common actor. -/
def intersectionKernelSubrepresentation :
    Subrepresentation (σ.comp (inclusion (show H ⊓ J ≤ J from inf_le_right))) where
  toSubmodule := p.imageSpace ((A ⊓ B) ⊓ N)
  apply_mem_toSubmodule a w hw := p.imageSpace_apply_mem _ _
    (inf_normalizer_le_normalizer_inf
      ⟨q.intersection_normalized p a.property,q.kernel_normalized a.property.1⟩) w hw

/-- Canonical comparison as an actual intertwiner, with its literal kernel. -/
theorem exists_intersection_intertwiner (hUA : U ≤ A) :
    ∃ f : (q.intersectionSubrepresentation p).toRepresentation.IntertwiningMap
      (q.otherKernelSubrepresentation p).quotientRepresentation,
      (∀ x : ↥(A ⊓ B),
        f ⟨(p.coordinates (inclusion inf_le_right x)).toAdd,
          (p.mem_imageSpace_iff (A ⊓ B) _).mpr ⟨inclusion inf_le_right x,x.property,rfl⟩⟩ =
          (q.imageSpace U).mkQ (q.coordinates (inclusion inf_le_left x)).toAdd) ∧
      LinearMap.ker f.toLinearMap =
        (q.intersectionKernelSubrepresentation p).toSubmodule.comap
          (p.imageSpace (A ⊓ B)).subtype ∧
      (q.imageSpace (A ⊓ B) = ⊤ → Function.Surjective f) := by
  obtain ⟨f,hf⟩ := q.exists_image_quotient_comparison p (A ⊓ B) inf_le_left inf_le_right
  let F : (q.intersectionSubrepresentation p).toRepresentation.IntertwiningMap
      (q.otherKernelSubrepresentation p).quotientRepresentation := {
    f with
    isIntertwining' a := by
      ext w
      exact q.image_quotient_comparison_equivariant p (A ⊓ B) inf_le_left inf_le_right f hf
        (inclusion inf_le_left a) a.property.2 (q.intersection_normalized p a.property)
        (p.kernel_normalized a.property.2) w }
  exact ⟨F,hf,q.image_quotient_comparison_kernel p _ _ _ f hf (le_inf hUA p.kernel_le),
    fun hfull => q.image_quotient_comparison_surjective p _ _ _ f hf hfull⟩

/-- The intersection comparison restricts to the original comparison on any
smaller common subgroup, element by element. -/
theorem intersection_comparison_restrict
    (D : Subgroup G) (hDA : D ≤ A) (hDB : D ≤ B)
    (f : p.imageSpace D →ₗ[ZMod 2] W ⧸ q.imageSpace U)
    (hf : ∀ x : D, f ⟨(p.coordinates (inclusion hDB x)).toAdd,
      (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB x,x.property,rfl⟩⟩ =
        (q.imageSpace U).mkQ (q.coordinates (inclusion hDA x)).toAdd)
    (F : p.imageSpace (A ⊓ B) →ₗ[ZMod 2] W ⧸ q.imageSpace U)
    (hF : ∀ x : ↥(A ⊓ B), F ⟨(p.coordinates (inclusion inf_le_right x)).toAdd,
      (p.mem_imageSpace_iff (A ⊓ B) _).mpr ⟨inclusion inf_le_right x,x.property,rfl⟩⟩ =
        (q.imageSpace U).mkQ (q.coordinates (inclusion inf_le_left x)).toAdd)
    (w : p.imageSpace D) :
    F (Submodule.inclusion (p.imageSpace_mono (le_inf hDA hDB)) w) = f w := by
  obtain ⟨x,hx,hxw⟩ := (p.mem_imageSpace_iff D w.val).mp w.property
  let xD : D := ⟨x,hx⟩
  let xAB : ↥(A ⊓ B) := inclusion (le_inf hDA hDB) xD
  have hwD : (⟨(p.coordinates (inclusion hDB xD)).toAdd,
      (p.mem_imageSpace_iff D _).mpr ⟨inclusion hDB xD,hx,rfl⟩⟩ : p.imageSpace D) = w :=
    Subtype.ext hxw
  have hwAB : (⟨(p.coordinates (inclusion inf_le_right xAB)).toAdd,
      (p.mem_imageSpace_iff (A ⊓ B) _).mpr
        ⟨inclusion inf_le_right xAB,xAB.property,rfl⟩⟩ : p.imageSpace (A ⊓ B)) =
      Submodule.inclusion (p.imageSpace_mono (le_inf hDA hDB)) w := Subtype.ext hxw
  exact (congrArg F hwAB.symm).trans
    ((hF xAB).trans ((hf xD).symm.trans (congrArg f hwD)))

end Representation.BinaryConjugationSection
