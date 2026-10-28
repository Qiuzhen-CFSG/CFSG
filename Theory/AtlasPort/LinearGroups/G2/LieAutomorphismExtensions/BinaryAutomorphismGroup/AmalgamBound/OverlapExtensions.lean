module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.OverlapExtensions.Basic
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.OverlapExtensions.Checks
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Actual
public import Theory.GroupTheory.Amalgam.SylowRigidity

/-!
# Every automorphism of the derived binary G₂ overlap extends on the left

The overlap has two generators. Their orders and the fourth power of their
product restrict their possible images to 32 pairs. Each pair is supplied
with a checked permutation of the left parabolic's word coordinates.
The permutation intertwines the two generator translations, so word induction
makes it a group automorphism. Its restriction equals the prescribed overlap
automorphism because both agree on the two overlap generators.

The final theorem applies this construction to the actual octonion-derived
parabolics through `binaryConcreteRealization`, including the literal overlap
embedding. It proves an endpoint extension, without assuming faithfulness or
an amalgam isomorphism. Source application: Aschbacher--Smith F.1.12(I)(8),
printed p.263; the word data retain the ATLAS attribution in LICENSES/ATLAS.txt.
-/

public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.OverlapExtensions
open Theory.GroupTheory RankTwoAmalgam

variable {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R}
    (E : AmalgamRealization leftTable rightTable α)
    (hi : Function.Injective α.left)

include hi in
private theorem middle_one : E.middle 0 = 1 := by
  apply hi
  rw [← E.left_overlap, middle_zero, E.left.one_eq, map_one]

include hi in
private theorem middle_mul (i j : Fin 32) :
    E.middle (middleMul i j) = E.middle i * E.middle j := by
  apply hi
  rw [map_mul, ← E.left_overlap, ← E.left_overlap, ← E.left_overlap,
    middle_product, E.left.mul_eq]

include hi in
private theorem middle_word (i : Fin 32) :
    groupWord (E.middle 1) (E.middle 2) (middleWord i) = E.middle i := by
  apply hi
  rw [map_groupWord, ← E.left_overlap, ← E.left_overlap, ← E.left_overlap,
    ← E.left.eval_eq, middle_words]

private def extensionPerm (k : Fin 32) : Equiv.Perm (Fin 96) where
  toFun := extension k
  invFun := inverse k
  left_inv := extension_inverse k
  right_inv := inverse_extension k

private noncomputable def endpointExtension (k : Fin 32) : MulAut L :=
  E.left.autOfPermutation left_valid (extensionPerm k)
    (extension_zero k) (extension_step k)

private theorem endpointExtension_apply (k : Fin 32) (i : Fin 96) :
    endpointExtension E k (E.left.equiv i) = E.left.equiv (extension k i) :=
  E.left.autOfPermutation_apply left_valid (extensionPerm k)
    (extension_zero k) (extension_step k) i

include hi in
private theorem exists_images (d : MulAut B) :
    ∃ k : Fin 32, d (E.middle 1) = E.middle (firstImage k) ∧
      d (E.middle 2) = E.middle (secondImage k) := by
  let x := E.middle.symm (d (E.middle 1))
  let y := E.middle.symm (d (E.middle 2))
  have hx : E.middle x = d (E.middle 1) := E.middle.apply_symm_apply _
  have hy : E.middle y = d (E.middle 2) := E.middle.apply_symm_apply _
  have h₁ : middleMul (middleMul x x) (middleMul x x) ≠ 0 := by
    intro he
    apply middle_relations.1
    apply E.middle.injective
    apply d.injective
    have he' := congrArg E.middle he
    simpa only [middle_mul E hi, middle_one E hi, hx, map_mul, map_one] using he'
  have h₂ : middleMul y y = 0 := by
    apply E.middle.injective
    rw [middle_mul E hi, hy, ← map_mul, ← middle_mul E hi,
      middle_relations.2.1, middle_one E hi, map_one]
  have h₃ : middleMul (middleMul (middleMul x y) (middleMul x y))
      (middleMul (middleMul x y) (middleMul x y)) = 0 := by
    apply E.middle.injective
    simp only [middle_mul E hi, hx, hy, ← map_mul]
    rw [← middle_mul E hi, ← middle_mul E hi, ← middle_mul E hi,
      middle_relations.2.2, middle_one E hi, map_one]
  obtain ⟨k, hk₁, hk₂⟩ := image_coverage x y h₁ h₂ h₃
  exact ⟨k, hx.symm.trans (congrArg E.middle hk₁),
    hy.symm.trans (congrArg E.middle hk₂)⟩

include E hi in
/-- The word-coordinate construction extends every overlap automorphism. -/
theorem extendsAcross_left (d : MulAut B) : ExtendsAcross α.left d := by
  obtain ⟨k, hk₁, hk₂⟩ := exists_images E hi d
  refine ⟨endpointExtension E k, ?_⟩
  have h₁ : endpointExtension E k (α.left (E.middle 1)) =
      α.left (d (E.middle 1)) := by
    rw [← E.left_overlap, endpointExtension_apply, (extension_generators k).1,
      E.left_overlap, hk₁]
  have h₂ : endpointExtension E k (α.left (E.middle 2)) =
      α.left (d (E.middle 2)) := by
    rw [← E.left_overlap, endpointExtension_apply, (extension_generators k).2,
      E.left_overlap, hk₂]
  intro b
  obtain ⟨i, rfl⟩ := E.middle.surjective b
  rw [← middle_word E hi i]
  change (endpointExtension E k).toMonoidHom
    (α.left (groupWord _ _ _)) = α.left (d.toMonoidHom (groupWord _ _ _))
  simp only [map_groupWord]
  exact congrArg₂ (fun x y : L => groupWord x y (middleWord i)) h₁ h₂

/-- The actual derived parabolic embedding has the extension property. -/
theorem binary_extendsAcross_left (d : MulAut binaryOverlap) :
    ExtendsAcross binaryAmalgam.left d :=
  extendsAcross_left binaryConcreteRealization
    (Subgroup.inclusion_injective inf_le_left) d

/-- All twists of the actual derived amalgam factor, even without faithfulness. -/
theorem binary_factorsThrough (d : MulAut binaryOverlap) :
    FactorsThrough binaryAmalgam d := by
  refine ⟨d, MulEquiv.refl _, binary_extendsAcross_left d, ?_, ?_⟩
  · exact ⟨MulEquiv.refl _, fun _ => rfl⟩
  · ext b
    rfl

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.OverlapExtensions
