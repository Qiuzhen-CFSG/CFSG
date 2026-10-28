module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Generation

/-!
# Transport from the native sextet permutation space

An injective list of partitions and its two native generator equations define
an action of the entire native M24 on the index set: the stabilizer of the
listed set contains both generators and hence is the full group. Functions
transform by the inverse point action. The covector equations make their
image invariant; finiteness handles inverses in the subgroup induction.
Restricting to that image and transporting along the embedding gives the
literal degree-252 matrices, with no irreducibility premise.

The geometric and matrix hypotheses below are finite certificate obligations,
not asserted identities. The final assembly must discharge all of them.
Source: James, J. Algebra 27 (1973), 57–111; GM02, Proposition 5.1;
`Degrees120252/source/README.md` for the saved sextet construction.
-/

@[expose] public noncomputable section
open scoped Pointwise
open Sporadic.Mathieu
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252

variable (hp : Function.Injective pointParts)
  (hm : ∀ j i, actor j • pointParts i = pointParts (forward j i))

include hp hm in
theorem forward_bijective (j : Fin 2) : Function.Bijective (forward j) := by
  have hi : Function.Injective (forward j) := by
    intro i k h
    apply hp
    apply MulAction.injective (actor j)
    change actor j • pointParts i = actor j • pointParts k
    rw [hm, hm, h]
  exact ⟨hi, Finite.surjective_of_injective hi⟩

include hp hm in
theorem range_stable (g : M24) : g • Set.range pointParts = Set.range pointParts := by
  have hle : Subgroup.closure (Set.range actor) ≤
      MulAction.stabilizer M24 (Set.range pointParts) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    change actor j • Set.range pointParts = Set.range pointParts
    rw [← Set.range_smul]
    have he : (fun i => actor j • pointParts i) = pointParts ∘ forward j := funext (hm j)
    rw [he, Set.range_comp, Set.range_eq_univ.mpr (forward_bijective hp hm j).surjective,
      Set.image_univ]
  exact hle (by rw [actors_closure_eq_top]; trivial)

/-- The native action on the listed partitions, using their actual point labels. -/
def index (g : M24) (i : Fin 1771) : Fin 1771 :=
  Classical.choose (show g • pointParts i ∈ Set.range pointParts from by
    rw [← range_stable hp hm g]
    exact Set.smul_mem_smul_set (Set.mem_range_self i))

theorem pointParts_index (g : M24) (i : Fin 1771) :
    pointParts (index hp hm g i) = g • pointParts i :=
  Classical.choose_spec (show g • pointParts i ∈ Set.range pointParts from by
    rw [← range_stable hp hm g]
    exact Set.smul_mem_smul_set (Set.mem_range_self i))

theorem index_one (i : Fin 1771) : index hp hm 1 i = i := by
  apply hp
  rw [pointParts_index, one_smul]

theorem index_mul (g h : M24) (i : Fin 1771) :
    index hp hm (g * h) i = index hp hm g (index hp hm h i) := by
  apply hp
  rw [pointParts_index, pointParts_index, pointParts_index, mul_smul]

theorem index_actor (j : Fin 2) (i : Fin 1771) :
    index hp hm (actor j) i = forward j i := by
  apply hp
  rw [pointParts_index, hm]

/-- Functions transform by the inverse native action. -/
def permutationRepresentation : Representation (ZMod 2) M24 (Fin 1771 → ZMod 2) where
  toFun g := {
    toFun v i := v (index hp hm g⁻¹ i)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    change v (index hp hm (1 : M24)⁻¹ i) = v i
    rw [inv_one, index_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    change v (index hp hm (g * h)⁻¹ i) =
      v (index hp hm h⁻¹ (index hp hm g⁻¹ i))
    rw [mul_inv_rev, index_mul]

theorem permutationRepresentation_actor (j : Fin 2) (v : Fin 1771 → ZMod 2)
    (i : Fin 1771) :
    permutationRepresentation hp hm (actor j) v (forward j i) = v i := by
  change v (index hp hm (actor j)⁻¹ (forward j i)) = v i
  rw [← index_actor hp hm, ← index_mul, inv_mul_cancel, index_one]

variable (hE : Function.Injective embedding)
  (hEA : ∀ j i k, (embeddingMatrix * matrix252 j) (forward j i) k = embeddingMatrix i k)

include hEA in
theorem embedding_actor (j : Fin 2) (v : Fin 252 → ZMod 2) :
    embedding ((matrix252 j).mulVec v) =
      permutationRepresentation hp hm (actor j) (embedding v) := by
  funext k
  obtain ⟨i, rfl⟩ := (forward_bijective hp hm j).surjective k
  rw [permutationRepresentation_actor]
  change (embeddingMatrix.mulVec ((matrix252 j).mulVec v)) (forward j i) =
    embeddingMatrix.mulVec v i
  rw [Matrix.mulVec_mulVec]
  change (∑ k, (embeddingMatrix * matrix252 j) (forward j i) k * v k) = _
  simp only [hEA]
  rfl

include hp hm hEA in
theorem embedding_range_invariant (g : M24) :
    LinearMap.range embedding ≤
      (LinearMap.range embedding).comap (permutationRepresentation hp hm g) := by
  have hg : g ∈ Subgroup.closure (Set.range actor) := by
    rw [actors_closure_eq_top]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    rintro _ ⟨v, rfl⟩
    exact ⟨(matrix252 j).mulVec v, embedding_actor hp hm hEA j v⟩
  | one => intro v hv; simpa using hv
  | inv g _ ih =>
    let f : LinearMap.range embedding → LinearMap.range embedding :=
      fun v => ⟨permutationRepresentation hp hm g v, ih v.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact (Representation.apply_bijective (permutationRepresentation hp hm) g).injective
        (congrArg Subtype.val h)
    intro v hv
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have he : permutationRepresentation hp hm g w = v := congrArg Subtype.val hw
    change permutationRepresentation hp hm g⁻¹ v ∈ LinearMap.range embedding
    rw [← he, Representation.inv_self_apply]
    exact w.property
  | mul g h _ _ hg hh =>
    intro v hv
    have he : permutationRepresentation hp hm g
        (permutationRepresentation hp hm h v) ∈ LinearMap.range embedding := hg (hh hv)
    change permutationRepresentation hp hm (g * h) v ∈ LinearMap.range embedding
    simpa only [map_mul, Module.End.mul_apply] using he

/-- Restrict to the image, then use the injective covector coordinates. -/
def transportRealization : NativeRealization 252 matrix252 where
  representation :=
    (LinearEquiv.ofInjective embedding hE).symm.conjRingEquiv.toMonoidHom.comp
      ((permutationRepresentation hp hm).subrepresentation (LinearMap.range embedding)
        (embedding_range_invariant hp hm hEA))
  matrix_actor j := by
    have he :
        (LinearEquiv.ofInjective embedding hE).symm.conjRingEquiv
          (((permutationRepresentation hp hm).subrepresentation (LinearMap.range embedding)
            (embedding_range_invariant hp hm hEA)) (actor j)) =
        Matrix.toLin' (matrix252 j) := by
      apply LinearMap.ext
      intro v
      apply hE
      change embedding ((LinearEquiv.ofInjective embedding hE).symm
        ⟨permutationRepresentation hp hm (actor j) (embedding v), _⟩) =
          embedding ((matrix252 j).mulVec v)
      rw [LinearEquiv.ofInjective_symm_apply]
      exact (embedding_actor hp hm hEA j v).symm
    exact (congrArg LinearMap.toMatrix' he).trans (LinearMap.toMatrix'_toLin' _)

/-- The coordinate action is the restriction of the native permutation action
under the saved embedding, for every native group element. -/
theorem transportRealization_equivariant (g : M24) (v : Fin 252 → ZMod 2) :
    embedding ((transportRealization hp hm hE hEA).representation g v) =
      permutationRepresentation hp hm g (embedding v) := by
  change embedding ((LinearEquiv.ofInjective embedding hE).symm
    ⟨permutationRepresentation hp hm g (embedding v), _⟩) = _
  rw [LinearEquiv.ofInjective_symm_apply]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252
