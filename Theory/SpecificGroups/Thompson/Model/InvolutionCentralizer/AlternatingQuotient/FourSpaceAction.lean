module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.Words
public import Mathlib.Data.Set.Finite.Basic
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.FourSpaceAction.Lifted
/-!
# The actual nine-four-space action of the Thompson max3 word subgroup

The nine distinct 25-dimensional spaces are inverse images of the certified
four-spaces in the literal 29/21 section. Generator multiplication preserves
their finite incidence set. Bijectivity upgrades forward preservation to an
equivalence, and compatibility is closed under products and inverses.
Distinctness then makes the permutation unique for each actual matrix-group
element, so the action descends to `wordSubgroup`.

Only the two literal matrix-image equalities remain as inputs. The parent
assembly must discharge them using the independent word certificates.
Right row actions give the inverses of the point maps in `Permutations`.
Source: GLS3 Table 5.3x and Aschbacher--Smith A.2.19, printed pp.40--41;
ATLAS and witness provenance is in `AlternatingQuotient/source/README.md`.
-/

public section
open scoped Matrix
namespace Thompson.InvolutionCentralizer.AlternatingQuotient

private theorem finite_incidence_iff {I V : Type*} [Finite I] [Finite V]
    (spaces : I → Set V) (p : Equiv.Perm I) (e : V ≃ V)
    (h : ∀ i v, v ∈ spaces i → e v ∈ spaces (p i)) (i : I) (v : V) :
    v ∈ spaces i ↔ e v ∈ spaces (p i) := by
  let S : Set (I × V) := {x | x.2 ∈ spaces x.1}
  let f : I × V → I × V := fun x => (p x.1, e x.2)
  have hf : Function.Injective f := by
    intro x y hxy
    exact Prod.ext (p.injective (congrArg Prod.fst hxy))
      (e.injective (congrArg Prod.snd hxy))
  have hm : Set.MapsTo f S S := fun x hx => h x.1 x.2 hx
  have hb := ((Set.toFinite S).injOn_iff_bijOn_of_mapsTo hm).mp hf.injOn
  refine ⟨h i v, fun hv => ?_⟩
  obtain ⟨x, hx, he⟩ := hb.surjOn (show f (i, v) ∈ S from hv)
  change (i, v) ∈ S
  exact hf he ▸ hx

private def rowEquiv (g : Model) : (Fin 248 → ZMod 2) ≃ (Fin 248 → ZMod 2) where
  toFun v := v ᵥ* matrixHom g
  invFun v := v ᵥ* matrixHom g⁻¹
  left_inv v := by
    change (v ᵥ* matrixHom g) ᵥ* matrixHom g⁻¹ = v
    rw [Matrix.vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one, Matrix.vecMul_one]
  right_inv v := by
    change (v ᵥ* matrixHom g⁻¹) ᵥ* matrixHom g = v
    rw [Matrix.vecMul_vecMul, ← map_mul, inv_mul_cancel, map_one, Matrix.vecMul_one]

variable (spaces : Fin 9 → Submodule (ZMod 2) (Fin 248 → ZMod 2))

private def Compatible (g : Model) (p : Equiv.Perm (Fin 9)) : Prop :=
  ∀ i v, v ∈ spaces i ↔ v ᵥ* matrixHom g ∈ spaces (p⁻¹ i)

private theorem compatible_one : Compatible spaces 1 1 := by
  intro i v
  simp

private theorem compatible_mul {g h : Model} {p q : Equiv.Perm (Fin 9)}
    (hg : Compatible spaces g p) (hh : Compatible spaces h q) :
    Compatible spaces (g * h) (p * q) := by
  intro i v
  have ht := (hg i v).trans (hh (p⁻¹ i) (v ᵥ* matrixHom g))
  simpa only [map_mul, Matrix.vecMul_vecMul, mul_inv_rev, Equiv.Perm.mul_apply] using ht

private theorem compatible_inv {g : Model} {p : Equiv.Perm (Fin 9)}
    (h : Compatible spaces g p) : Compatible spaces g⁻¹ p⁻¹ := by
  intro i v
  have ht := (h (p i) (v ᵥ* matrixHom g⁻¹)).symm
  simpa only [Matrix.vecMul_vecMul, ← map_mul, inv_mul_cancel, map_one,
    Matrix.vecMul_one, inv_inv, Equiv.Perm.inv_def, Equiv.symm_apply_apply, Equiv.symm_symm] using ht

private theorem compatible_unique (hinj : Function.Injective spaces)
    {g : Model} {p q : Equiv.Perm (Fin 9)}
    (hp : Compatible spaces g p) (hq : Compatible spaces g q) : p = q := by
  apply inv_injective
  apply Equiv.ext
  intro i
  apply hinj
  apply Submodule.ext
  intro v
  obtain ⟨w, rfl⟩ := (rowEquiv g).surjective v
  exact (hp i w).symm.trans (hq i w)

private theorem compatible_of_forward {g : Model} {p : Equiv.Perm (Fin 9)}
    (h : ∀ i v, v ∈ spaces i → v ᵥ* matrixHom g ∈ spaces (p⁻¹ i)) :
    Compatible spaces g p :=
  fun i v => finite_incidence_iff (fun i => (spaces i : Set (Fin 248 → ZMod 2)))
    p⁻¹ (rowEquiv g) h i v

private theorem compatible_wordA (hA : matrixHom wordA = wordAMatrix) :
    Compatible liftedBlockSpace wordA permA := by
  apply compatible_of_forward
  intro i v hv
  rw [hA]
  exact liftedBlockSpace_wordA i hv

private theorem compatible_wordB (hB : matrixHom wordB = wordBMatrix) :
    Compatible liftedBlockSpace wordB permB := by
  apply compatible_of_forward
  intro i v hv
  rw [hB]
  exact liftedBlockSpace_wordB i hv

private def actionGroup : Subgroup Model where
  carrier := {g | ∃ p : Equiv.Perm (Fin 9), Compatible liftedBlockSpace g p}
  one_mem' := ⟨1, compatible_one _⟩
  mul_mem' := by
    rintro g h ⟨p, hp⟩ ⟨q, hq⟩
    exact ⟨p * q, compatible_mul _ hp hq⟩
  inv_mem' := by
    rintro g ⟨p, hp⟩
    exact ⟨p⁻¹, compatible_inv _ hp⟩

private theorem wordSubgroup_le_actionGroup
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix) :
    wordSubgroup ≤ actionGroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact ⟨permA, compatible_wordA hA⟩
  · rcases Set.mem_singleton_iff.mp hg with rfl
    exact ⟨permB, compatible_wordB hB⟩

private theorem exists_compatible
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix)
    (g : wordSubgroup) : ∃ p : Equiv.Perm (Fin 9), Compatible liftedBlockSpace g.val p :=
  wordSubgroup_le_actionGroup hA hB g.property

/-- The permutation of the nine actual four-spaces, realized on their lifts.
The inputs are precisely the two matrix-image certificates for the source words. -/
noncomputable def fourSpaceAction
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix) :
    wordSubgroup →* Equiv.Perm (Fin 9) where
  toFun g := Classical.choose (exists_compatible hA hB g)
  map_one' := compatible_unique _ liftedBlockSpace_injective
    (Classical.choose_spec (exists_compatible hA hB 1)) (compatible_one _)
  map_mul' g h := compatible_unique _ liftedBlockSpace_injective
    (Classical.choose_spec (exists_compatible hA hB (g * h)))
    (compatible_mul _ (Classical.choose_spec (exists_compatible hA hB g))
      (Classical.choose_spec (exists_compatible hA hB h)))

/-- Exact equivariance for every actual element, independent of its word expression. -/
theorem fourSpaceAction_spec
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix)
    (g : wordSubgroup) (i : Fin 9) (v : Fin 248 → ZMod 2) :
    v ∈ liftedBlockSpace i ↔
      v ᵥ* matrixHom g.val ∈ liftedBlockSpace ((fourSpaceAction hA hB g)⁻¹ i) :=
  Classical.choose_spec (exists_compatible hA hB g) i v

/-- The source max3 first output induces precisely the fixed inverse point map. -/
theorem fourSpaceAction_generatorX
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix) :
    fourSpaceAction hA hB generatorX = permA :=
  compatible_unique _ liftedBlockSpace_injective
    (fourSpaceAction_spec hA hB generatorX) (compatible_wordA hA)

/-- The source max3 second output induces precisely the fixed inverse point map. -/
theorem fourSpaceAction_generatorY
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix) :
    fourSpaceAction hA hB generatorY = permB :=
  compatible_unique _ liftedBlockSpace_injective
    (fourSpaceAction_spec hA hB generatorY) (compatible_wordB hB)

/-- The homomorphism permutes the literal lifted subspaces by matrix multiplication. -/
theorem fourSpaceAction_map_liftedBlockSpace
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix)
    (g : wordSubgroup) (i : Fin 9) :
    (liftedBlockSpace i).map (matrixHom g.val).vecMulLinear =
      liftedBlockSpace ((fourSpaceAction hA hB g)⁻¹ i) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (fourSpaceAction_spec hA hB g i w).mp hw
  · intro hv
    obtain ⟨w, rfl⟩ := (rowEquiv g.val).surjective v
    exact ⟨w, (fourSpaceAction_spec hA hB g i w).mpr hv, rfl⟩

/-- The exact action contract consumed by the alternating-quotient assembly. -/
theorem exists_fourSpaceAction_of_matrix_images
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix) :
    ∃ f : wordSubgroup →* Equiv.Perm (Fin 9),
      f generatorX = permA ∧ f generatorY = permB :=
  ⟨fourSpaceAction hA hB, fourSpaceAction_generatorX hA hB, fourSpaceAction_generatorY hA hB⟩

private theorem invariant_of_generators
    (U : Submodule (ZMod 2) (Fin 248 → ZMod 2))
    (hA : ∀ v ∈ U, v ᵥ* matrixHom wordA ∈ U)
    (hB : ∀ v ∈ U, v ᵥ* matrixHom wordB ∈ U)
    (g : wordSubgroup) (v : Fin 248 → ZMod 2) :
    v ∈ U ↔ v ᵥ* matrixHom g.val ∈ U := by
  let H : Subgroup Model :=
    { carrier := {g | Compatible (fun _ => U) g 1}
      one_mem' := compatible_one _
      mul_mem' := fun hg hh => by simpa using compatible_mul _ (p := 1) (q := 1) hg hh
      inv_mem' := fun hg => by simpa using compatible_inv _ (p := 1) hg }
  have hle : wordSubgroup ≤ H := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact compatible_of_forward _ (p := 1) (fun _ v hv => hA v hv)
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact compatible_of_forward _ (p := 1) (fun _ v hv => hB v hv)
  exact hle g.property (0 : Fin 9) v

/-- Every word-subgroup element preserves the actual 29-dimensional section. -/
theorem sectionSpace_invariant
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix)
    (g : wordSubgroup) (v : Fin 248 → ZMod 2) :
    v ∈ sectionSpace ↔ v ᵥ* matrixHom g.val ∈ sectionSpace := by
  apply invariant_of_generators
  · intro w hw
    rw [hA]
    exact sectionSpace_wordA hw
  · intro w hw
    rw [hB]
    exact sectionSpace_wordB hw

/-- Every word-subgroup element preserves the literal 21-dimensional denominator. -/
theorem denominatorSpace_invariant
    (hA : matrixHom wordA = wordAMatrix) (hB : matrixHom wordB = wordBMatrix)
    (g : wordSubgroup) (v : Fin 248 → ZMod 2) :
    v ∈ denominatorSpace ↔ v ᵥ* matrixHom g.val ∈ denominatorSpace := by
  apply invariant_of_generators
  · intro w hw
    rw [hA]
    exact denominatorSpace_wordA hw
  · intro w hw
    rw [hB]
    exact denominatorSpace_wordB hw

end Thompson.InvolutionCentralizer.AlternatingQuotient
