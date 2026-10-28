module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.Data
/-!
# Verified matrices of the dual induced action

The equivalence `flatten` uses coordinate 3*i+j for slot i and component j.
A kernel-checked sparse-entry identity compares the two saved column matrices
with the inverse-transpose Schreier corrections in `Coordinates.generator_apply`.
Linearity then proves `generator_coordinates` for every vector of the actual
induced coordinate representation.

Only the nonzero 3-by-3 blocks need inverse-transpose calculations. The row
Decidable instance avoids recursive instance search across two 66-element
quantifiers; it is an ordinary finite decision procedure checked by the kernel.
No basis-change, invariant-flag or factor-simplicity assertion is made here.

Data and attribution: `source/README.md`. Source context: Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7.
-/

@[expose] public noncomputable section
open Representation
open Representation.SL3FourLocalCatalogue
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration
open Uniqueness.PointRestriction.PointModel

def index (i : Fin 22) (j : Fin 3) : Fin 66 := ⟨3 * i.val + j.val, by omega⟩
def slot (q : Fin 66) : Fin 22 := ⟨q.val / 3, by omega⟩
def component (q : Fin 66) : Fin 3 := ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩

@[simp] lemma slot_index (i : Fin 22) (j : Fin 3) : slot (index i j) = i := by
  apply Fin.ext
  dsimp [slot, index]
  omega
@[simp] lemma component_index (i : Fin 22) (j : Fin 3) : component (index i j) = j := by
  apply Fin.ext
  dsimp [component, index]
  omega
@[simp] lemma index_slot_component (q : Fin 66) : index (slot q) (component q) = q := by
  apply Fin.ext
  dsimp [slot, component, index]
  omega

/-- Flatten the actual 22 slots in the specified column convention. -/
def flatten : Space ≃ₗ[F] (Fin 66 → F) where
  toFun v q := v (slot q) (component q)
  invFun v i j := v (index i j)
  left_inv v := by funext i j; simp
  right_inv v := by funext q; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma flatten_index (v : Space) (i : Fin 22) (j : Fin 3) :
    flatten v (index i j) = v i j := by
  change v (slot (index i j)) (component (index i j)) = _
  rw [slot_index, component_index]

private instance sparseRowDecidable (a : Fin 2) (r : Fin 66) :
    Decidable (∀ q : Fin 66,
      ambientMatrix a r q =
        if slot r = ambientPermutation a (slot q) then
          (Matrix.SpecialLinearGroup.inverseTranspose
            (SchreierCertificate.referenceElement
              (SchreierCertificate.schreierIndex (slot q) a))).val (component r) (component q)
        else 0) := Fintype.decidableForallFintype

set_option Elab.async false in
/-- The sparse entries of the saved matrices agree with the actual Schreier corrections. -/
lemma ambient_sparse : ∀ (a : Fin 2) (r q : Fin 66),
    ambientMatrix a r q =
      if slot r = ambientPermutation a (slot q) then
        (Matrix.SpecialLinearGroup.inverseTranspose
          (SchreierCertificate.referenceElement
            (SchreierCertificate.schreierIndex (slot q) a))).val (component r) (component q)
      else 0 := by decide +kernel

lemma index_eq_iff (i : Fin 22) (j : Fin 3) (q : Fin 66) :
    index i j = q ↔ i = slot q ∧ j = component q := by
  constructor
  · intro h
    constructor
    · simpa using congrArg slot h
    · simpa using congrArg component h
  · rintro ⟨rfl, rfl⟩
    exact index_slot_component q

lemma flatten_symm_single (q : Fin 66) (i : Fin 22) :
    flatten.symm (Pi.single q 1) i =
      if i = slot q then Pi.single (component q) 1 else 0 := by
  funext j
  by_cases hi : i = slot q
  · subst i
    simp [flatten, Pi.single_apply, index_eq_iff]
  · simp [flatten, index_eq_iff, hi]

private lemma generator_basis (a : Fin 2) (q : Fin 66) (i : Fin 22) (j : Fin 3) :
    constituent .dual
      (SchreierCertificate.referenceElement (SchreierCertificate.schreierIndex i a))
      (flatten.symm (Pi.single q 1) i) j =
        ambientMatrix a (index (ambientPermutation a i) j) q := by
  rw [flatten_symm_single, ambient_sparse, slot_index, component_index]
  by_cases hi : i = slot q
  · subst i
    rw [if_pos rfl, if_pos rfl]
    change ((Matrix.SpecialLinearGroup.inverseTranspose
      (SchreierCertificate.referenceElement
        (SchreierCertificate.schreierIndex (slot q) a))).val).mulVec
          (Pi.single (component q) 1) j = _
    rw [Matrix.mulVec_single_one]
    rfl
  · rw [if_neg hi, if_neg ((ambientPermutation a).injective.ne hi), map_zero]
    rfl

/-- The saved column matrices are the actual two generator actions. -/
lemma generator_coordinates (a : Fin 2) (v : Space) :
    flatten (fieldRepresentation .dual (ambientGenerator a) v) =
      (ambientMatrix a).mulVec (flatten v) := by
  let f : Module.End F (Fin 66 → F) :=
    flatten.toLinearMap.comp
      ((fieldRepresentation .dual (ambientGenerator a)).comp flatten.symm.toLinearMap)
  have hf : f = (ambientMatrix a).mulVecLin := by
    apply (Pi.basisFun F (Fin 66)).ext
    intro q
    funext r
    obtain ⟨i, hi⟩ := (ambientPermutation a).surjective (slot r)
    have hr : index (ambientPermutation a i) (component r) = r := by
      rw [hi, index_slot_component]
    simp only [f, Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Matrix.mulVecLin_apply]
    rw [← hr]
    change flatten (fieldRepresentation .dual (ambientGenerator a)
      (flatten.symm (Pi.single q 1))) (index (ambientPermutation a i) (component r)) =
        (ambientMatrix a).mulVec (Pi.single q 1) (index (ambientPermutation a i) (component r))
    rw [flatten_index, Matrix.mulVec_single_one]
    change representation .dual (ambientGenerator a) (flatten.symm (Pi.single q 1))
      (ambientPermutation a i) (component r) = _
    rw [generator_apply]
    exact generator_basis a q i (component r)
  have h := LinearMap.congr_fun hf (flatten v)
  change flatten (fieldRepresentation .dual (ambientGenerator a)
    (flatten.symm (flatten v))) = _ at h
  simpa only [flatten.symm_apply_apply, Matrix.mulVecLin_apply] using h

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration
