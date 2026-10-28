module
public import Theory.GroupAction.BinaryWreathPointStabilizer

@[expose] public section
/-!
# Orbits and singular point stabilizers of the binary orthogonal four-space

The matrix wreath action is transitive on the six nonzero vectors supported
on a single definite plane. Each of the nine vectors nonzero on both planes
has stabilizer of order eight. The plane transitivity and the small stabilizer
count use finite kernel reduction; the wreath transport is structural.

Source application: Aschbacher--Smith, 14.6.17(3--4), printed p.1036.
-/

open Subgroup
namespace BinaryWreathPointStabilizer
attribute [local instance] FourGroupMatrixCoordinates.naturalAction
attribute [local instance] RegularWreathProduct.functionModule

private instance planeOrbitDecidable (v w : Plane) : Decidable (∃ a : MatrixActor, a • v = w) :=
  Fintype.decidableExistsFintype

private theorem plane_transitive : ∀ v w : Plane, v ≠ 1 → w ≠ 1 →
    ∃ a : MatrixActor, a • v = w := by decide +kernel

/-- The two definite planes form one orbit on their nonzero vectors. -/
theorem supported_transitive {i j : Index} {v w : Vector}
    (hv : Supported i v) (hw : Supported j w) (hvn : v ≠ 1) (hwn : w ≠ 1) :
    ∃ a : Actor, a • v = w := by
  obtain ⟨b,hb⟩ := plane_transitive (v i) (w j) (value_ne_one hv hvn) (value_ne_one hw hwn)
  let a : Actor := ⟨fun k => if k = j then b else 1,j * i⁻¹⟩
  refine ⟨a,?_⟩
  funext k
  change (if k = j then b else 1) • v ((j * i⁻¹)⁻¹ * k) = w k
  by_cases hk : k = j
  · subst k
    simpa only [ite_true,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hb
  · rw [if_neg hk,one_smul,hw k hk,hv]
    intro he
    apply hk
    have he' := congrArg (fun x => (j * i⁻¹) * x) he
    simpa [mul_assoc] using he'

private instance vectorOrbitFintype : Fintype Actor := Fintype.ofEquiv ((Index → MatrixActor) × Index)
  (RegularWreathProduct.equivProd MatrixActor Index).symm
private instance vectorStabilizerDecidable (v : Vector) : DecidablePred (· ∈ MulAction.stabilizer Actor v) :=
  fun a => inferInstanceAs (Decidable (a • v = v))

private theorem singular_card_check : ∀ v : Vector, (∀ i, v i ≠ 1) →
    Fintype.card (MulAction.stabilizer Actor v) = 8 := by decide +kernel

/-- A nonzero singular vector has an eight-element stabilizer. -/
theorem singular_stabilizer_card (v : Vector) (hv : ∀ i, v i ≠ 1) :
    Nat.card (MulAction.stabilizer Actor v) = 8 := by
  rw [Nat.card_eq_fintype_card]
  exact singular_card_check v hv

end BinaryWreathPointStabilizer
