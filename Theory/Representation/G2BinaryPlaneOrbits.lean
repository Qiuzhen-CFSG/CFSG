module

public import Theory.Representation.G2BinaryPlaneOrbits.Sylow
public import Theory.Representation.G2BinaryPlaneOrbits.Stabilizer

/-!
# Recognizing binary G₂ planes with an order-96 stabilizing subgroup

An order-96 subgroup of G₂(2)' has odd index 63, so each of its Sylow
2-subgroups is an ambient Sylow subgroup. Conjugating one to the standard
positive-root Sylow simultaneously transports its invariant plane by the
natural linear action. Uniqueness of a plane invariant under this fixed Sylow
then places the original plane, and the standard stabilizer order forces the
image of the original subgroup to be the entire stabilizer.

The standard-Sylow uniqueness and the literal stabilizer order are proved in
the imported modules. The final theorem discharges both geometric inputs and
constructs the compatible coordinate maps from only the three stated small
plane and subgroup hypotheses.

Source: Aschbacher–Smith, printed p.1132 (PDF p.1149), C.1.30 and B.5.3–6.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.BinaryPlane
open Representation.BinaryOffender

/-- Every order-96 subgroup contains a conjugate of the fixed actual Sylow. -/
theorem exists_conjugate_contains_standardSylow (P : Subgroup Actor)
    (hP : Nat.card P = 96) :
    ∃ g : Actor, (standardSylow : Subgroup Actor) ≤ P.map (MulAut.conj g).toMonoidHom := by
  have hi : P.index = 63 := by
    have h := P.card_mul_index
    rw [hP, card_actor] at h
    omega
  let T : Sylow 2 P := Sylow.nonempty.some
  let Q : Subgroup Actor := (T : Subgroup P).map P.subtype
  have hQ : ¬ 2 ∣ Q.index := by
    rw [Subgroup.index_map_subtype, hi]
    exact Nat.prime_two.not_dvd_mul T.not_dvd_index (by decide)
  let S : Sylow 2 Actor := (T.2.map P.subtype).toSylow hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Actor S standardSylow
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  change Q.map (MulAut.conj g).toMonoidHom ≤ P.map (MulAut.conj g).toMonoidHom
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

/-- Sylow uniqueness and the literal stabilizer order suffice for the entire
coordinate conclusion. The unconditional theorem below supplies both premises. -/
theorem plane_geometry_of_standardSylow
    (uniquePlane : ∀ W : Submodule (ZMod 2) Coefficients,
      Nat.card W = 4 → (standardSylow : Subgroup Actor) ≤ subspaceStabilizer action W →
      W = standardPlane)
    (stabilizerCard : Nat.card (subspaceStabilizer action standardPlane) = 96)
    (W : Submodule (ZMod 2) Coefficients) (P : Subgroup Actor)
    (hW : Nat.card W = 4) (hP : Nat.card P = 96)
    (hPW : P ≤ subspaceStabilizer action W) :
    ∃ (f : Actor ≃* Actor) (e : Coefficients ≃ₗ[ZMod 2] Coefficients),
      (∀ a v, e (action a v) = action (f a) (e v)) ∧
      W.map e.toLinearMap = standardPlane ∧
      P.map f.toMonoidHom = subspaceStabilizer action standardPlane := by
  obtain ⟨g, hg⟩ := exists_conjugate_contains_standardSylow P hP
  let f : Actor ≃* Actor := MulAut.conj g
  let e := innerCoordinates g
  have he : ∀ a v, e (action a v) = action (f a) (e v) := innerCoordinates_equivariant g
  have hmap : P.map f.toMonoidHom ≤ subspaceStabilizer action (W.map e.toLinearMap) := by
    rw [← map_subspaceStabilizer_equivariant action action f e he W]
    exact Subgroup.map_mono hPW
  have hc : Nat.card (W.map e.toLinearMap) = 4 :=
    (Nat.card_congr (Submodule.equivMapOfInjective e.toLinearMap e.injective W).toEquiv).symm.trans hW
  have hw := uniquePlane (W.map e.toLinearMap) hc (hg.trans hmap)
  refine ⟨f, e, he, hw, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge (hw ▸ hmap)
  rw [Subgroup.card_map_of_injective f.injective, hP, stabilizerCard]

/-- Every binary plane stabilized by an order-96 subgroup has the prescribed
marking, through compatible inner actor and natural coefficient coordinates.
The original subgroup maps onto the entire literal marked-plane stabilizer. -/
theorem plane_geometry (W : Submodule (ZMod 2) Coefficients) (P : Subgroup Actor)
    (hW : Nat.card W = 4) (hP : Nat.card P = 96)
    (hPW : P ≤ subspaceStabilizer action W) :
    ∃ (f : Actor ≃* Actor) (e : Coefficients ≃ₗ[ZMod 2] Coefficients),
      (∀ a v, e (action a v) = action (f a) (e v)) ∧
      W.map e.toLinearMap = standardPlane ∧
      P.map f.toMonoidHom = subspaceStabilizer action standardPlane :=
  plane_geometry_of_standardSylow eq_standardPlane_of_standardSylow
    card_standardPlane_stabilizer W P hW hP hPW

end Atlas.G2.Natural.BinaryPlane
