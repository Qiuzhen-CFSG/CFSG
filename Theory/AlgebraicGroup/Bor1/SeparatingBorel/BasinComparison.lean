module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.AttractorComparison

/-!
# Attracting stabilizers are independent of the Borel model

Borel conjugacy aligns the stabilizers of two basepoints. Translating one
nonempty open basin and intersecting it with the other gives common actors
on the irreducible connected group. The corresponding actual affine curves
lie in a closed diagonal Borel orbit, so their endpoint stabilizers agree.

This is the canonical comparison for B(c) in Borel, *Linear Algebraic Groups*,
IV, 13.8 and 13.11. The inputs are literal morphic actions and affine curves;
the source producer supplies the open basins.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open Variety.Geometric
open Variety.Geometric.ProjectivePolynomialCurve
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {X Y : Variety.Geometric k}

theorem orbit_preimage_isOpen (A : MorphicAction G X) (x : Point X)
    (U : X.toScheme.Opens) :
    IsOpen {g : Variety.Point G | (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈ U} := by
  apply isClosed_compl_iff.mp
  apply Variety.isClosed_iff_isZariskiClosed.mpr
  have hc := Variety.Geometric.Morphism.preimage_isZariskiClosed_ofAffine
    (A.orbitMorphismAt x) U.isOpen.isClosed_compl
  convert hc using 1
  ext g
  change (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∉ U ↔
    (A.orbitMorphismAt x ((affinePointEquiv G).symm g)).1 (IsLocalRing.closedPoint k) ∉ U
  rw [A.orbitMorphismAt_apply]

theorem attracting_stabilizers_eq
    (hG : Variety.IsConnected G)
    (A : MorphicAction G X) (C : MorphicAction G Y)
    (x p : Point X) (y q : Point Y)
    (hBx : IsBorelSubgroup (A.pointStabilizer x))
    (hBy : IsBorelSubgroup (C.pointStabilizer y))
    (param : kˣ → Variety.Point G)
    (U V : Set (Variety.Point G)) (hU : IsOpen U) (hV : IsOpen V)
    (hneU : U.Nonempty) (hneV : V.Nonempty)
    (hf : ∀ g ∈ U, ∃ f : Variety.Geometric.Morphism (polynomialAffineLine k) X,
      f (affinePoint 0) = p ∧ ∀ (a : k) (ha : a ≠ 0),
        f (affinePoint a) = A.toMulAction.smul (param (Units.mk0 a ha)) (A.toMulAction.smul g x))
    (hg : ∀ g ∈ V, ∃ f : Variety.Geometric.Morphism (polynomialAffineLine k) Y,
      f (affinePoint 0) = q ∧ ∀ (a : k) (ha : a ≠ 0),
        f (affinePoint a) = C.toMulAction.smul (param (Units.mk0 a ha)) (C.toMulAction.smul g y)) :
    A.pointStabilizer p = C.pointStabilizer q := by
  obtain ⟨s, hs⟩ := BorelGeometricConjugacy.conjugacy hBx hBy
  let U' := (fun g : Variety.Point G => g * s) ⁻¹' U
  have hU' : IsOpen U' := hU.preimage (continuous_mul_const s)
  have hneU' : U'.Nonempty := by
    obtain ⟨g, hg⟩ := hneU
    exact ⟨g * s⁻¹, by simpa only [U', Set.mem_preimage, inv_mul_cancel_right] using hg⟩
  obtain ⟨g, _, hgu, hgv⟩ := (connectedAlgebraicGroup_irreducible G hG).2 U' V hU' hV
    (by simpa only [Set.univ_inter] using hneU')
    (by simpa only [Set.univ_inter] using hneV)
  obtain ⟨f, hf0, hfa⟩ := hf (g * s) hgu
  obtain ⟨j, hj0, hja⟩ := hg g hgv
  have hbase : ∀ b : Variety.Point G,
      A.toMulAction.smul b (A.toMulAction.smul s x) = A.toMulAction.smul s x ↔
        b ∈ (C.pointStabilizer y).toSubgroup := by
    intro b
    rw [hs]
    change A.toMulAction.smul b (A.toMulAction.smul s x) = A.toMulAction.smul s x ↔
      b ∈ (A.pointStabilizer x).conjugate s
    rw [ClosedSubgroup.mem_conjugate_iff]
    rw [A.mem_pointStabilizer]
    let := A.toMulAction
    change b • (s • x) = s • x ↔ (s⁻¹ * b * s) • x = x
    constructor
    · intro h
      simpa only [mul_smul, inv_smul_smul] using congrArg (fun z : Point X => s⁻¹ • z) h
    · intro h
      simpa only [mul_smul, smul_inv_smul] using congrArg (fun z : Point X => s • z) h
  have he := endpoint_stabilizers_eq_of_common_borel_curves hG
    (C.pointStabilizer y) hBy A C (A.toMulAction.smul s x) y hbase
    (fun b => (C.mem_pointStabilizer y b).symm) f j (by
      intro a ha
      refine ⟨param (Units.mk0 a ha) * g, ?_, ?_⟩
      · rw [hfa a ha]
        let := A.toMulAction
        change (param (Units.mk0 a ha) * g) • (s • x) = param (Units.mk0 a ha) • ((g * s) • x)
        simp only [mul_smul]
      · rw [hja a ha]
        let := C.toMulAction
        exact mul_smul _ _ _)
  simpa only [hf0, hj0] using he
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
