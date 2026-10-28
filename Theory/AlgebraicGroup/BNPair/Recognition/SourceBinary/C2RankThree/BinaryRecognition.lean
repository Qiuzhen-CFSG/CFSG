module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.BinaryNormality
public import Theory.GroupAction.SymplecticRankThree.BinaryHigman

/-!
# Full recognition of the original binary C₂ quotient

The exact (6A)(a) commutator clause and roots of order two give the kernel
on the six-point neighboring orbit. The remainder normalities follow from
index two. Higman's incidence argument constructs the fifteen-point polarity
design, and binary row-span reconstruction gives a faithful embedding of the
same quotient in Sp₄(F₂). No coordinates or model homomorphism are assumed.

The nontrivial pointwise block kernel supplies an actual transvection.
Transitivity and symplectic generation give surjectivity. The output
therefore retains full Sp₄(2), without assuming a group order, perfectness,
simplicity, or normal generation. The source local characteristic-two
hypothesis is used only for faithfulness of the action. The stronger
coordinate theorem records equivariance and literal orthogonality on the
same original second-parabolic cosets.

Source: Fong–Seitz I (1I), (3G), (6A)(a); II (7C), p.193;
Higman (1964), Theorem 2(i), pp.154–155, with the binary case proved directly.
-/

public noncomputable section
open Subgroup
open Theory.GroupAction.SymplecticRankThree
open Theory.SpecificGroups.SymplecticFour
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The same original quotient and cosets have full equivariant symplectic coordinates. -/
theorem binary_source_coordinates
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple 1}) :
      Set (Q.tits.standardParabolic {Q.simple 1})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple 1}))
    (hm : rotationOrder Q = 4)
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = 2)
    (hrow : ⁅simpleRoot Q split 1,kernelRoot Q split⁆ = ⊥) :
    ∃ D : PolarityDesign (Points Q 1) 2,
      (∀ x y, D.incident x y ↔ y = x ∨
        (MulAction.SwappedOrbital.graph (rightCosetPoint Q 1 1) (neighborPoint Q)
          (base_ne_neighbor Q) (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
          (neighbor_swap_base Q) (neighbor_swap_neighbor Q)).Adj x y) ∧
      D.block (rightCosetPoint Q 1 1) = insert (rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (neighborPoint Q)) ∧
      ∃ E : Theory.LinearAlgebra.BinaryPolarGeometry.Space D.incident ≃ₗ[ZMod 2] Vector (ZMod 2),
      ∃ e : (X ⧸ Q.D) ≃* Sp (ZMod 2),
        (∀ g x, E (Theory.LinearAlgebra.BinaryPolarGeometry.point D.incident (g • x)) =
          e g • E (Theory.LinearAlgebra.BinaryPolarGeometry.point D.incident x)) ∧
        (∀ x y, form (ZMod 2) (E (Theory.LinearAlgebra.BinaryPolarGeometry.point D.incident x))
          (E (Theory.LinearAlgebra.BinaryPolarGeometry.point D.incident y)) = 0 ↔ D.incident x y) := by
  let := faithful Q split 1 hc
  let := primitive Q 1
  let := Fintype.ofFinite (Points Q 1)
  exact binary_condition_i_recognition
    (rightCosetPoint Q 1 1) (neighborPoint Q) (oppositePoint Q)
    (base_ne_neighbor Q) (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
    (neighbor_swap_base Q) (neighbor_swap_neighbor Q)
    (opposite_orbit_eq_compl Q hm) (points_card Q split hm (hq 0) (hq 1) 1)
    (neighbor_orbit_card Q split hm (hq 0) (hq 1))
    (binary_kernel_lower_bound Q split hm hq hrow)

/-- The original binary C₂ quotient is the full concrete symplectic group. -/
theorem binary_symplectic_equiv
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple 1}) :
      Set (Q.tits.standardParabolic {Q.simple 1})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple 1}))
    (hm : rotationOrder Q = 4)
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = 2)
    (hrow : ⁅simpleRoot Q split 1,kernelRoot Q split⁆ = ⊥) :
    Nonempty ((X ⧸ Q.D) ≃* Sp (ZMod 2)) := by
  obtain ⟨_,_,_,_,e,_,_⟩ := binary_source_coordinates Q split hc hm hq hrow
  exact ⟨e⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
