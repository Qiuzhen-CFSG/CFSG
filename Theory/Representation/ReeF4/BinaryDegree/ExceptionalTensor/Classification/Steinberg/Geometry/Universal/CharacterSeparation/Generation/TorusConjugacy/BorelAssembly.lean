module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy.BorelReduction
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy
public import Theory.AlgebraicGroup.Solvable.MaximalTorusConjugacy

/-!
# Maximal-torus conjugacy from Borel geometry

The connected solvable carrier of a Borel satisfies the hypotheses of the
solvable maximal-torus conjugacy theorem. Combining this with geometric Borel
conjugacy discharges both inputs to `BorelReduction`: any two maximal tori
are conjugate, without an ambient connectedness assumption.

Source: GLS3, Theorem 1.4.3(b), via Theorem 1.6.2(b), and Borel,
*Linear Algebraic Groups*, Chapter III, Theorem 10.6(4).
-/

public section

namespace Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Variety k} [AlgebraicGroup G]

/-- Maximal tori inside a Borel are conjugate by a point of that Borel. -/
theorem borelCarrier_maximalTori_conjugate
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (T₁ T₂ : ClosedSubgroup B.carrierVariety)
    (hT₁ : IsMaximalTorus T₁) (hT₂ : IsMaximalTorus T₂) :
    ∃ b : Variety.Point B.carrierVariety, T₂ = T₁.conjugate b := by
  have hconn : Variety.IsConnected B.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
    let : ConnectedSpace {x : Variety.Point G // x ∈ (B : Set (Variety.Point G))} :=
      Subtype.connectedSpace hB.connected
    let : ConnectedSpace (Variety.Point B.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  exact maximalTori_conjugate_of_solvable_connected hB.solvable hconn hT₁ hT₂

/-- Geometric Borel conjugacy and solvable conjugacy prove GLS3 1.4.3(b). -/
theorem maximalTori_conjugate
    (T₁ T₂ : ClosedSubgroup G) (hT₁ : IsMaximalTorus T₁) (hT₂ : IsMaximalTorus T₂) :
    ∃ g : Variety.Point G, T₂ = T₁.conjugate g :=
  maximalTori_conjugate_of_borel_and_solvable_conjugacy
    (fun _ _ hB hC => BorelGeometricConjugacy.conjugacy hB hC)
    borelCarrier_maximalTori_conjugate T₁ T₂ hT₁ hT₂

end Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
