module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Groups
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.LastChiefFactor
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.OrthogonalSix
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Assembly

/-!
# Intrinsic parabolic geometry of Λ²(F₂⁵)

The four source exterior stabilizers are the actual natural flag parabolics,
with their two-cores, marked Levi quotients and solvable residuals identified.
The strict chain 0 < V₁ < V₇ < V has three irreducible actual factors.

The natural comparisons on V₃, V₄ and V/V₆ use the literal residual quotients;
V₃ uses the inverse-transpose SL₃ actor. The Pfaffian isometry identifies V₆
equivariantly with the split orthogonal module for the actual Ω⁺₆(2) subgroup.
The quotient V/V₆ is equivariantly isomorphic to R₆ = O₂(L₆T) under conjugation.
Every descended action agrees with the original exterior action on quotient
representatives. For the middle parabolics, quotients of Lᵢ use Lᵢ ∩ Rᵢ,
and the residual images fill (LᵢT)/Rᵢ; no containment Rᵢ ≤ Lᵢ is imposed.

Reference: Aschbacher–Smith, Lemma 12.5.2, printed p.817/PDF p.834.
-/
