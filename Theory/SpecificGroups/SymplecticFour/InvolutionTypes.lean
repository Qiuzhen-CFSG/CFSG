module

public import Theory.SpecificGroups.SymplecticFour.Flag
public import Theory.Representation.FirstCohomologySymplecticFour.Generation

/-!
# Geometric involution types in symplectic four-space

The Suzuki types use the dimension of the moved space on the actual natural
module. Type a₂ is distinguished from c₂ by whether every vector is
orthogonal to its image. Root elements are separately defined by conjugacy
to the existing eight matrix root families; identifying the two root types
with those families requires a theorem, not a family label.

The parabolic predicate likewise refers to the actual point and plane
stabilizers. These definitions supply shared vocabulary for the involution
and fixed-group calculations in Aschbacher–Smith, *The Classification of
Quasithin Groups*, Definition E.2.6, printed p.218, and Lemma 16.1.4,
printed p.1171. They assert no classification or centralizer calculation.
-/

@[expose] public noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.InvolutionTypes
variable {F : Type*} [Field F]

/-- The commutator space [V,g] in the natural four-dimensional module. -/
def movedSpace (g : Sp F) : Submodule F (Vector F) :=
  LinearMap.range ((toLinear g).toLinearMap - LinearMap.id)

/-- Suzuki type b₁: an involution with one-dimensional moved space. -/
def IsB1 (g : Sp F) : Prop :=
  orderOf g = 2 ∧ Module.finrank F (movedSpace g) = 1

/-- Suzuki type a₂: rank two, with every vector orthogonal to its image. -/
def IsA2 (g : Sp F) : Prop :=
  orderOf g = 2 ∧ Module.finrank F (movedSpace g) = 2 ∧
    ∀ v : Vector F, form F v (g • v) = 0

/-- Suzuki type c₂: rank two, with a vector not orthogonal to its image. -/
def IsC2 (g : Sp F) : Prop :=
  orderOf g = 2 ∧ Module.finrank F (movedSpace g) = 2 ∧
    ∃ v : Vector F, form F v (g • v) ≠ 0

/-- A nonidentity element of a conjugate of one of the eight matrix root
groups. In characteristic two these are root involutions. -/
def IsRootElement (g : Sp F) : Prop :=
  ∃ (h : Sp F) (r : Fin 8) (t : F), t ≠ 0 ∧
    g = h * Representation.OneCohomology.SymplecticFour.rootElement r t * h⁻¹

/-- A conjugate of an actual point or maximal-isotropic-plane stabilizer. -/
def IsParabolic (P : Subgroup (Sp F)) : Prop :=
  ∃ h : Sp F,
    P = pointParabolic.map (MulAut.conj h).toMonoidHom ∨
    P = planeParabolic.map (MulAut.conj h).toMonoidHom

end Theory.SpecificGroups.SymplecticFour.InvolutionTypes
