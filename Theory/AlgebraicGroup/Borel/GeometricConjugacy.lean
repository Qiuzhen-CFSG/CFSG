module

public import Theory.AlgebraicGroup.Bor1.BorelHomogeneousSpace
public import Theory.AlgebraicGroup.Borel.Conjugation.theorem_1_6_2_b
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel
public import Theory.AlgebraicGroup.Bor1.SolvableCompleteFixedPoint
public import Theory.AlgebraicGroup.Variety.MorphicActionPullback

/-!
# Geometric Borel conjugacy

The target is GLS3, Definition 1.6.1 and Theorem 1.6.2(b), including
disconnected ambient algebraic groups. Borel, *Linear Algebraic Groups*,
10.4 and 11.1 give the geometric proof: construct one complete Borel
homogeneous space, apply the solvable fixed-point theorem to each Borel,
and use maximality to turn fixed-point containment into conjugacy.

The complete model is the closed flag orbit of a Borel of maximal dimension.
Restricting its regular action to each Borel gives fixed points by the solvable
fixed-point theorem. The equivariant point equivalence transports these to the
actual Plücker homogeneous space, where Borel maximality gives conjugacy.
Thus `conjugacy` has no extra geometric premises or ambient connectedness
assumption. The arbitrary-proposition record `CompleteBorelHomogeneousSpace`
is not used.
Only the independent `IsBorelSubgroup.conjugate` lemma is used from the
legacy conjugation module, never its unresolved conjugacy theorem.
-/

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

open Bor1

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- A fixed point in the actual homogeneous space turns Borel containment
into equality with a conjugate. Ambient connectedness is unnecessary. -/
public theorem conjugate_of_homogeneousSpace_fixed {B S : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hS : IsBorelSubgroup S)
    (x : borelHomogeneousSpace B)
    (hfix : ∀ s : Variety.Point G, s ∈ S.toSubgroup → s • x = x) :
    ∃ g : Variety.Point G, S = B.conjugate g := by
  obtain ⟨g, hg⟩ := subgroup_le_conjugate_of_homogeneousSpace_fixed B S.toSubgroup x hfix
  have hBg := hB.conjugate g
  exact ⟨g, (hS.maximal (B.conjugate g) hBg.connected hBg.solvable hg).symm⟩

/-- Conversely, a conjugate fixes the coset represented by its conjugator. -/
public theorem homogeneousSpace_fixed_of_conjugate {B S : ClosedSubgroup G}
    (hconj : ∃ g : Variety.Point G, S = B.conjugate g) :
    ∃ x : borelHomogeneousSpace B,
      ∀ s : Variety.Point G, s ∈ S.toSubgroup → s • x = x := by
  obtain ⟨g, rfl⟩ := hconj
  refine ⟨borelHomogeneousSpace.projection B g, ?_⟩
  intro s hs
  apply Subtype.ext
  exact (projectivization_fixed_iff_mem_conjugate B g s).mpr hs

omit [IsAlgClosed k] in
/-- Two subgroups conjugate to the same subgroup are conjugate to one another.
This is useful when geometry constructs a complete quotient for one Borel
of maximal dimension rather than for the two Borels supplied by a caller. -/
public theorem conjugate_of_common_conjugate {B B₁ B₂ : ClosedSubgroup G}
    (h₁ : ∃ g : Variety.Point G, B₁ = B.conjugate g)
    (h₂ : ∃ g : Variety.Point G, B₂ = B.conjugate g) :
    ∃ g : Variety.Point G, B₂ = B₁.conjugate g := by
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [ClosedSubgroup.conjugate_conjugate]
  simp only [inv_mul_cancel_right]

/-- Transport from fixed points on one common Borel homogeneous space.
The theorem `conjugacy` below supplies these points using complete geometry. -/
public theorem conjugacy_of_common_homogeneousSpace_fixed
    {B B₁ B₂ : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hB₁ : IsBorelSubgroup B₁) (hB₂ : IsBorelSubgroup B₂)
    (h₁ : ∃ x : borelHomogeneousSpace B,
      ∀ s : Variety.Point G, s ∈ B₁.toSubgroup → s • x = x)
    (h₂ : ∃ x : borelHomogeneousSpace B,
      ∀ s : Variety.Point G, s ∈ B₂.toSubgroup → s • x = x) :
    ∃ g : Variety.Point G, B₂ = B₁.conjugate g := by
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  exact conjugate_of_common_conjugate
    (conjugate_of_homogeneousSpace_fixed hB hB₁ x₁ hx₁)
    (conjugate_of_homogeneousSpace_fixed hB hB₂ x₂ hx₂)

/-- Every Borel fixes a point on the homogeneous space of a Borel with a
complete geometric model. This is the fixed-point step of Borel §11.1. -/
public theorem CompleteModel.homogeneousSpace_fixed_of_isBorel
    {B S : ClosedSubgroup G} (M : CompleteModel B) (hS : IsBorelSubgroup S) :
    ∃ x : borelHomogeneousSpace B,
      ∀ s : Variety.Point G, s ∈ S.toSubgroup → s • x = x := by
  have hconnected : Variety.IsConnected S.carrierVariety := by
    let : ConnectedSpace {x : Variety.Point G // x ∈ (S : Set (Variety.Point G))} :=
      Subtype.connectedSpace hS.connected
    let : ConnectedSpace (Variety.Point S.carrierVariety) :=
      (Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed).connectedSpace_iff.mpr
        inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨x, hx⟩ :=
    (M.action.pullbackGroup S.inclusion).exists_fixedPoint_of_isConnected_isSolvable_isComplete
      hconnected hS.solvable M.complete M.nonempty
  refine ⟨M.pointEquiv x, ?_⟩
  intro s hs
  have hsrange : s ∈ Set.range S.inclusion.onPoints := by
    rw [S.range_inclusion]
    exact hs
  obtain ⟨t, rfl⟩ := hsrange
  rw [← M.equivariant]
  exact congrArg M.pointEquiv (hx t)

/-- Any two Borel subgroups of an algebraic group over an algebraically closed
field are conjugate. The ambient group may be disconnected.

This proves GLS3, Theorem 1.6.2(b), by the complete flag orbit and solvable
fixed-point argument of Borel, *Linear Algebraic Groups*, §§10.4 and 11.1. -/
public theorem conjugacy {B₁ B₂ : ClosedSubgroup G}
    (hB₁ : IsBorelSubgroup B₁) (hB₂ : IsBorelSubgroup B₂) :
    ∃ g : Variety.Point G, B₂ = B₁.conjugate g := by
  obtain ⟨B, hB, ⟨M⟩⟩ := exists_borel_completeModel B₁ hB₁
  exact conjugacy_of_common_homogeneousSpace_fixed hB hB₁ hB₂
    (M.homogeneousSpace_fixed_of_isBorel hB₁)
    (M.homogeneousSpace_fixed_of_isBorel hB₂)

end Theory.AlgebraicGroup.BorelGeometricConjugacy
