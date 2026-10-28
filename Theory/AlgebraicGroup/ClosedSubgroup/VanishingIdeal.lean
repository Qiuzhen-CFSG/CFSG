module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.CoordinateRing.Point

universe u

/-!
The vanishing ideal of a closed subgroup in the ambient polynomial-function
ring.  This is the finite-generation input for the finite-dimensional
Chevalley representation used in Proposition 1.1.2(b).
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- Polynomial functions on `G` vanishing on the closed subgroup `H`. -/
@[expose]
public def ClosedSubgroup.vanishingIdeal {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) : Ideal G.PolynomialFunction :=
  RingHom.ker H.restrictionRingHom

/-- Membership in the vanishing ideal is pointwise vanishing on the induced
closed-subgroup variety. -/
public lemma ClosedSubgroup.mem_vanishingIdeal_iff_carrier
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (f : G.PolynomialFunction) :
    f ∈ H.vanishingIdeal ↔
      ∀ h : Variety.Point H.carrierVariety,
        f (H.inclusion.onPoints h) = 0 := by
  rw [ClosedSubgroup.vanishingIdeal, RingHom.mem_ker]
  constructor
  · intro hf h
    have hvalue := congrArg
      (fun a : H.carrierVariety.PolynomialFunction => a h) hf
    rw [H.restrictionRingHom_apply] at hvalue
    exact hvalue
  · intro hf
    apply Variety.PolynomialFunction.ext
    intro h
    rw [H.restrictionRingHom_apply]
    exact hf h

/-- Membership in the vanishing ideal is pointwise vanishing on the ambient
points belonging to the underlying subgroup. -/
public lemma ClosedSubgroup.mem_vanishingIdeal_iff
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (f : G.PolynomialFunction) :
    f ∈ H.vanishingIdeal ↔
      ∀ x : Variety.Point G, x ∈ H.toSubgroup → f x = 0 := by
  rw [H.mem_vanishingIdeal_iff_carrier]
  constructor
  · intro hf x hx
    have hx' : x ∈ (H.toSubgroup : Set (Variety.Point G)) := hx
    rw [← H.range_inclusion] at hx'
    obtain ⟨h, rfl⟩ := hx'
    exact hf h
  · intro hf h
    apply hf
    change H.inclusion.onPoints h ∈
      (H.toSubgroup : Set (Variety.Point G))
    rw [← H.range_inclusion]
    exact ⟨h, rfl⟩

/-- A closed subgroup is the common zero locus of its polynomial-function
vanishing ideal. -/
public lemma ClosedSubgroup.mem_iff_forall_vanishingIdeal
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (x : Variety.Point G) :
    x ∈ H.toSubgroup ↔ ∀ f ∈ H.vanishingIdeal, f x = 0 := by
  constructor
  · intro hx f hf
    exact (H.mem_vanishingIdeal_iff f).mp hf x hx
  · intro hx
    rcases H.isZariskiClosed with ⟨equations, hequations⟩
    change x ∈ (H.toSubgroup : Set (Variety.Point G))
    rw [hequations]
    intro p hp
    let f := Variety.PolynomialFunction.ofPolynomial G p
    have hf : f ∈ H.vanishingIdeal := by
      rw [H.mem_vanishingIdeal_iff]
      intro y hy
      have hy' : y ∈ (H.toSubgroup : Set (Variety.Point G)) := hy
      rw [hequations] at hy'
      exact hy' p hp
    exact hx f hf

/-- The vanishing ideal of a closed subgroup is finitely generated. -/
public lemma ClosedSubgroup.vanishingIdeal_fg
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.vanishingIdeal.FG := by
  let : Algebra.FiniteType k G.PolynomialFunction :=
    polynomialFunction_finiteType G
  let : IsNoetherianRing G.PolynomialFunction :=
    Algebra.FiniteType.isNoetherianRing k _
  exact Ideal.fg_of_isNoetherianRing _

end

end Theory.AlgebraicGroup

