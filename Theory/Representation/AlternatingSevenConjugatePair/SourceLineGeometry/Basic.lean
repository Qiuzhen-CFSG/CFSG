module

public import Theory.Representation.AlternatingSevenConjugatePair.Model
public import Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The source line and its cubic identities

The three disjoint swaps use the marking `{23,45,01}`. The source actors
are the embedded two-residuals of the cubic, duad and syntheme overgroups.
Three-cycles have zero cubic norm on every supplied conjugate pair: this
follows from the fixed-point-free calculation on its two actual summands.
No comparison with the constructed model is an input.

Source: Aschbacher–Smith, Lemma 14.4.11, printed p.1011/PDF p.1028.
-/

@[expose] public section

namespace Representation.AlternatingSevenConjugatePair.SourceLineGeometry

open BinaryOffender
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels

def a : S7 := Equiv.swap 2 3
def b : S7 := Equiv.swap 4 5
def c : S7 := Equiv.swap 0 1

/-- The elementary group actually used in the displacement inclusions. -/
def B8 : Subgroup S7 := Subgroup.closure ({a, b, c} : Set S7)

/-- The embedded residual, so that all actors live in the same symmetric group. -/
def residual (P : Subgroup S7) : Subgroup S7 := (pResidual 2 P).map P.subtype

def firstCubic : S7 := Equiv.swap 0 1 * Equiv.swap 1 6
def secondCubic : S7 := Equiv.swap 2 3 * Equiv.swap 3 4

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def line (s : V) : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {s}

def displacement (ρ : Representation (ZMod 2) S7 V) (t : S7) : Submodule (ZMod 2) V :=
  LinearMap.range (ρ t - LinearMap.id)

def movedLine (ρ : Representation (ZMod 2) S7 V) (s : V) (P : Subgroup S7) :
    Submodule (ZMod 2) V := subspaceCommutator ρ (line s) (residual P)

theorem orbit_eq_of_coset (ρ : Representation (ZMod 2) S7 V) (s : V)
    (K : Subgroup S7) (hs : ∀ t ∈ K, ρ t s = s) (p q : S7)
    (hpq : q⁻¹ * p ∈ K) : ρ p s = ρ q s := by
  have h := congrArg (ρ q) (hs _ hpq)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using h

variable [FiniteDimensional (ZMod 2) V]

/-- A three-cycle has no nonzero fixed vector on the whole conjugate pair. -/
theorem threeCycle_fixedPointFree (D : Pair V) (t : S7) (ht : t.IsThreeCycle)
    (v : V) (hv : D.representation t v = v) : v = 0 := by
  have he : t ∈ alternatingGroup (Fin 7) := ht.mem_alternatingGroup
  let x : alternatingGroup (Fin 7) := ⟨t, he⟩
  have hfix : v ∈ fixedSpace D.representation (Subgroup.zpowers t) :=
    (mem_fixedSpace_zpowers_iff _ _ _).mpr hv
  rw [D.fixedSpace_eq_sup _ (Subgroup.zpowers_le.mpr he)] at hfix
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hfix
  have hu0 : u = 0 := by
    have h := Model.threeCycle_fixedPointFree D.first.toRepresentation
      D.first_faithful D.first_dim x ht (⟨u, hu.1⟩ : D.first.toSubmodule)
      (Subtype.ext ((mem_fixedSpace_zpowers_iff D.representation t u).mp hu.2))
    exact congrArg Subtype.val h
  have hw0 : w = 0 := by
    have h := Model.threeCycle_fixedPointFree D.second.toRepresentation
      D.second_faithful D.second_dim x ht (⟨w, hw.1⟩ : D.second.toSubmodule)
      (Subtype.ext ((mem_fixedSpace_zpowers_iff D.representation t w).mp hw.2))
    exact congrArg Subtype.val h
  simp only [hu0, hw0, add_zero]

/-- The cubic relation used in the line calculations, valid on the given action. -/
theorem threeCycle_norm (D : Pair V) (t : S7) (ht : t.IsThreeCycle) (v : V) :
    v + D.representation t v + D.representation (t * t) v = 0 := by
  have ht3 : t * (t * t) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using
      (show t ^ 3 = 1 from ht.orderOf ▸ pow_orderOf_eq_one t)
  apply threeCycle_fixedPointFree D t ht
  simp only [map_add, ← Module.End.mul_apply, ← map_mul, ht3, map_one,
    Module.End.one_apply]
  abel

/-- A cubic norm at an orbit point, with its other two points reduced modulo
any subgroup fixing the marked vector. -/
theorem orbit_norm (D : Pair V) (s : V) (K : Subgroup S7)
    (hs : ∀ t ∈ K, D.representation t s = s) (t p q r : S7)
    (ht : t.IsThreeCycle) (hq : q⁻¹ * (t * p) ∈ K)
    (hr : r⁻¹ * (t * t * p) ∈ K) :
    D.representation p s + D.representation q s + D.representation r s = 0 := by
  have h := threeCycle_norm D t ht (D.representation p s)
  simp only [← Module.End.mul_apply, ← map_mul] at h
  rw [orbit_eq_of_coset D.representation s K hs _ q hq,
    orbit_eq_of_coset D.representation s K hs _ r hr] at h
  exact h

/-- The previously proved involution calculation, in the literal range convention. -/
theorem displacement_finrank (D : Pair V) (t : S7) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (displacement D.representation t) = 4 := by
  rw [displacement, ← fixedCodim_zpowers_eq_displacement_rank]
  exact D.involution_fixedCodim t ht

end Representation.AlternatingSevenConjugatePair.SourceLineGeometry
