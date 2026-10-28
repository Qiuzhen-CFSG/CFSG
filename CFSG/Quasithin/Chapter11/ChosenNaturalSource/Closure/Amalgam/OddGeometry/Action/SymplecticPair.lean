module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action.SymplecticCore

/-!
# The complete symplectic odd pair and its axis

The normalized endpoint supplies the literal indices, core escape, mutual
commutator and disjoint points. The symplectic hyperplane calculation supplies
the core-intersection commutator, while the relative-component kernel argument
supplies motion. Thus all OddPair fields hold for the same endpoint, and E.3.6
supplies its actual axis.

The preceding corank, point comparison, transitivity, local quotient and
relative-component inputs have producers qt-d-1222-cartan-exceptional-corank,
qt-d-1222-shadow-component-comparison, qt-d-1222-shadow-components,
qt-d-1222-natural-flag-cartan and qt-d-1222-natural-relative-components.
The final Symplectic.lean assembly constructs the point coordinates and
excludes even distance; no new action premise remains there. Its parent
qt-d-1222-natural-closure supplies abelianness, and
qt-d-1222-nonbinary-natural discharges preceding Chapter11 inputs.
Source: Aschbacher--Smith, 11.5.8, printed p.784.
-/

public noncomputable section
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
open Subgroup Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- All eight fields on the same normalized Sp₄ endpoint, with the two distinct
closures retained in the core-intersection argument. -/
theorem symplectic_oddPair (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (hab : IsMulCommutative E.W) (ho : Odd (distance E h hout))
    (m : Closure.Symplectic.MarkedFlag E)
    (p : Closure.Symplectic.Terminal.PointCoordinates E m)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hc : RadicalCorank E)
    (hres : pointResidual L E.z = E.L₁) (hcomp : E.Kz = E.K)
    (horbit : ∀ u ∈ E.V₁, u ≠ 1 → ∃ x ∈ L ⊓ E.G₁, (MulAut.conj x) E.z = u)
    (ht : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, (MulAut.conj l) u = v)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree)) :
    ∃ g : generated E, OddPair E (g : G) := by
  obtain ⟨g,hV,hescape,hmut,hfirst,hsecond,hlines⟩ :=
    exists_odd_endpoint_bounds E h hout hab ho hc hres hcomp horbit ht
  exact ⟨g, hV, hescape, hmut, hfirst, hsecond, hlines,
    (by rw [Action.symplectic_core_intersections_commute E m p hfixed h g
      hfirst hsecond hlines]; exact bot_le),
    Action.moves_closure_of_escape E g h hK hlt hlocal hV hescape⟩

/-- The constructed Sp₄ pair supplies the literal E.3.6 axis and nontrivial
motion on the same conjugate closure, without any action callback. -/
theorem symplectic_odd_axis (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (hab : IsMulCommutative E.W) (ho : Odd (distance E h hout))
    (m : Closure.Symplectic.MarkedFlag E)
    (p : Closure.Symplectic.Terminal.PointCoordinates E m)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hc : RadicalCorank E)
    (hres : pointResidual L E.z = E.L₁) (hcomp : E.Kz = E.K)
    (horbit : ∀ u ∈ E.V₁, u ≠ 1 → ∃ x ∈ L ⊓ E.G₁, (MulAut.conj x) E.z = u)
    (ht : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, (MulAut.conj l) u = v)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞)) :
    ∃ g : generated E, OddPair E (g : G) ∧
      U₀ E (g : G) ≤ centralizer (V : Set G) ∧
      (U₀ E (g : G)).relIndex ((localClosure E).map (MulAut.conj (g : G)).toMonoidHom) ≤ 2 ∧
      ⁅V,(localClosure E).map (MulAut.conj (g : G)).toMonoidHom⁆ ≠ ⊥ := by
  obtain ⟨g,hg⟩ := symplectic_oddPair E h hout hab ho m p hfixed hc hres hcomp horbit ht hK hlt hlocal
  exact ⟨g,hg,OddPair.axis E h hab hs hg⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
