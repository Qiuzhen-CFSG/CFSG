module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action.Core
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action.Movement

/-!
# Constructing the SL₃ odd critical pair

The normalized endpoint already gives the two core-index bounds, disjoint
point lines and mutual normalization. The actual SL₃ point-core action
supplies the intersection commutator; the centralizer-kernel argument supplies
motion on the conjugate closure. These give all eight OddPair fields on the
same representative. The E.3.6 application retains that representative.

The earlier source corank, point residual, Cartan orbit, transitivity,
relative component and rank-one quotient remain explicit. Their producers
are qt-d-1222-cartan-exceptional-corank, qt-d-1222-shadow-component-comparison,
qt-d-1222-natural-relative-components, qt-d-1222-natural-flag-cartan and
qt-d-1222-shadow-components. The final source owner is
qt-d-1222-natural-closure-amalgam; its Linear extension discharges the parity
premise and consumes the constructed pair. The Sp₄ core-intersection step
remains with that same owner; the movement theorem applies to both cases.
Source: Aschbacher--Smith, 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
open Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- Every actual normalized odd endpoint moves the conjugate closure. -/
theorem Endpoint.moves_closure {h : LocalInputs E} {hout : ¬ E.K ≤ E.M}
    (i : Endpoint E h hout)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree)) :
    ⁅V,(localClosure E).map (MulAut.conj ((i : generated E) : G)).toMonoidHom⁆ ≠ ⊥ :=
  Action.moves_closure_of_escape E _ h hK hlt hlocal i.seed_le_actor i.seed_not_core

/-- All eight odd-pair fields on the same normalized endpoint. In the SL₃
branch the genuine point-core action discharges the last commutator bound. -/
theorem linear_oddPair (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (hab : IsMulCommutative E.W) (ho : Odd (distance E h hout))
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (f : InvariantFlag (.sl3 m)) (hm : Even.FlagMatch E f)
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
    Action.linear_core_intersection_commutator E m f hm h g,
    Action.moves_closure_of_escape E g h hK hlt hlocal hV hescape⟩

/-- The constructed SL₃ pair supplies the literal E.3.6 axis and nontrivial
motion on the same conjugate closure, without any action callback. -/
theorem linear_odd_axis (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (hab : IsMulCommutative E.W) (ho : Odd (distance E h hout))
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (f : InvariantFlag (.sl3 m)) (hm : Even.FlagMatch E f)
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
  obtain ⟨g,hg⟩ := linear_oddPair E h hout hab ho m f hm hc hres hcomp horbit ht hK hlt hlocal
  exact ⟨g,hg,OddPair.axis E h hab hs hg⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
