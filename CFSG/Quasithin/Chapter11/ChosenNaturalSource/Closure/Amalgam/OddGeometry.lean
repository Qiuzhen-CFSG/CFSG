module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Lines

/-!
# Bounds for the original odd critical pair

The actual normalized endpoint simultaneously supplies both index-two bounds,
disjoint field lines, mutual normalization, and seed placement outside the
opposite core. The earlier corank and point-closure statements remain explicit.
The core-intersection commutator and nontrivial action on the opposite closure
are still required to construct OddPair and apply OddPair.axis; no theorem
in this module asserts that those two source obligations are discharged.
Source: Aschbacher--Smith 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterF.Section07
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- Elementary abelianness rules out radius one; odd parity therefore puts
both opposite edges in the range of F.7.11(5--6). -/
theorem three_le_distance (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (hab : IsMulCommutative E.W) (ho : Odd (distance E h hout)) :
    3 ≤ distance E h hout := by
  have htwo := one_lt_distance E h hout hab
  obtain ⟨k,hk⟩ := ho
  omega

/-- The bounds already established for the original odd critical pair.
The corank premise is precisely preceding 11.5.6(6). The literal 11.4.2
comparison at z and its Cartan orbit supply PointClosures; transitivity is
11.4.1(1).
The two missing action assertions of OddPair are deliberately absent. -/
theorem exists_odd_endpoint_bounds (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (hab : IsMulCommutative E.W) (ho : Odd (distance E h hout))
    (hc : RadicalCorank E)
    (hres : pointResidual L E.z = E.L₁) (hcomp : E.Kz = E.K)
    (horbit : ∀ u ∈ E.V₁, u ≠ 1 → ∃ x ∈ L ⊓ E.G₁, (MulAut.conj x) E.z = u)
    (ht : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, (MulAut.conj l) u = v) :
    ∃ g : generated E,
      V ≤ (KT E).map (MulAut.conj (g : G)).toMonoidHom ∧
      ¬ V ≤ ((KT E).map (MulAut.conj (g : G)).toMonoidHom).pCoreIn 2 ∧
      ⁅localClosure E, (localClosure E).map (MulAut.conj (g : G)).toMonoidHom⁆ ≤
        localClosure E ⊓ (localClosure E).map (MulAut.conj (g : G)).toMonoidHom ∧
      (U₁ E (g : G)).relIndex (localClosure E) ≤ 2 ∧
      (U₀ E (g : G)).relIndex ((localClosure E).map (MulAut.conj (g : G)).toMonoidHom) ≤ 2 ∧
      E.V₁ ⊓ E.V₁.map (MulAut.conj (g : G)).toMonoidHom = ⊥ := by
  have hp := pointClosures_of_comparison E hres hcomp horbit
  obtain ⟨i⟩ := CriticalPairs.NormalizedEndpoint.nonempty
    (D := sourceSetup E h hout) (hne := sourceV_ne_bot E h hout) ho
  have hb := three_le_distance E h hout hab ho
  exact ⟨(i : generated E), Endpoint.seed_le_actor i, Endpoint.seed_not_core i,
    Endpoint.mutual_commutator i hb, Endpoint.first_index i hab hb hc,
    Endpoint.second_index i hab hb hc, Endpoint.lines_disjoint i hab hb hp ht⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
