module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action.Rigidity
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic

/-!
# Motion and point containment at the symplectic odd endpoint

The actual normalized endpoint moves Uᵍ. Centralizer rigidity and its second
index bound force motion already on U₀. Since U₀ lies in the original point
radical, the natural Sp₄ action puts the whole marked point in [V,U₀].
Mutual normalization and the two normal cores then put that point in both
U₁ and U₀. Every group is the original subgroup image with left conjugation.

The final endpoint adapter constructs the point coordinates from the original
marked flag and supplies motion and both index bounds itself. It retains only
preceding flag, fixed-space, corank, relative-component, quotient and parameter
facts. These are supplied by qt-d-1222-natural-flag-cartan,
qt-d-1222-shadow-components, qt-d-1222-cartan-exceptional-corank,
qt-d-1222-natural-relative-components and qt-d-1222-natural-weak-closure-source.
The remaining bound on [U₁,U₀] belongs to this same assembly owner,
qt-d-1222-natural-closure-amalgam; point containment alone does not prove it.
Source: Aschbacher--Smith, 11.5.8, printed p.784, using E.3.6, printed p.232.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
open Chapter12.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

open Closure.Symplectic Closure.Symplectic.Terminal

/-- Nontrivial radical action puts the original marked point in both literal
core intersections. The endpoint application below supplies the action premises. -/
theorem symplectic_point_le_intersections
    (m : MarkedFlag E) (p : PointCoordinates E m)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; globalS V = (E.input.field.degree : ℕ∞))
    (g : G)
    (hmut : ⁅localClosure E, (localClosure E).map (MulAut.conj g).toMonoidHom⁆ ≤
      localClosure E ⊓ (localClosure E).map (MulAut.conj g).toMonoidHom)
    (hi : (U₀ E g).relIndex ((localClosure E).map (MulAut.conj g).toMonoidHom) ≤ 2)
    (hn : ⁅V, (localClosure E).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    E.V₁ ≤ U₁ E g ⊓ U₀ E g := by
  have hmove := moves_core_intersection E hs g hi hn
  have hpoint := Even.Symplectic.point_le_commutator m p hfixed (U₀ E g)
    (inf_le_right.trans (OddGeometry.Action.core_le_radical E)) hmove
  have hQg : (localClosure E).map (MulAut.conj g).toMonoidHom ≤
      ((KT E).map (MulAut.conj g).toMonoidHom).pCoreIn 2 := by
    rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj g).injective]
    exact map_mono (localClosure_le_core E h hab)
  have hcUg : ⁅V, U₀ E g⁆ ≤ (localClosure E).map (MulAut.conj g).toMonoidHom :=
    ((commutator_mono (le_conjugateSpanBy _ _) inf_le_left).trans hmut).trans inf_le_right
  have hcQ : ⁅V, U₀ E g⁆ ≤ (KT E).pCoreIn 2 := by
    apply (commutator_mono le_rfl inf_le_right).trans
    apply le_normalizer_iff_commutator_le_right.mp
    exact (V_le_KT E).trans ((KT E).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact le_inf (le_inf (E.V₁_le.trans (le_conjugateSpanBy _ _))
    (hpoint.trans (hcUg.trans hQg))) (hpoint.trans (le_inf hcUg hcQ))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
open Chapter12.Section02 LocalGeometry
open Closure.Symplectic Closure.Symplectic.Terminal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- The original endpoint moves its literal core intersection, using the
already proved index bound and action-kernel argument. -/
theorem Endpoint.moves_core_intersection {h : LocalInputs E} {hout : ¬ E.K ≤ E.M}
    (i : Endpoint E h hout) (hab : IsMulCommutative E.W)
    (ho : Odd (distance E h hout)) (hc : RadicalCorank E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞)) :
    ⁅V, U₀ E ((i : generated E) : G)⁆ ≠ ⊥ :=
  Action.moves_core_intersection E hs _
    (i.second_index hab (three_le_distance E h hout hab ho) hc)
    (i.moves_closure E hK hlt hlocal)

/-- Both source core indices and endpoint motion give a nonzero commutator.
No geometric bound on that commutator is assumed. -/
theorem Endpoint.core_intersections_noncommuting {h : LocalInputs E} {hout : ¬ E.K ≤ E.M}
    (i : Endpoint E h hout) (hab : IsMulCommutative E.W)
    (ho : Odd (distance E h hout)) (hc : RadicalCorank E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞)) :
    ⁅U₁ E ((i : generated E) : G), U₀ E ((i : generated E) : G)⁆ ≠ ⊥ := by
  have hb := three_le_distance E h hout hab ho
  exact Action.core_intersections_noncommuting E hs _
    (i.first_index hab hb hc) (i.second_index hab hb hc) (i.moves_closure E hK hlt hlocal)

open Theory.SpecificGroups.SymplecticFour

/-- Original-geometry application: construct the radical coordinates and use
the actual endpoint, without any extra motion, index or coordinate callback. -/
theorem Endpoint.symplectic_point_le_intersections {h : LocalInputs E} {hout : ¬ E.K ≤ E.M}
    (i : Endpoint E h hout) (m : MarkedFlag E)
    (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap)
    (hplane : ∀ x : V, (x : G) ∈ E.V₂ ↔
      (markedProjection E m s x).toAdd ∈ plane E.input.field.Carrier)
    (hthree : ∀ x : V, (x : G) ∈ E.V₃ ↔
      (markedProjection E m s x).toAdd (.inr 0) = 0)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hab : IsMulCommutative E.W) (ho : Odd (distance E h hout)) (hc : RadicalCorank E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞)) :
    E.V₁ ≤ U₁ E ((i : generated E) : G) ⊓ U₀ E ((i : generated E) : G) := by
  have hb := three_le_distance E h hout hab ho
  exact Action.symplectic_point_le_intersections E m
    (Even.Symplectic.pointCoordinates m s hp hplane hthree) hfixed h hab hs _
    (i.mutual_commutator hb) (i.second_index hab hb hc) (i.moves_closure E hK hlt hlocal)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
