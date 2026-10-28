module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Geometry
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The remaining local inputs in the pure-vector argument

These contracts retain the original coordinate summands and the embedded
two-core of the full point centralizer. They separate 12.1.4--5's ambient
Sylow argument from 12.1.6's component exclusion and G.2 application.
No contract asserts fusion, abelianness of the closure, or commutation of
intersecting conjugates.

Source: Aschbacher--Smith 12.1.4--6, printed pp.790--792.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The literal embedded O₂(C_G(w)). -/
def purePointCore (_B : DoubledBranch T L V n)
    (w : componentOrbit V (T : Subgroup G)) : Subgroup G :=
  (centralizer ({(w : G)} : Set G)).pCoreIn 2

/-- The conjugacy-invariant consequence of the marked Sylow assertion
12.1.5(1) needed by the core argument. The marked assertion itself must
still be proved for the original T₁, before transporting it to every point. -/
def PurePointSylows : Prop :=
  ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
    (B.coordinates w).toAdd.2 = 0 →
    ∃ P : Sylow 2 (centralizer ({(w : G)} : Set G)),
      (P : Subgroup _).map (centralizer ({(w : G)} : Set G)).subtype ≤
        normalizer (componentOrbit V (T : Subgroup G) : Set G) ⊓
          normalizer (B.dualSummand : Set G)

/-- Fixing either summand in the full module normalizer fixes all of W.
These are H.9 action-kernel facts, not ambient centralizer bounds. -/
structure SummandCentralizers : Prop where
  natural : normalizer (componentOrbit V (T : Subgroup G) : Set G) ⊓
    centralizer (B.naturalSummand : Set G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)
  dual : normalizer (componentOrbit V (T : Subgroup G) : Set G) ⊓
    centralizer (B.dualSummand : Set G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)

/-- The core containment and the natural-section centrality obtained in
12.1.6. The second clause is [V₁,Q_v]≤⟨v⟩, with relative core conventions. -/
structure PureCoreControl : Prop where
  orbit_le : ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
    (B.coordinates w).toAdd.2 = 0 →
    componentOrbit V (T : Subgroup G) ≤ B.purePointCore w
  commutator_le : ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
    (B.coordinates w).toAdd.2 = 0 →
    ⁅B.naturalSummand, B.purePointCore w⁆ ≤ zpowers (w : G)

theorem purePointCore_le_normalizers [Finite G] (hs : B.PurePointSylows)
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    B.purePointCore w ≤ normalizer (componentOrbit V (T : Subgroup G) : Set G) ⊓
      normalizer (B.dualSummand : Set G) := by
  obtain ⟨P, hP⟩ := hs w hw hp
  exact (pCoreIn_le_sylow _ P).trans hP

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
