module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear.PointCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The core intersections of the SL₃ odd pair

The two-core of KT lies in the original edge radical R₁. The actual SL₃
point-core calculation therefore bounds [V,O₂(KT)] by V₁. Normality of the
core and invariance of the point propagate that bound to U=⟨V^(KT)⟩.
Applying the bound in both conjugate orientations places [U₁,U₀] inside
V₁ ∩ V₁ᵍ, as required by E.3.6 on the original odd pair.

The generic propagation lemmas retain their displacement premise. The SL₃
application discharges it from the literal marked natural action; no claim
about the different V₃-closure is used for the Sp₄ case.
Source: Aschbacher--Smith, 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

theorem core_le_radical : (KT E).pCoreIn 2 ≤ E.R₁ := by
  have hQT : (KT E).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ KT E from le_sup_right)] using
      pCoreIn_le_sylow (KT E) (T.subtype (show (T : Subgroup G) ≤ KT E from le_sup_right))
  have hLH : E.L₁ ⊔ (T : Subgroup G) ≤ KT E :=
    sup_le ((le_conjugateSpanBy E.L₁ E.G₁).trans le_sup_left) le_sup_right
  exact (le_inf (hQT.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hLH)

/-- Propagate the seed displacement to its literal KT-closure. -/
theorem closure_core_bound (h : LocalInputs E)
    (hseed : ⁅V,(KT E).pCoreIn 2⁆ ≤ E.V₁) :
    ⁅localClosure E,(KT E).pCoreIn 2⁆ ≤ E.V₁ := by
  have hHZ : KT E ≤ normalizer (E.V₁ : Set G) := KT_le_G₁ E h
  have hHQ : KT E ≤ normalizer ((KT E).pCoreIn 2 : Set G) :=
    (KT E).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hspan : localClosure E ≤ commutatorPreimage (KT E) ((KT E).pCoreIn 2) E.V₁ :=
    conjugateSpanBy_le (le_commutatorPreimage (V_le_KT E) hseed)
      (commutatorPreimage_normalized _ _ _ _ hHZ (KT E).le_normalizer hHQ hHZ)
  exact (commutator_mono hspan le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hHZ)

/-- The two core intersections use opposite sides of the same equivariant bound. -/
theorem core_intersection_commutator (g : G)
    (hc : ⁅localClosure E,(KT E).pCoreIn 2⁆ ≤ E.V₁) :
    ⁅U₁ E g,U₀ E g⁆ ≤ E.V₁ ⊓ E.V₁.map (MulAut.conj g).toMonoidHom := by
  apply le_inf
  · exact (commutator_mono (show U₁ E g ≤ localClosure E from inf_le_left)
      (show U₀ E g ≤ (KT E).pCoreIn 2 from inf_le_right)).trans hc
  · have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hc
    rw [map_commutator, ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (MulAut.conj g).injective] at hm
    rw [commutator_comm]
    exact (commutator_mono (show U₀ E g ≤ (localClosure E).map (MulAut.conj g).toMonoidHom
      from inf_le_left) (show U₁ E g ≤ ((KT E).map (MulAut.conj g).toMonoidHom).pCoreIn 2
      from inf_le_right)).trans hm

open CFSG.Quasithin.ChapterB.QuasisimpleSource
open LocalGeometry

theorem linear_closure_core_bound
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (f : InvariantFlag (.sl3 m)) (hm : Even.FlagMatch E f) (h : LocalInputs E) :
    ⁅localClosure E,(KT E).pCoreIn 2⁆ ≤ E.V₁ :=
  closure_core_bound E h ((commutator_mono le_rfl (core_le_radical E)).trans
    (Even.Linear.point_core_bound m f hm))

theorem linear_core_intersection_commutator
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (f : InvariantFlag (.sl3 m)) (hm : Even.FlagMatch E f) (h : LocalInputs E) (g : G) :
    ⁅U₁ E g,U₀ E g⁆ ≤ E.V₁ ⊓ E.V₁.map (MulAut.conj g).toMonoidHom :=
  core_intersection_commutator E g (linear_closure_core_bound E m f hm h)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
