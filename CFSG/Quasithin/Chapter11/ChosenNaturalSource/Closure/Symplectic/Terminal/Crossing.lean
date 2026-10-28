module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Normalizer

/-!
# Escaping conjugates and the literal intersection plane

Noncentrality of V on the span of V₃ gives a G₁-conjugate of V that moves
V₃. Both seeds are normal in W_H, so their commutator is contained in their
intersection. The natural-action centralizer and displacement bounds then
identify that intersection with the original V₂. These statements retain
the original subgroups, rather than just their isomorphism types.

Source: Aschbacher--Smith 11.5.7, printed p.783, noncommuting terminal branch.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Noncommutation with U produces an actual escaping G₁-conjugate of V. -/
theorem exists_conjugate_moving_threeSpace (hc : ⁅V,E.U⁆ ≠ ⊥) :
    ∃ g ∈ E.G₁,
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (E.V₃ : Set G) := by
  by_contra! hn
  have hw : E.W ≤ centralizer (E.V₃ : Set G) := by
    apply (closure_le _).mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact hn g hg (mem_map_of_mem (MulAut.conj g).toMonoidHom hv)
  have hwu : E.W ≤ centralizer (E.U : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes E.W E.V₃ E.G₁
      (le_normalizer_conjugateSpanBy V E.G₁) hw
  exact hc (commutator_eq_bot_iff_le_centralizer.mpr
    ((le_conjugateSpanBy V E.G₁).trans hwu))

/-- Normality of the closure transports normalization of its original seed
to each of its G₁-conjugates. -/
theorem closure_normalizes_conjugate (hn : E.W ≤ normalizer (V : Set G))
    {g : G} (hg : g ∈ E.G₁) :
    E.W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hw : E.W.map (MulAut.conj g).toMonoidHom = E.W :=
    mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy V E.G₁) hg)
  exact hw.symm.le.trans ((map_mono hn).trans (V.le_normalizer_map _))

/-- Both normal seeds lie in their common closure. -/
theorem commutator_le_intersection (hn : E.W ≤ normalizer (V : Set G))
    {g : G} (hg : g ∈ E.G₁) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  have ha : V.map (MulAut.conj g).toMonoidHom ≤ E.W := by
    rintro _ ⟨v,hv,rfl⟩
    exact subset_closure ⟨g,hg,v,hv,rfl⟩
  exact le_inf (le_normalizer_iff_commutator_le_left.mp (ha.trans hn))
    (le_normalizer_iff_commutator_le_right.mp
      ((le_conjugateSpanBy V E.G₁).trans (closure_normalizes_conjugate E hn hg)))

/-- The source centralizer/displacement sandwich identifies the actual plane,
the commutator, and the full intersection, not merely their dimensions. -/
theorem intersection_eq_plane (hn : E.W ≤ normalizer (V : Set G))
    {g : G} (hg : g ∈ E.G₁)
    (hfixed : V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ≤ E.V₂)
    (hmoved : E.V₂ ≤ ⁅V,V.map (MulAut.conj g).toMonoidHom⁆) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = E.V₂ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = E.V₂ := by
  let := D.elementary
  let : IsMulCommutative (V.map (MulAut.conj g).toMonoidHom) :=
    inferInstance
  have hi : V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
      V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) :=
    inf_le_inf_left V (V.map (MulAut.conj g).toMonoidHom).le_centralizer
  have hc := commutator_le_intersection E hn hg
  exact ⟨le_antisymm (hi.trans hfixed) (hmoved.trans hc),
    le_antisymm (hc.trans (hi.trans hfixed)) hmoved⟩

/-- The initial core conclusion supplies normalization of W_H's seed, with
the original Sylow subgroup and its given action. -/
theorem closure_normalizes_seed (m : MarkedFlag E)
    (hcore : E.W ≤ E.G₁.pCoreIn 2) : E.W ≤ normalizer (V : Set G) := by
  have ht : E.G₁.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le m.sylow_le_point_normalizer] using
      pCoreIn_le_sylow E.G₁ (T.subtype m.sylow_le_point_normalizer)
  exact hcore.trans (ht.trans E.input.sylow_normalizes)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
