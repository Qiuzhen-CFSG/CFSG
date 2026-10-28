module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.QuietRecognition

/-!
# Preparing the point orbit from the original local moved subgroup

The half-Sylow join normalizes [V_T,L]. Its uniqueness bounds the
normalizer of this nonzero two-group, so containment of [V_T,L] in the
point orbit already controls the orbit centralizer. At cubic component
order the established Thompson equality completes preparation.

An irreducible cover of [V_T,L] supplies that containment: the constrained
context kills its fixed kernel, and the nonzero point-Sylow fixed space
generates the entire local moved subgroup. No equality V_T=V_M is used.
The Source consumer uses this weaker preparation premise. Constructing
such local covers in the remaining cases is still owned by
qt-d-10-nona5-point-constrained.

Source: Aschbacher--Smith 10.2.6(1) and10.2.9, pp.748--751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The half-Sylow join normalizes the original local moved subgroup. -/
theorem Context.halfJoin_normalizes_local_moved (c : Context D t v I) :
    halfJoin T L ≤ normalizer (↑(⁅D.moduleSubgroup,L⁆ : Subgroup G) : Set G) := by
  have hN : halfJoin T L ≤ normalizer (D.moduleSubgroup : Set G) :=
    sup_le D.orbit_normalizes_module (inf_le_left.trans D.sylow_normalizes_module)
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hN hx),
    mem_normalizer_iff_map_conj_eq.mp ((halfJoin_le_stabilizer D
      (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem))).trans inf_le_right hx)]

/-- Half-Sylow uniqueness controls the local moved normalizer, even when
its M-orbit is larger. -/
theorem Context.local_moved_normalizer_le (c : Context D t v I) :
    normalizer (↑(⁅D.moduleSubgroup,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal := by
  have hW : ⁅D.moduleSubgroup,L⁆ ≤ D.moduleSubgroup :=
    le_normalizer_iff_commutator_le_left.mp
      ((le_componentOrbit L T).trans D.orbit_normalizes_module)
  exact normalizer_le_of_unique_maximalTwoLocal c.escaping.half_unique
    (D.module_elementary.isPGroup.to_le hW) (Selection.ModuleChoice.local_moved_ne_bot D)
    c.halfJoin_normalizes_local_moved

/-- The constrained orbit need only contain the local moved subgroup to
control its ambient centralizer. -/
theorem Context.centralizer_le_of_local_moved_le (c : Context D t v I)
    (h : ⁅D.moduleSubgroup,L⁆ ≤ orbitModule D v I) :
    centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal :=
  (centralizer_le h).trans
    ((Subgroup.centralizer_le_normalizer _).trans c.local_moved_normalizer_le)

/-- At cubic component order, the smaller local span suffices for complete
preparation of the literal reduced orbit. -/
theorem Context.prepared_of_local_moved_le_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (h : ⁅D.moduleSubgroup,L⁆ ≤ orbitModule D v I) : Prepared D v I :=
  c.prepared_of_centralizer_of_three hd (c.centralizer_le_of_local_moved_le h)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) L V} [IsIrreducible ρ]

/-- An irreducible cover of the original local moved subgroup generates
that subgroup inside VI. Its fixed kernel is discharged by the context. -/
theorem Context.local_moved_le_of_irreducible_cover (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆
      (⁅D.moduleSubgroup,L⁆ ⊓ centralizer (L : Set G)) ρ) :
    ⁅D.moduleSubgroup,L⁆ ≤ orbitModule D v I := by
  let W := ⁅D.moduleSubgroup,L⁆
  have hWF : W ≤ ⁅D.fullModule,L⁆ := commutator_mono (le_componentOrbit _ _) le_rfl
  have hz : W ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hWF).trans_eq c.moved_fixed_eq_bot)
  have s' : BinaryConjugationSection L W ⊥ ρ := hz ▸ s
  let P := pointSylow T v
  have hPH : P ≤ halfJoin T L :=
    (le_inf inf_le_left c.escaping.sylow_normalizes).trans le_sup_right
  have hPW : P ≤ normalizer (W : Set G) := hPH.trans c.halfJoin_normalizes_local_moved
  have hWV : W ≤ D.moduleSubgroup := le_normalizer_iff_commutator_le_left.mp
    ((le_componentOrbit L T).trans D.orbit_normalizes_module)
  have hfix := inf_centralizer_ne_bot_of_pGroups P W (T.isPGroup'.to_le inf_le_left)
    (D.module_elementary.isPGroup.to_le hWV) hPW
    (Selection.ModuleChoice.local_moved_ne_bot D)
  let A := conjugateSpanBy (W ⊓ centralizer (P : Set G)) L
  have hA : A = W := by
    rcases s'.eq_kernel_or_section A bot_le
      (conjugateSpanBy_le inf_le_left s'.normalized)
      (le_normalizer_conjugateSpanBy _ _) with hb | ht
    · exact (hfix (bot_unique ((le_conjugateSpanBy _ _).trans_eq hb))).elim
    · exact ht
  change W ≤ orbitModule D v I
  rw [←hA]
  exact conjugateSpanBy_mono (inf_le_inf_right _ hWF) c.escaping.strict.le

/-- A local irreducible cover and cubic component order prepare the actual
orbit without identifying the local moved subgroup with the full one. -/
theorem Context.prepared_of_local_irreducible_cover (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (s : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆
      (⁅D.moduleSubgroup,L⁆ ⊓ centralizer (L : Set G)) ρ) : Prepared D v I :=
  c.prepared_of_local_moved_le_of_three hd (c.local_moved_le_of_irreducible_cover s)

/-- Apply local preparation to the original quotient action and its complete
FF classification. Local cover recognition remains with this source owner. -/
theorem Context.actionFacts_of_local_irreducible_cover (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (s : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆
      (⁅D.moduleSubgroup,L⁆ ⊓ centralizer (L : Set G)) ρ) : ActionFacts c :=
  c.actionFacts (c.prepared_of_local_irreducible_cover hd s)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
