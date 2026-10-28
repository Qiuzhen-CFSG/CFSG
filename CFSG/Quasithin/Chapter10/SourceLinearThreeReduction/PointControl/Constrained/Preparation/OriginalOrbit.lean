module
public import Theory.GroupTheory.ReducedNormal.OrbitMinimality
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.FourNatural

/-!
# Original orbit preparation without a moved-cover marking

Joining an L-invariant local moved subgroup with its opposite conjugate
makes it invariant under the original Sylow group. Homogeneous orbit
minimality then gives the entire local module or a central subgroup.
Crossed centralization recovers the original local moved factor in the
first case; its proved zero fixed kernel excludes the second.

Apply this to the L-span of the half-Sylow fixed subgroup. The p-group
fixed-point theorem makes that subgroup nonzero, so its span is [V_T,L].
The point Sylow lies in the half-Sylow, placing this same local factor in
the literal VI. Its centralizer therefore lies in M. At cubic component
order the existing Thompson equality completes preparation and supplies
the actual FF action. V_T, V_M and VI remain distinct throughout.

Source: Aschbacher--Smith D.3.6 and10.2.9, printed pp.196,751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Half-Sylow-invariant subgroups of the local moved factor are full or central. -/
theorem Context.local_moved_minimal (c : Context D t v I)
    (A : Subgroup G) (hA : A ≤ ⁅D.moduleSubgroup,L⁆)
    (hLA : L ≤ normalizer (A : Set G))
    (hBA : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G)) :
    A = ⁅D.moduleSubgroup,L⁆ ∨ A ≤ centralizer (L : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem)
  have hi := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  let f := (MulAut.conj t).toMonoidHom
  let U := A ⊔ A.map f
  have hsplit : componentOrbit A T = U :=
    componentOrbit_eq_sup_of_index_two A T (normalizer (L : Set G)) hi hBA
      c.escaping.t_mem c.escaping.t_not_normalizes
  have hpair : localOrbit T L = L ⊔ L.map f :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G)) hi inf_le_right
      c.escaping.t_mem c.escaping.t_not_normalizes
  have hAW : A ≤ ⁅D.fullModule,L⁆ :=
    hA.trans (commutator_mono (le_componentOrbit _ _) le_rfl)
  have hAC : A ≤ centralizer (L.map f : Set G) := hAW.trans c.moved_centralizes_opposite
  have hAtC : A.map f ≤ centralizer (L : Set G) :=
    (map_mono hAW).trans c.escaping.crossed
  have hLtAt : L.map f ≤ normalizer (A.map f : Set G) := by
    rw [←map_equiv_normalizer_eq A (MulAut.conj t)]
    exact map_mono hLA
  have hLU : L ≤ normalizer (U : Set G) :=
    (le_inf hLA ((le_centralizer_iff.mp hAtC).trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hLtU : L.map f ≤ normalizer (U : Set G) :=
    (le_inf ((le_centralizer_iff.mp hAC).trans (Subgroup.centralizer_le_normalizer _)) hLtAt).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hOU : localOrbit T L ≤ normalizer (U : Set G) := by
    rw [hpair]
    exact sup_le hLU hLtU
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    hsplit ▸ le_normalizer_componentOrbit A T
  have hAV : A ≤ D.moduleSubgroup := hA.trans
    (le_normalizer_iff_commutator_le_left.mp
      ((le_componentOrbit L T).trans D.orbit_normalizes_module))
  have hUV : U ≤ D.moduleSubgroup := sup_le hAV (by
    have hm := map_mono (f := f) hAV
    exact hm.trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (D.sylow_normalizes_module c.escaping.t_mem)))
  rcases ReducedNormal.subspaceImage_orbit_eq_or_le_centralizer (localJoin T L)
      (localOrbit T L) (T : Subgroup G) le_sup_left le_sup_right
      D.homogeneous U hUV hOU hTU with he | hc
  · left
    apply le_antisymm hA
    have hAL : A ≤ normalizer (L : Set G) :=
      hAV.trans (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
    have hcomm := commutator_eq_of_centralizing_sup
      (show A.map f ⊔ A = D.moduleSubgroup by rw [sup_comm]; exact he)
      hAtC hAL
    rw [commutator_comm,←hcomm,commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hLA
  · exact Or.inr (le_sup_left.trans (hc.trans (centralizer_le (le_componentOrbit L T))))

/-- Half-Sylow fixed vectors generate the local moved subgroup under L. -/
theorem Context.local_moved_eq_half_fixed_span (c : Context D t v I) :
    conjugateSpanBy (⁅D.moduleSubgroup,L⁆ ⊓
      centralizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G)) L =
        ⁅D.moduleSubgroup,L⁆ := by
  let W := ⁅D.moduleSubgroup,L⁆
  let B := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let F := W ⊓ centralizer (B : Set G)
  let A := conjugateSpanBy F L
  have hWF : W ≤ ⁅D.fullModule,L⁆ := commutator_mono (le_componentOrbit _ _) le_rfl
  have hz : W ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hWF).trans_eq c.moved_fixed_eq_bot)
  have hBW : B ≤ normalizer (W : Set G) :=
    (show B ≤ halfJoin T L from le_sup_right).trans c.halfJoin_normalizes_local_moved
  have hLW : L ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  have hBF : B ≤ normalizer (F : Set G) :=
    (le_inf hBW (B.le_normalizer.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf
  have hBA : B ≤ normalizer (A : Set G) :=
    normalizes_conjugateSpanBy F L B hBF inf_le_right
  have hAW : A ≤ W := conjugateSpanBy_le inf_le_left hLW
  have hWV : W ≤ D.moduleSubgroup := le_normalizer_iff_commutator_le_left.mp
    ((le_componentOrbit L T).trans D.orbit_normalizes_module)
  have hfix : F ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups B W
    (T.isPGroup'.to_le inf_le_left) (D.module_elementary.isPGroup.to_le hWV)
    hBW (Selection.ModuleChoice.local_moved_ne_bot D)
  rcases c.local_moved_minimal A hAW (le_normalizer_conjugateSpanBy _ _) hBA with he | hc
  · exact he
  · exact (hfix (bot_unique ((le_conjugateSpanBy F L).trans
      ((le_inf hAW hc).trans_eq hz)))).elim

/-- The original reduced orbit contains the local moved subgroup, with no model marking. -/
theorem Context.local_moved_le (c : Context D t v I) :
    ⁅D.moduleSubgroup,L⁆ ≤ orbitModule D v I := by
  rw [←c.local_moved_eq_half_fixed_span]
  apply conjugateSpanBy_mono ?_ c.escaping.strict.le
  exact inf_le_inf (commutator_mono (le_componentOrbit _ _) le_rfl)
    (centralizer_le (le_inf inf_le_left c.escaping.sylow_normalizes))

/-- The literal reduced orbit has its centralizer in the original maximal local subgroup. -/
theorem Context.orbit_centralizer_le (c : Context D t v I) :
    centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal :=
  c.centralizer_le_of_local_moved_le c.local_moved_le

/-- Cubic component order alone completes preparation of the original reduced orbit. -/
theorem Context.prepared_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) : Prepared D v I :=
  c.prepared_of_local_moved_le_of_three hd c.local_moved_le

/-- The literal FF action is available without an original row marking in the cubic branch. -/
theorem Context.actionFacts_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) : ActionFacts c :=
  c.actionFacts (c.prepared_of_three hd)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
