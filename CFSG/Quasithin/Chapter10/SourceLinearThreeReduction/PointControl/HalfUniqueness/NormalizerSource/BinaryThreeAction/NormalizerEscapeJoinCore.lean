module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeAbelianCore
public import Theory.GroupTheory.PResidual.RelativeCoreCommutator
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The full MS core inside the original join

Subnormality and two-perfectness identify the full MS core with the
commutator of the original join's two-core and the original component.
When that core is the selected natural factor, its exchanged copy controls
the other component too. Consequently the original orbit moves the join's
two-core exactly onto the original full module. In the abelian MS branch,
the only alternative left by this comparison is the core of order sixty-four.
Source: Aschbacher--Smith 10.2.5 and C.1.34, pp.748 and136--137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The full MS core is the movement of the actual original join core. -/
theorem normalizerEscape_join_core_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
    ⁅(localJoin T L).pCoreIn 2,L⁆ =
      (commutatorCore (L.subgroupOf J)).map J.subtype := by
  dsimp only
  have hc : (L.subgroupOf (localJoin T L)).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  rw [commutator_pCoreIn_eq_intrinsic_of_subnormal L (localJoin T L)
    ((le_componentOrbit L T).trans le_sup_left) hc.subnormal D.faithful.1.2.1,
    normalizerEscape_commutatorCore_map D hn hout e,map_commutator,
    ← MonoidHom.range_eq_map,range_subtype]
  rfl

/-- If the full MS core is the selected natural factor, the same original
orbit moves the original join core exactly onto the full selected module. -/
theorem normalizerEscape_join_core_moved_eq
    (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype = ⁅D.fullModule,L⁆) :
    ⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆ = D.fullModule := by
  let R := (localJoin T L).pCoreIn 2
  have hR : localJoin T L ≤ normalizer (R : Set G) :=
    (localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (localJoin T L)))
  have hmap : R.map (MulAut.conj s.exchange).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp
      (hR ((show (T : Subgroup G) ≤ localJoin T L from le_sup_right) s.exchange_mem))
  have hfirst : ⁅R,L⁆ = ⁅D.fullModule,L⁆ :=
    (normalizerEscape_join_core_component D (selected_nonnormal s) hout s.quotient).trans hc
  have hsecond : ⁅R,L.map (MulAut.conj s.exchange).toMonoidHom⁆ =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
    have hh := congrArg (map (MulAut.conj s.exchange).toMonoidHom) hfirst
    rwa [map_commutator,hmap] at hh
  apply le_antisymm
  · rw [commutator_comm,orbit_eq_pair s]
    apply commutator_sup_le_of_relative_normal D.maximalLocal L _ R D.fullModule
      D.maximalLocal_normalizes_fullModule
      ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer)
      ((show L.map (MulAut.conj s.exchange).toMonoidHom ≤ localOrbit T L from
        (orbit_eq_pair s).symm ▸ le_sup_right).trans (localOrbit T L).le_normalizer)
    · rw [commutator_comm,hfirst]
      exact selected_moved_le s
    · rw [commutator_comm,hsecond]
      exact selected_partner_le s
  · rw [s.generated,←hsecond,←hfirst]
    exact sup_le (commutator_mono le_rfl (le_componentOrbit L T))
      (commutator_mono le_rfl ((orbit_eq_pair s).symm ▸ le_sup_right))

/-- The genuine abelian branch gives either exact movement of the original
join core or a full MS core of order sixty-four. -/
theorem normalizerEscape_abelian_join_core_eq_or_card
    (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))))) :
    ⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆ = D.fullModule ∨
      Nat.card ((commutatorCore
        (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
          (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64 := by
  rcases normalizerEscape_abelian_core_eq_or_card D s hout hc with h | h
  · exact Or.inl (normalizerEscape_join_core_moved_eq D s hout h)
  · exact Or.inr h

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
