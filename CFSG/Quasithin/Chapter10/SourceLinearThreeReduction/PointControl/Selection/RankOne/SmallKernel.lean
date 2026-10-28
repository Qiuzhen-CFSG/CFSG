module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.EvenReduction

/-!
# Rank-one point control with a fixed kernel of order at most two

The literal half-Sylow normalizes both original moved kernels. For a kernel
of order at most two, this is pointwise centralization. Crossed centralization
identifies their join with the whole L₀-fixed layer. The rank-one Baumann
argument therefore supplies point control in every field degree, including
even degree with a kernel of order two. Larger even-degree kernels remain
with the source assembly; their stabilization is not a coordinate consequence.

Source: Aschbacher--Smith, 10.1.1(1) and 10.2.9, printed pp.741,750.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A trivial or order-two moved kernel is fixed by the original half-Sylow. -/
theorem fixed_layer_centralizes_half_sylow_of_small_kernel
    (hcard : Nat.card (sourceMovedFixed D) ≤ 2)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
      centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
  by_cases hz : sourceMovedFixed D = ⊥
  · rw [fixed_layer_eq_bot_of_zero_kernel D hz ht htn hcross]
    exact bot_le
  have hk2 : Nat.card (sourceMovedFixed D) = 2 := by
    have hp := (Subgroup.one_lt_card_iff_ne_bot _).mpr hz
    omega
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let W := ⁅D.fullModule,L⁆
  let B := L.map (MulAut.conj t).toMonoidHom
  let U := W.map (MulAut.conj t).toMonoidHom
  have hSM : S ≤ D.maximalLocal := inf_le_left.trans (le_normalizer_componentOrbit L T)
  have hSW : S ≤ normalizer (W : Set G) :=
    (le_inf hSM inf_le_right).trans (source_moved_normalizer_local_containment D)
  have hSK : S ≤ normalizer (sourceMovedFixed D : Set G) :=
    (le_inf inf_le_right hSW).trans (source_original_moved_fixed_normalizer D)
  have hSB : S ≤ normalizer (B : Set G) :=
    (le_inf inf_le_right hSM).trans (source_nonnormal_component_normalizer_fixes_opposite
      D (fun hn => htn (hn ht)) ht htn)
  have hmap : U = ⁅D.fullModule,B⁆ := by
    dsimp [U,W,B]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))]
  have hSU : S ≤ normalizer (U : Set G) := by
    rw [hmap]
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (hSM hs)),
      mem_normalizer_iff_map_conj_eq.mp (hSB hs)]
  have hKmap : (sourceMovedFixed D).map (MulAut.conj t).toMonoidHom =
      U ⊓ centralizer (B : Set G) := by
    change (W ⊓ centralizer (L : Set G)).map (MulAut.conj t).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj t).injective,Theory.GroupTheory.map_centralizer_equiv]
    rfl
  have hSK' : S ≤ normalizer
      (((sourceMovedFixed D).map (MulAut.conj t).toMonoidHom) : Set G) := by
    rw [hKmap]
    exact (le_inf hSU (hSB.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf
  have hk2' : Nat.card ((sourceMovedFixed D).map (MulAut.conj t).toMonoidHom) = 2 :=
    (card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
      (K := sourceMovedFixed D) (MulAut.conj t).injective).trans hk2
  rw [BinaryThree.fixed_layer_eq_moved_kernels D ht htn hcross]
  exact sup_le
    (le_centralizer_iff.mpr (hSK.trans (normalizer_le_centralizer_of_card_two _ hk2)))
    (le_centralizer_iff.mpr (hSK'.trans (normalizer_le_centralizer_of_card_two _ hk2')))

/-- All rank-one geometry follows on the original module and exchanger. -/
theorem point_geometry_of_small_kernel
    (hnotA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D) (hcard : Nat.card (sourceMovedFixed D) ≤ 2)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    RankOnePointGeometry D t :=
  point_geometry_of_fixed_layer D hnotA5 hmodel ht htn
    (fixed_layer_centralizes_half_sylow_of_small_kernel D hcard ht htn hcross)

/-- The actual point consumer retains only its supplied half-Sylow uniqueness. -/
theorem pointSylowControl_of_small_kernel
    (hnotA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D) (hcard : Nat.card (sourceMovedFixed D) ≤ 2)
    (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    PointSylowControl D t := by
  have hg := point_geometry_of_small_kernel D hnotA5 hmodel hcard ht htn hcross
  exact pointSylowControl_of_baumann_orbits D hhalf hg.fixed_layer ht htn hcross
    hg.baumann_normalizer hg.fixed_orbits

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
