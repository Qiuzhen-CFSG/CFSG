module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryInput
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationPrefix
public import CFSG.Quasithin.Chapter10.SourceThompsonControl
public import Theory.GroupTheory.ReducedNormal.SylowCentralizer

/-!
# Core and Thompson control for the alternating-eight point span

Write Q = O₂(LT), E = Ω₁Z(C_T(v)), and W = ⟨E^L⟩. The original local
centralizer theorem gives C_T(V) = Q. Since V and Q lie in C_T(v), E lies
in Ω₁Z(Q). Its L-span W therefore remains elementary and lies in T.
The corrected weight-two seed gives V ≤ W and hence C_T(W) = Q.

If J(T) centralized V, the original normalizer-control theorem would put
N_G(C_T(v)) inside N_G(L), contradicting the supplied outside conjugator.
Thus J(T) moves W. Once LT-normalization of W is established, reducedness
extends from V by the Sylow-centralizer criterion and B.2.7 gives the FF
property for the specified faithful conjugation image.

The final consumer isolates the source supplement
T ≤ L ∨ C_T(v). This supplement implies LT-normalization of W; it is an
explicit premise here. FusionEightGeometryModuleComplete discharges it
using FusionEightGeometryModuleSupplement and constructs PointSpanModule
from the original hypotheses. No fixed-supplement decomposition or
omega-center containment in V is used.

Source: Aschbacher--Smith, 12.2.16, final paragraph, printed p.800,
using 3.2.2(8), 3.2.10(8), and B.2.7. The printed nonfixed Z(T) seed
is replaced by FusionEightGeometrySeed.chosen_le_pointSpan.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
namespace AlternatingEightFusion
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable (C : AlternatingEightFusion T L V)
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
variable (structural : Structural1222 KnownSimple.IsKnownSimple.{u})

include D

omit [Finite G] in
/-- The elementary chosen module centralizes its distinguished point. -/
theorem chosen_le_pointSylow : V ≤ C.pointSylow := by
  let := D.elementary
  intro x hx
  exact ⟨D.le_sylow hx, mem_centralizer_singleton_iff.mpr
    (setLike_mul_comm hx C.v.property)⟩

include h structural

/-- The original LT two-core lies in the literal point centralizer in T. -/
theorem core_le_pointSylow : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ C.pointSylow := by
  rw [← chosen_sylow_centralizer_eq_core h D structural]
  intro x hx
  exact ⟨hx.1, mem_centralizer_singleton_iff.mpr (hx.2 C.v C.v.property).symm⟩

/-- Centrality against V first puts the point omega in Q; it also centralizes Q. -/
theorem pointOmega_le_coreOmega :
    omegaCenterIn C.pointSylow ≤ omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  intro x hx
  obtain ⟨hxT, hxc, hxs⟩ := (mem_omegaCenterIn_iff _ _).mp hx
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨?_, centralizer_le (C.core_le_pointSylow h D structural) hxc, hxs⟩
  rw [← chosen_sylow_centralizer_eq_core h D structural]
  exact ⟨hxT.1, centralizer_le (C.chosen_le_pointSylow D) hxc⟩

/-- L-normalization of Q preserves its central omega and contains the whole span. -/
theorem pointSpan_le_coreOmega :
    C.pointSpan ≤ omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  apply iSup_conjugates_le_of_le_normalizer _ _ _ (C.pointOmega_le_coreOmega h D structural)
  exact ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)).trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))).trans
    (normalizer_le_normalizer_omegaCenterIn _)

/-- The actual L-conjugate span is elementary abelian. -/
theorem pointSpan_elementary : IsElementaryAbelian 2 C.pointSpan :=
  IsElementaryAbelian.of_le (C.pointSpan_le_coreOmega h D structural)

/-- The actual point span lies in the original Sylow subgroup. -/
theorem pointSpan_le_sylow : C.pointSpan ≤ (T : Subgroup G) := by
  intro x hx
  have hc := ((mem_omegaCenterIn_iff _ _).mp (C.pointSpan_le_coreOmega h D structural hx)).1
  rw [← chosen_sylow_centralizer_eq_core h D structural] at hc
  exact hc.1

/-- The original LT two-core centralizes the actual point span. -/
theorem core_centralizes_pointSpan : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
    centralizer (C.pointSpan : Set G) := by
  apply le_centralizer_iff.mp
  intro x hx
  exact ((mem_omegaCenterIn_iff _ _).mp (C.pointSpan_le_coreOmega h D structural hx)).2.1

/-- The span and the chosen module have the same literal Sylow centralizer. -/
theorem pointSpan_sylow_centralizer_eq_core :
    (T : Subgroup G) ⊓ centralizer (C.pointSpan : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le (C.chosen_le_pointSpan D))).trans_eq
      (chosen_sylow_centralizer_eq_core h D structural)
  · rw [← chosen_sylow_centralizer_eq_core h D structural]
    exact le_inf inf_le_left
      ((chosen_sylow_centralizer_eq_core h D structural).le.trans
        (C.core_centralizes_pointSpan h D structural))

theorem pointSpan_reduced_of_normalizes
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (C.pointSpan : Set G)) :
    IsPReduced 2 (C.pointSpan.subgroupOf (L ⊔ (T : Subgroup G))) := by
  let H := L ⊔ (T : Subgroup G)
  let W := C.pointSpan.subgroupOf H
  let := C.pointSpan_elementary h D structural
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.subgroupOf ((C.pointSpan_le_sylow h D structural).trans le_sup_right)
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  apply (((structural G T L h).2.2 V D).2.1).of_le_of_sylow_centralizer_le
    (T.subtype le_sup_right) (fun x hx => C.chosen_le_pointSpan D hx)
  intro x hx y hy
  have hxV : (x : G) ∈ centralizer (V : Set G) := by
    intro v hv
    exact congrArg H.subtype (hx.2 ⟨v, (le_sup_right : (T : Subgroup G) ≤ H) (D.le_sylow hv)⟩ hv)
  have hxQ := (chosen_sylow_centralizer_eq_core h D structural).le ⟨hx.1, hxV⟩
  exact Subtype.ext ((C.core_centralizes_pointSpan h D structural hxQ) y hy)

include C

/-- The outside normalizer of the point Sylow forces the Thompson group to move V. -/
theorem thompson_moves_chosen :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  intro hc
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rcases ((structural G T L h).2.2 V D).2.2.2 with hn | hz
    · exact hn
    · exact (C.z_ne (mem_bot.mp (hz ▸
        (show (C.z : G) ∈ V ⊓ centralizer (L : Set G) from ⟨C.z.property, C.z_fixed⟩)))).elim
  have hfull : (D.fundamentalSetup h.toHypothesis1221).fullModule = V := by
    rw [D.fundamentalSetup_fullModule]
    exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hMV)
      (le_componentOrbit _ _)
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ C.pointSylow := by
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((hc hx) C.v C.v.property).symm
  have hn := (Chapter10.source_two_overgroup_normalizer_le_of_centralizes
    (D.fundamentalSetup h.toHypothesis1221) (hfull.symm ▸ hc)
    C.pointSylow (T.isPGroup'.to_le inf_le_left) hJ).2
  have hn' : normalizer (C.pointSylow : Set G) ≤ normalizer (L : Set G) := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal, D.localOrbit_eq] using hn
  exact C.outside (hn' C.normalizes)

omit D in
/-- The point Sylow normalizes both L and its own central omega, hence their orbit. -/
theorem pointSylow_normalizes_pointSpan :
    C.pointSylow ≤ normalizer (C.pointSpan : Set G) := by
  apply le_normalizer_iff.mpr
  intro t ht x hx
  have hnL := (structural G T L h).1 ht.1
  have hnE := normalizer_le_normalizer_omegaCenterIn C.pointSylow
    (C.pointSylow.le_normalizer ht)
  have hm : C.pointSpan.map (MulAut.conj t).toMonoidHom ≤ C.pointSpan := by
    change (⨆ l : L, (omegaCenterIn C.pointSylow).map
      (MulAut.conj (l : G)).toMonoidHom).map (MulAut.conj t).toMonoidHom ≤ _
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro l
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    apply (le_iSup (fun l : L => (omegaCenterIn C.pointSylow).map
      (MulAut.conj (l : G)).toMonoidHom)
      ⟨t * l * t⁻¹, (mem_normalizer_iff.mp hnL l).mp l.property⟩)
    refine ⟨t * e * t⁻¹, (mem_normalizer_iff.mp hnE e).mp he, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
    group
  exact hm (mem_map_of_mem (MulAut.conj t).toMonoidHom hx)

omit D in
theorem pointSpan_normalizes_of_supplement
    (hs : (T : Subgroup G) ≤ L ⊔ C.pointSylow) :
    L ⊔ (T : Subgroup G) ≤ normalizer (C.pointSpan : Set G) :=
  sup_le (le_normalizer_componentOrbit _ _)
    (hs.trans (sup_le (le_normalizer_componentOrbit _ _)
      (C.pointSylow_normalizes_pointSpan h structural)))

theorem pointSpanModule_of_normalizes
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (C.pointSpan : Set G)) : C.PointSpanModule := by
  have he := C.pointSpan_elementary h D structural
  refine ⟨he, C.pointSpan_le_sylow h D structural, hn,
    C.pointSpan_reduced_of_normalizes h D structural hn, ?_⟩
  let := he
  apply Chapter3.internalActionImage_isFFModule_of_thompson_not_le
    T (L ⊔ (T : Subgroup G)) C.pointSpan le_sup_right
      (C.pointSpan_le_sylow h D structural) hn
  intro hJ
  exact C.thompson_moves_chosen h D structural
    (hJ.trans (centralizer_le (C.chosen_le_pointSpan D)))

theorem pointSpanModule_of_pointSylow_supplement
    (hs : (T : Subgroup G) ≤ L ⊔ C.pointSylow) : C.PointSpanModule :=
  C.pointSpanModule_of_normalizes h D structural
    (C.pointSpan_normalizes_of_supplement h structural hs)

end AlternatingEightFusion
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
