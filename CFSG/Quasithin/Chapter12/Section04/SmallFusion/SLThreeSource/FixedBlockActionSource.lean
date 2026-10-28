module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockAssembly
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionSupplement
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionGeometry
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Preparation
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The original fixed-residual action

Once C_T(V)=V, the original chosen module and the marked normalizer action
identify O₂(LT)=V and LT=LV=L. Thus the image of the actual Sylow T in
L/O₂(L) ≅ SL₃(2) has order eight. The source index |T:R|=2 gives |R:V|=4.

Every a in R outside V fixes at most four vectors: a larger fixed subgroup
would force a to centralize all of V by the marked B.4.8 centralizer bound.
The original plane E is already fixed by R and has order four, so C_V(a)=E.
The final application discharges the action premise of the fixed-residual
assembly, leaving its independent block calculation to its source producer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(2),
printed p.91, and 12.4.5–6, printed pp.813–814.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

private theorem sylow_action_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hself : (T : Subgroup G) ⊓ centralizer (V : Set G) = V) :
    V.relIndex (T : Subgroup G) = 8 := by
  have hcore : (L ⊔ (T : Subgroup G)).pCoreIn 2 = V :=
    (centralizer_eq_core D h hTV).symm.trans hself
  have hjoin : L ⊔ (T : Subgroup G) = L := by
    rw [join_eq_component_sup_core D ext hTV, hcore, sup_eq_left.mpr D.le_component]
  have hTL : (T : Subgroup G) ≤ L := hjoin ▸ le_sup_right
  have hcoreL : L.pCoreIn 2 = V := by rwa [hjoin] at hcore
  have hp : pCore 2 L = V.subgroupOf L := by
    rw [← hcoreL, pCoreIn]
    exact (comap_map_eq_self_of_injective L.subtype_injective (pCore 2 L)).symm
  let S : Sylow 2 L := T.subtype hTL
  let q := QuotientGroup.mk' (pCore 2 L)
  let Sbar : Sylow 2 (L ⧸ pCore 2 L) :=
    S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hcard : Nat.card Sbar = 8 := by
    rw [Sbar.card_eq_multiplicity, Nat.card_congr ext.quotientEquiv.toEquiv,
      Matrix.PSL3Two.card_SL]
    decide +kernel
  have hi : (pCore 2 L).relIndex (S : Subgroup L) = 8 := by
    have hh := relIndex_ker (S : Subgroup L) q
    rw [QuotientGroup.ker_mk'] at hh
    exact hh.trans hcard
  rw [hp, Sylow.coe_subtype, relIndex_subgroupOf hTL] at hi
  exact hi

private theorem single_fixed_plane
    (ext : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v)
    (hself : (T : Subgroup G) ⊓ centralizer (V : Set G) = V)
    (d : LocalGeometry D) (a : G) (ha : a ∈ d.R) (haV : a ∉ V) :
    V ⊓ centralizer ({a} : Set G) = d.E := by
  let W : Subgroup G := V ⊓ centralizer ({a} : Set G)
  have hEW : d.E ≤ W := by
    refine le_inf d.le_module ?_
    intro e he
    exact mem_centralizer_singleton_iff.mpr (ha.2 e he)
  have hW : Nat.card W ≤ 4 := by
    by_contra! hlarge
    have hc := SLThreeCommutatorSource.CentralizerBound.local_centralizer_of_card_gt_four
      ext hne hN W inf_le_left hlarge
    have haC : a ∈ centralizer (W : Set G) := by
      intro w hw
      exact mem_centralizer_singleton_iff.mp hw.2
    exact haV (hself.le ⟨ha.1, hc.le ⟨hTV ha.1, haC⟩⟩)
  exact (eq_of_le_of_card_ge hEW (by rw [d.card_plane]; exact hW)).symm

/-- The original fixed-block action calculation from the structural and marked
module implications of 12.2.2. -/
theorem fixedBlockActionCalculation
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    FixedBlockActionCalculation.{u} := by
  intro G _ _ T L V h D hmodel hne d _hescape hself
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTV := ((structural G T L h).2.2 V D).1
  have hN := SLThreeCommutatorSource.normalizerAction_of_structural_marked
    structural marked G T L V h D hmodel hne
  let _ := D.elementary
  have hVR : V ≤ d.R := le_inf D.le_sylow
    (V.le_centralizer.trans (centralizer_le d.le_module))
  refine ⟨module_card_sixteen ext hne, ?_, single_fixed_plane ext hne hTV hN hself d⟩
  have hi := relIndex_mul_relIndex V d.R (T : Subgroup G) hVR inf_le_left
  rw [d.index, sylow_action_index h ext hTV hself] at hi
  omega

/-- The literal fixed-residual consumer with its independent C.1.34 block
calculation as the sole remaining input beyond the earlier 12.2 implications. -/
theorem fixedResidualCalculation_of_block
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (block : FixedBlockCalculation.{u}) : FixedResidualCalculation.{u} :=
  fixedResidualCalculation_of_block_and_action structural marked block
    (fixedBlockActionCalculation structural marked)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
