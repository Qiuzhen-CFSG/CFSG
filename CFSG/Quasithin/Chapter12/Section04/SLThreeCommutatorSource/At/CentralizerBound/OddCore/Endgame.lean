module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore.Containment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.ChapterA.Section01.RankActions.LargeElementary
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.ElementaryAbelian.Injective

/-!
# The odd normal-closure endgame of 12.4.8

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

An odd subgroup normalized by M lies in the odd core of its own normalizer.
That normalizer is quasithin and contains the original elementary V of
order sixteen and the perfect actor L. The actual identity V = [V,L]
therefore makes V centralize the odd subgroup, by A.1.28 and A.1.26.
Applying this to the M-conjugate closure of O(C_G(U)) contradicts inversion
by the fixed involution in V.

The ordinary-layer centralization and construction of the odd closure remain
separate explicit source obligations. The conditional assembly below does
not assert the odd-core exclusion until both are supplied.

Source: Aschbacher–Smith, 12.4.8, printed p.816.
-/

@[expose] public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore
open Section02 SmallFusion ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- The literal closure under M = N_G(V), with no assertion that it is odd. -/
def conjugateClosure (V U : Subgroup G) : Subgroup G :=
  conjugateSpanBy (core U) (normalizer (V : Set G))

/-- The remaining ordinary-layer argument, including exclusion of the
exceptional A₇ action using normality of V in C_G(z). -/
def LayerCentralization : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V U : Subgroup G),
    Configuration T L V U →
      (∀ K : Subgroup G, ¬ IsComponentIn K (centralizer (U : Set G))) →
      ∀ W ≤ U, subgroupCorank U W = 1 → core U ≤ centralizer
        ((componentLayer (centralizer (W : Set G))).map
          (centralizer (W : Set G)).subtype : Set G)

/-- Construct the abelian odd closure from the explicit plane containments.
This implication can be proved independently of their model-theoretic producer. -/
def ClosureConstruction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V U : Subgroup G),
    Configuration T L V U →
      (∀ W ≤ U, subgroupCorank U W = 1 → core U ≤ core W) →
      IsMulCommutative (conjugateClosure V U) ∧
        Nat.Coprime 2 (Nat.card (conjugateClosure V U))

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

/-- The actual A.1.26 application, deriving all rank and commutator premises
from the original chosen module. -/
theorem centralizes_odd_normalized (c : Configuration T L V U)
    (P : Subgroup G) (hodd : Nat.Coprime 2 (Nat.card P))
    (hn : normalizer (V : Set G) ≤ normalizer (P : Set G)) :
    V ≤ centralizer (P : Set G) := by
  let N := normalizer (P : Set G)
  have hVN : V ≤ N := V.le_normalizer.trans hn
  have hLN : L ≤ N := c.chosen.normalizes.trans hn
  let VN := V.subgroupOf N
  let LN := L.subgroupOf N
  let PN := P.subgroupOf N
  let eV : VN ≃* V := subgroupOfEquivOfLe hVN
  let eL : LN ≃* L := subgroupOfEquivOfLe hLN
  let eP : PN ≃* P := subgroupOfEquivOfLe P.le_normalizer
  let _ := c.chosen.elementary
  let : IsElementaryAbelian 2 VN :=
    IsElementaryAbelian.comap_of_injective N.subtype N.subtype_injective V
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect c.hypothesis.maximal_faithful.1.1
  let : Group.IsPerfect LN := Group.IsPerfect.ofSurjective
    (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hcard : 8 < Nat.card VN := by
    rw [Nat.card_congr eV.toEquiv, module_card c.extension c.fixed_nontrivial]
    decide
  have hcomm : VN = ⁅VN, LN⁆ := by
    apply Subgroup.map_injective N.subtype_injective
    simpa only [VN, LN, map_commutator, map_subgroupOf_eq_of_le hVN,
      map_subgroupOf_eq_of_le hLN] using c.chosen.eq_commutator
  have hc := ChapterA.large_elementary_commutator_centralizes_oddCore
    (c.hypothesis.simpleQTKE.quasithin.subgroup N) LN VN
    perfect_twoPerfect hcard hcomm
  let : PN.Normal := normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (P : Set G) from le_rfl)
  have hPN : PN ≤ pPrimeCore 2 N := le_sSup ⟨inferInstance, by
    rwa [Nat.card_congr eP.toEquiv]⟩
  intro v hv p hp
  exact congrArg Subtype.val ((commutator_eq_bot_iff_le_centralizer.mp hc)
    (show (⟨v, hVN hv⟩ : N) ∈ VN from hv)
    ⟨p, P.le_normalizer hp⟩ (hPN hp))

/-- An odd M-conjugate closure contradicts the original nontrivial odd core.
Its oddness is the only remaining closure input to this endgame. -/
theorem false_of_odd_closure (c : Configuration T L V U)
    (hne : pPrimeCore 2 (centralizer (U : Set G)) ≠ ⊥)
    (hodd : Nat.Coprime 2 (Nat.card (conjugateClosure V U))) : False := by
  have hc := centralizes_odd_normalized c (conjugateClosure V U) hodd
    (le_normalizer_conjugateSpanBy _ _)
  obtain ⟨z, _, hfix, _, hi, _, _⟩ := simultaneous_inversion c
  have hzV : z ∈ V := (show fixedSubgroup L V ≤ V from inf_le_left)
    (hfix.symm ▸ mem_zpowers z)
  have hzC := hc hzV
  have hle : core U ≤ conjugateClosure V U := le_conjugateSpanBy _ _
  apply ((core_ne_bot_iff U).mpr hne)
  apply eq_bot_iff.mpr
  intro x hx
  have he : x = x⁻¹ := by
    simpa only [← hzC x (hle hx), mul_inv_cancel_right] using hi x hx
  have hs : (⟨x, hx⟩ : core U) ^ 2 = 1 := by
    apply Subtype.ext
    change x ^ 2 = 1
    rw [pow_two]
    nth_rw 1 [he]
    exact inv_mul_cancel x
  have ho : orderOf (⟨x, hx⟩ : core U) = 1 :=
    Nat.eq_one_of_dvd_coprimes (core_odd U) (orderOf_dvd_of_pow_eq_one hs)
      (_root_.orderOf_dvd_natCard _)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp ho)

/-- Assemble the remaining two source steps into the exact existing case
contract. Both premises must be discharged by their source producers. -/
theorem oddCoreExclusion_of_layer_and_closure
    (layer : LayerCentralization.{u}) (closure : ClosureConstruction.{u}) :
    OddCoreExclusion.{u} := by
  intro G _ _ T L V U c hnc hne
  have hplane : ∀ W ≤ U, subgroupCorank U W = 1 → core U ≤ core W := by
    intro W hWU hcor
    exact core_le_plane_core_of_layer c W hWU hcor (layer G T L V U c hnc W hWU hcor)
  exact false_of_odd_closure c hne (closure G T L V U c hplane).2

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore
