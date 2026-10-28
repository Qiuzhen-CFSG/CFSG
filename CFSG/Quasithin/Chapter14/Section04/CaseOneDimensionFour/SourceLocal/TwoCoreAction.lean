module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Parabolic
public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.LocalActions.QuaternionResidual.CoreAction
public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.LocalActions.QuaternionResidual
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The extra two-core action in the original order-32 source branch

With Z(U) equal to the flagged point, the earlier tilded action-kernel
calculation is also the kernel calculation on U/Z(U). The actual block
and point-core equalities then supply all block premises of the quaternion
core-action theorem. Thus, in the swapping branch, the intersection of
O₂(H) with N_{O²(H)}(A) induces exactly the same four-group on
A = ⟨a,[U,a]⟩ as U does. The full central cover U has order 32 throughout.

An omitted-point conjugator can be chosen inside L: remove its T-factor
from the previously constructed element of P. Every outside involution of
its literal Wᵍ generates T∩L together with U. This also proves the required
normalization of A by T∩L. The final consumer supplies the index-four
premise of QuaternionGenerators from the original source arrangement.

The universal earlier input EarlierSetupResults retains 1.2.7 uniqueness,
12.2.2 and 12.2.13. The outer index-three and centralizer conclusions remain
explicit in the consumer; the ambient lifting control, nonsplit exclusion
and fusion argument still belong to qt-d-14414-g2-source. This module does
not assert SourceLocalData. Earlier source premises and the final order-32
recognition must still be discharged in that assembly, with universal I.4.5
owned by qt-i45-g2-recognition and final 14.4.14 by qt-d-14414-source.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
12.8.4(4), printed p.850, and the proof of 14.4.4, printed p.1007.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open DimensionFour.SplitImage
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem normalizes_generated_commutator (U : Subgroup G) (a : G) :
    U ⊔ zpowers a ≤ normalizer ((zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup G) : Set G) := by
  let A := zpowers a ⊔ ⁅U, zpowers a⁆
  apply sup_le _ ((show zpowers a ≤ A from le_sup_left).trans A.le_normalizer)
  intro u hu
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    apply sup_le
    · apply zpowers_le.mpr
      change MulAut.conj u a ∈ A
      have he : MulAut.conj u a = ⁅u, a⁆ * a := by
        simp only [MulAut.conj_apply, commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
      rw [he]
      exact A.mul_mem (mem_sup_right (commutator_mem_commutator hu (mem_zpowers a)))
        (mem_sup_left (mem_zpowers a))
    · rw [mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_left U (zpowers a) hu)]
      exact le_sup_right
  · rw [card_map_of_injective (MulAut.conj u).injective]

/-- The earlier tilded kernel is the literal central-quotient kernel when Z(U)=V₁. -/
theorem source_uhat_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hZ : F.ZU = F.Vi 1) :
    F.uhatAction.ker = pCore 2 F.H := by
  let := chosen.elementary
  rw [← source_action_kernel d earlier hq chosen previous F]
  ext h
  rw [F.mem_uhatAction_ker_iff, F.mem_localTildeAction_ker_iff, hZ]
  rfl

/-- Choose the omitted-point conjugator inside the actual L, using T≤P∩H. -/
theorem source_internal_conjugator (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    ∃ g : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨x, _, hxP, hxH, _⟩ := source_parabolic_generators d earlier hq chosen structural
    alternatives F hne hZ hcard
  have hx : x ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G) (H.sylow_normalizes structural)]
    exact hxP.1
  obtain ⟨g, hg, t, ht, he⟩ := hx
  have htP : t ∈ F.P L := F.binary_sylow_le_P L ht
  refine ⟨g, hg, ?_, ?_⟩
  · have hm := (F.P L).mul_mem hxP ((F.P L).inv_mem htP)
    rwa [← he, mul_inv_cancel_right] at hm
  · intro hgH
    exact hxH (he ▸ F.H.mul_mem hgH (F.invariant 1 ht))

/-- Any selected involution in Wᵍ−U generates the actual T∩L over U.
This Sylow intersection normalizes the generated subgroup ⟨a,[U,a]⟩. -/
theorem source_involution_sylow (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g a : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (haX : a ∈ F.X g) (ha : a ^ 2 = 1) (hout : a ∉ F.U) :
    (T : Subgroup G) ⊓ L = F.U ⊔ zpowers a ∧
    ((T : Subgroup G) ⊓ L) ≤ normalizer
      ((zpowers a ⊔ ⁅F.U, zpowers a⁆ : Subgroup G) : Set G) := by
  let := chosen.elementary
  obtain ⟨hprod, _, _, _⟩ := source_sylow_product d earlier hq chosen structural
    alternatives F hne hZ hcard g hgP hgH
  have haTL : a ∈ (T : Subgroup G) ⊓ L := hprod ▸ mem_sup_right haX
  have hTL : (T : Subgroup G) ⊓ L = F.U ⊔ zpowers a := by
    apply (eq_of_le_of_card_ge (sup_le (hprod ▸ le_sup_left)
      (zpowers_le.mpr haTL)) ?_).symm
    rw [card_sup_zpowers_of_normalizing_involution F.U a ha hout
      (F.X_normalizes_U g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) haX), hcard]
    rw [(source_sylow_index d earlier hq chosen structural
      alternatives F hne hZ hcard).1]
  exact ⟨hTL, hTL ▸ normalizes_generated_commutator F.U a⟩

/-- The original source arrangement discharges the block, kernel and
residual-containment premises of the extra two-core calculation. -/
theorem source_extra_twoCore_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (q : QuaternionCentralProductData F.U)
    (g a : G) (hgL : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (haX : a ∈ F.X g) (ha : a ^ 2 = 1) (hout : a ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj a).toMonoidHom =
      q.right.map F.U.subtype) :
    let A := zpowers a ⊔ ⁅F.U, zpowers a⁆
    QuaternionResidual.image A
      (((pResidual 2 F.H).map F.H.subtype ⊓ normalizer (A : Set G)) ⊓ F.H.pCoreIn 2) =
        QuaternionResidual.image A F.U ∧
    (centralizer (A : Set G)).relIndex
      (((pResidual 2 F.H).map F.H.subtype ⊓ normalizer (A : Set G)) ⊓ F.H.pCoreIn 2) = 4 := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  have hHU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  obtain ⟨hV, _⟩ := source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  obtain ⟨_, hUc, _, _⟩ := source_point_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  obtain ⟨_, hUK, _⟩ := source_point_cubic d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  obtain ⟨hTL, hAN⟩ := source_involution_sylow d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard g a hgP hgH haX ha hout
  have haTL : a ∈ (T : Subgroup G) ⊓ L := hTL ▸ mem_sup_right (mem_zpowers a)
  have hclosure : F.U = (normalClosure (V.subgroupOf F.H : Set F.H)).map F.H.subtype := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy V F.H
      ((le_conjugateSpanBy V F.H).trans F.U_le_H)]
    exact (map_subgroupOf_eq_of_le F.U_le_H).symm
  have hk : (QuaternionCoreAction.quotientAction F.H F.U hHU).ker = pCore 2 F.H := by
    have he : QuaternionCoreAction.quotientAction F.H F.U hHU = F.uhatAction := by
      ext x y
      rfl
    rw [he]
    exact source_uhat_kernel d earlier hq chosen previous F hZ
  exact QuaternionCoreAction.image_and_index F.H L (F.Li L 1) V F.U
    (zpowers a ⊔ ⁅F.U, zpowers a⁆) ((T : Subgroup G) ⊓ L)
    ((F.Li_le L 1).trans inf_le_left) hV hUc hclosure (le_conjugateSpanBy V F.H)
    (by simpa [F.last] using F.card 3 (by decide)) q
    (H.naturalMarking.quotientEquiv.trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm)
    (H.centralizer_L.le.trans hV.ge) (H.seed_centralizer_le previous.structural previous.uniqueness)
    hHU hk hUK g a haTL.2 ha hout hswap (point_centralizer F hZ) hgL hgH
    ((map_mono (show F.W ≤ F.U from inf_le_left)) haX) rfl hTL hAN

/-- Apply the proved source index-four calculation to the quaternion-generator
consumer. The outer index and centralizer bound remain source obligations of
qt-d-14414-g2-source. -/
theorem source_quaternion_generators_of_outer_indices (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (q : QuaternionCentralProductData F.U)
    (g a : G) (hgL : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (haX : a ∈ F.X g) (ha : a ^ 2 = 1) (hout : a ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj a).toMonoidHom =
      q.right.map F.U.subtype)
    (hcentral : ((pResidual 2 F.H).map F.H.subtype ⊓
      normalizer ((zpowers a ⊔ ⁅F.U, zpowers a⁆ : Subgroup G) : Set G)) ⊓
        centralizer ((zpowers a ⊔ ⁅F.U, zpowers a⁆ : Subgroup G) : Set G) ≤ F.H.pCoreIn 2)
    (hthree : (F.H.pCoreIn 2).relIndex
      ((pResidual 2 F.H).map F.H.subtype ⊓
        normalizer ((zpowers a ⊔ ⁅F.U, zpowers a⁆ : Subgroup G) : Set G)) = 3) :
    Nonempty (QuaternionGenerators (zpowers a ⊔ ⁅F.U, zpowers a⁆)
      ((pResidual 2 F.H).map F.H.subtype) ((T : Subgroup G) ⊓ L)) := by
  obtain ⟨hTL, hAN⟩ := source_involution_sylow d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard g a hgP hgH haX ha hout
  have hfour := (source_extra_twoCore_action d earlier hq chosen previous F hne hZ
    hcard q g a hgL hgP hgH haX ha hout hswap).2
  have hUK := (source_point_cubic d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).2.1
  exact quaternionGenerators_of_residual_indices F.H F.U (zpowers a ⊔ ⁅F.U, zpowers a⁆)
    ((T : Subgroup G) ⊓ L) q a ha hout hswap rfl hTL hAN hUK
    (le_normalizer_conjugateSpanBy V F.H) hcentral hfour hthree

/-- Construct the internal conjugator and quaternion marking from the source,
then give the two-core bound for every selected swapping involution. Selecting
such an involution and excluding the swapping branch remain with this owner. -/
theorem source_swapping_core_geometry (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    ∃ (q : QuaternionCentralProductData F.U) (g : G),
      g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧
      ∀ a : G, a ∈ F.X g → a ^ 2 = 1 → a ∉ F.U →
        (q.left.map F.U.subtype).map (MulAut.conj a).toMonoidHom =
          q.right.map F.U.subtype →
        let A := zpowers a ⊔ ⁅F.U, zpowers a⁆
        IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
          (centralizer (A : Set G)).relIndex
            (((pResidual 2 F.H).map F.H.subtype ⊓ normalizer (A : Set G)) ⊓
              F.H.pCoreIn 2) = 4 := by
  obtain ⟨q⟩ := source_quaternion d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  obtain ⟨g, hgL, hgP, hgH⟩ := source_internal_conjugator d earlier hq chosen
    previous.structural previous.alternatives F hne hZ hcard
  refine ⟨q, g, hgL, hgP, hgH, ?_⟩
  intro a haX ha hout hswap
  obtain ⟨_, he, hc⟩ := q.elementary_sixteen_of_swap F.U a ha hout hswap
  exact ⟨he, hc, (source_extra_twoCore_action d earlier hq chosen previous F hne hZ
    hcard q g a hgL hgP hgH haX ha hout hswap).2⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
