module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.TwoCoreAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Parabolic

/-!
# The extra two-core action in the original order-32 source branch at the original G,T

With Z(U) equal to the flagged point, the earlier tilded action-kernel
calculation is also the kernel calculation on U/Z(U). The actual block
and point-core equalities then supply all block premises of the quaternion
core-action theorem. Thus, in the swapping branch, the intersection of
O₂(H) with N_{O²(H)}(A) induces exactly the same four-group on
A = ⟨a,[U,a]⟩ as U does. The full central cover U has order 32 throughout.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
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
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hZ : F.ZU = F.Vi 1) :
    F.uhatAction.ker = pCore 2 F.H := by
  let := setup.chosen.elementary
  rw [← source_action_kernel d setup structural alternatives F]
  ext h
  rw [F.mem_uhatAction_ker_iff, F.mem_localTildeAction_ker_iff, hZ]
  rfl

/-- Choose the omitted-point conjugator inside the actual L, using T≤P∩H. -/
theorem source_internal_conjugator (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    ∃ g : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H := by
  let := setup.chosen.elementary
  let H := setup
  obtain ⟨x, _, hxP, hxH, _⟩ := source_parabolic_generators d setup structural
    alternatives F hne hZ hcard
  have hx : x ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G) (H.sylow_normalizes_at structural)]
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
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g a : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (haX : a ∈ F.X g) (ha : a ^ 2 = 1) (hout : a ∉ F.U) :
    (T : Subgroup G) ⊓ L = F.U ⊔ zpowers a ∧
    ((T : Subgroup G) ⊓ L) ≤ normalizer
      ((zpowers a ⊔ ⁅F.U, zpowers a⁆ : Subgroup G) : Set G) := by
  let := setup.chosen.elementary
  obtain ⟨hprod, _, _, _⟩ := source_sylow_product d setup structural
    alternatives F hne hZ hcard g hgP hgH
  have haTL : a ∈ (T : Subgroup G) ⊓ L := hprod ▸ mem_sup_right haX
  have hTL : (T : Subgroup G) ⊓ L = F.U ⊔ zpowers a := by
    apply (eq_of_le_of_card_ge (sup_le (hprod ▸ le_sup_left)
      (zpowers_le.mpr haTL)) ?_).symm
    rw [card_sup_zpowers_of_normalizing_involution F.U a ha hout
      (F.X_normalizes_U g (F.P_le_G₂ (by decide) L setup.chosen.normalizes hgP) haX), hcard]
    rw [(source_sylow_index d setup structural
      alternatives F hne hZ hcard).1]
  exact ⟨hTL, hTL ▸ normalizes_generated_commutator F.U a⟩

/-- The original source arrangement discharges the block, kernel and
residual-containment premises of the extra two-core calculation. -/
theorem source_extra_twoCore_action (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
  let := setup.chosen.elementary
  let H := setup
  have hHU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  obtain ⟨hV, _⟩ := source_block_core d setup structural
    alternatives F hne hZ hcard
  obtain ⟨_, hUc, _, _⟩ := source_point_core d setup structural
    alternatives F hne hZ hcard
  obtain ⟨_, hUK, _⟩ := source_point_cubic d setup structural
    alternatives F hne hZ hcard
  obtain ⟨hTL, hAN⟩ := source_involution_sylow d setup structural
    alternatives F hne hZ hcard g a hgP hgH haX ha hout
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
    exact source_uhat_kernel d setup structural alternatives F hZ
  exact QuaternionCoreAction.image_and_index F.H L (F.Li L 1) V F.U
    (zpowers a ⊔ ⁅F.U, zpowers a⁆) ((T : Subgroup G) ⊓ L)
    ((F.Li_le L 1).trans inf_le_left) hV hUc hclosure (le_conjugateSpanBy V F.H)
    (by simpa [F.last] using F.card 3 (by decide)) q
    (H.naturalMarking.quotientEquiv.trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm)
    (H.centralizer_L.le.trans hV.ge) (H.seed_centralizer_le_at structural)
    hHU hk hUK g a haTL.2 ha hout hswap (point_centralizer F hZ) hgL hgH
    ((map_mono (show F.W ≤ F.U from inf_le_left)) haX) rfl hTL hAN

/-- Apply the proved source index-four calculation to the quaternion-generator
consumer. The outer index and centralizer bound remain source obligations of
qt-d-14414-g2-source. -/
theorem source_quaternion_generators_of_outer_indices (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
  obtain ⟨hTL, hAN⟩ := source_involution_sylow d setup structural
    alternatives F hne hZ hcard g a hgP hgH haX ha hout
  have hfour := (source_extra_twoCore_action d setup structural alternatives F hne hZ
    hcard q g a hgL hgP hgH haX ha hout hswap).2
  have hUK := (source_point_cubic d setup structural
    alternatives F hne hZ hcard).2.1
  exact quaternionGenerators_of_residual_indices F.H F.U (zpowers a ⊔ ⁅F.U, zpowers a⁆)
    ((T : Subgroup G) ⊓ L) q a ha hout hswap rfl hTL hAN hUK
    (le_normalizer_conjugateSpanBy V F.H) hcentral hfour hthree

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
