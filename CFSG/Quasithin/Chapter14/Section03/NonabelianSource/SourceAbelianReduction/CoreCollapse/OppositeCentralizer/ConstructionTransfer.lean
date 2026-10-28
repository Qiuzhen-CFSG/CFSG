module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.ConstructionCentralizer
public import Theory.GroupTheory.PResidual.SylowJoin

/-!
# The original transfer subgroup and the opposite involution

The nine-group image of O²(H) in H/Q and the residual-core identity give
O²(H)∩T=U and |O²(H)|=288. The original T normalizes R, so O²(H)R is
normal in H and intersects T in UR. The span centralizes V, while
C_U(V)=W≤R; hence its constructed opposite involution cannot belong to UR.
The actual core and residual orders give [H:O²(H)R]=4. This puts the
opposite involution outside H′ and supplies the literal transfer consumer.

Global centralizer recognition and its fusion premise remain with
qt-e-14322-core-collapse; none is asserted by these local calculations.
Source: Aschbacher--Smith 14.3.22, printed p.999.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs

/-- The original two-residual has its full Sylow intersection in U and order 288. -/
theorem source_local_residual_sylow :
    localResidual F ⊓ (T : Subgroup G) = F.U ∧ Nat.card (localResidual F) = 288 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg, he, _, _, _, _, _⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  let K := localResidual F
  let Q := F.H.pCoreIn 2
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hK : K ≤ F.H := map_subtype_le _
  have hUK : F.U ≤ K := U_le_embedded_twoResidual_of_full_orthogonal F dg hZ hne hr
  have hUQ : F.U ≤ Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hUT : F.U ≤ (T : Subgroup G) := normalized_pSubgroup_le_sylow T F.H F.U
    (F.invariant 1) F.U_le_H (le_normalizer_conjugateSpanBy _ _) dg.two
  have hcore : F.U = K.pCoreIn 2 := twoResidual_core_eq_U_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hKQ : K ⊓ Q = F.U := le_antisymm
    ((inf_pCoreIn_le_of_le 2 hK).trans hcore.ge) (le_inf hUK hUQ)
  have hk : q.ker = pCore 2 F.H := by
    rw [QuotientGroup.ker_mk', terminal_kernel_of_center_point F dg hZ]
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨_, _, hRP, hRN, hRc⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hRne : F.terminalDot R ≠ ⊥ := by
    intro hh
    rw [hh, card_bot] at hRc
    omega
  have hres := (ChapterG.Section09.FittingRecognition.Four.full_orthogonal_normal_sylow_residual
    F.terminalRepresentation hr P (F.terminalDot R) hRP hRN hRne).2.1
  have hKdot : (K.subgroupOf F.H).map q = pResidual 2 F.TerminalHdot := by
    rw [show K.subgroupOf F.H = pResidual 2 F.H from
      comap_map_eq_self_of_injective F.H.subtype_injective (pResidual 2 F.H)]
    exact map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)
  have hodd : IsPGroup 3 (pResidual 2 F.TerminalHdot) :=
    IsPGroup.of_card (n := 2) (by simpa using hres)
  have hdis := P.isPGroup'.disjoint_of_coprime hodd (by decide : Nat.Coprime 2 3)
  have hKT : K ⊓ (T : Subgroup G) = F.U := by
    apply le_antisymm ?_ (le_inf hUK hUT)
    intro x hx
    have hxH : x ∈ F.H := hK hx.1
    have hxP : q ⟨x,hxH⟩ ∈ (P : Subgroup F.TerminalHdot) :=
      mem_map_of_mem q (show (⟨x,hxH⟩ : F.H) ∈ (T : Subgroup G).subgroupOf F.H from hx.2)
    have hxK : q ⟨x,hxH⟩ ∈ pResidual 2 F.TerminalHdot :=
      hKdot ▸ mem_map_of_mem q (show (⟨x,hxH⟩ : F.H) ∈ K.subgroupOf F.H from hx.1)
    have hxq : q ⟨x,hxH⟩ = 1 := hdis.le_bot ⟨hxP,hxK⟩
    have hxQ : x ∈ Q := mem_map_of_mem F.H.subtype
      (show (⟨x,hxH⟩ : F.H) ∈ pCore 2 F.H from hk ▸ hxq)
    exact hKQ ▸ (show x ∈ K ⊓ Q from ⟨hx.1,hxQ⟩)
  have hind : F.U.relIndex K = 9 := by
    have hh : (pCore 2 F.H).relIndex (K.subgroupOf F.H) = 9 := by
      rw [← hk, relIndex_ker, hKdot, hres]
    have hh' := relIndex_map_map_of_injective (pCore 2 F.H) (K.subgroupOf F.H)
      F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hK] at hh'
    change Q.relIndex K = (pCore 2 F.H).relIndex (K.subgroupOf F.H) at hh'
    rw [← hh', ← inf_relIndex_right, inf_comm Q K, hKQ] at hh
    exact hh
  have hh := relIndex_mul_card_of_le hUK
  rw [hind, dU.card] at hh
  exact ⟨hKT, hh.symm⟩

/-- The literal transfer subgroup is normal in H, and meets T in RU. -/
theorem source_transfer_subgroup_sylow :
    ((localResidual F ⊔ (F.I₂ (sourceResidual M Mc)).pCoreIn 2).subgroupOf F.H).Normal ∧
    (localResidual F ⊔ (F.I₂ (sourceResidual M Mc)).pCoreIn 2) ⊓ (T : Subgroup G) =
      F.U ⊔ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 := by
  let K := localResidual F
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  have h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hRT : R ≤ (T : Subgroup G) := (source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1
  have hRH : R ≤ F.H := hRT.trans (F.invariant 1)
  have hKH : K ≤ F.H := map_subtype_le _
  have hcore := (source_parabolic_residual_core_structure_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2.2.1
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    change (T : Subgroup G) ≤ normalizer ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 : Set G)
    rw [← hcore]
    exact h.sylow_normalizes_L.trans
      (normalizer_le_normalizer_characteristic_image (sourceResidual M Mc) (pCore 2 (sourceResidual M Mc)))
  have hTR' : (T : Subgroup G).subgroupOf F.H ≤
      normalizer (R.subgroupOf F.H : Set F.H) := by
    rw [← subgroupOf_normalizer_eq hRH]
    exact fun _ ht => hTR ht
  have hres : K.subgroupOf F.H = pResidual 2 F.H :=
    comap_map_eq_self_of_injective F.H.subtype_injective (pResidual 2 F.H)
  constructor
  · rw [subgroupOf_sup hKH hRH, hres]
    exact pResidual_sup_normal_of_sylow_normalizes (T.subtype (F.invariant 1))
      (R.subgroupOf F.H) hTR'
  · have hh := congrArg (Subgroup.map F.H.subtype)
      (pResidual_sup_inf_sylow (T.subtype (F.invariant 1)) (R.subgroupOf F.H)
        (show R.subgroupOf F.H ≤ (T : Subgroup G).subgroupOf F.H from fun _ hx => hRT hx))
    change (((pResidual 2 F.H ⊔ R.subgroupOf F.H) ⊓ (T : Subgroup G).subgroupOf F.H).map F.H.subtype) =
      (((pResidual 2 F.H ⊓ (T : Subgroup G).subgroupOf F.H) ⊔ R.subgroupOf F.H).map F.H.subtype) at hh
    simp only [map_inf _ _ F.H.subtype F.H.subtype_injective, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hRH, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)] at hh
    change (K ⊔ R) ⊓ (T : Subgroup G) = (K ⊓ (T : Subgroup G)) ⊔ R at hh
    rw [(source_local_residual_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1] at hh
    exact hh

/-- The actual opposite involution is outside the transfer subgroup O²(H)R. -/
theorem source_triple_outside_transfer
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a) :
    tripleProduct d a ∉ localResidual F ⊔ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg, he, _, _, _, _, _⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hRQ := (parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hWR : F.W ≤ R := hRQ.ge.trans inf_le_left
  have hRT : R ≤ (T : Subgroup G) := (source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1
  have hRU : R ≤ normalizer (F.U : Set G) :=
    (hRT.trans (F.invariant 1)).trans (le_normalizer_conjugateSpanBy _ _)
  have hRC : R ≤ centralizer (rankTwoSeed T M : Set G) := le_centralizer_iff.mp
    (source_seed_centralizes_parabolic_core hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs)
  have hwC : tripleProduct d a ∈ centralizer (rankTwoSeed T M : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mp (s.plane_centralizes_product hc hv)
  intro hw
  have hwUR : tripleProduct d a ∈ F.U ⊔ R :=
    (source_transfer_subgroup_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2 ▸
      (show tripleProduct d a ∈ (localResidual F ⊔ R) ⊓ (T : Subgroup G) from
        ⟨hw, (s.product_mem_sylow_and_square hc).1⟩)
  have hwprod : tripleProduct d a ∈ (R : Set G) * (F.U : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right R F.U hRU, sup_comm]
    exact hwUR
  obtain ⟨r, hrR, u, huU, hmul⟩ := hwprod
  have huC : u ∈ centralizer (rankTwoSeed T M : Set G) := by
    have hh := (centralizer (rankTwoSeed T M : Set G)).mul_mem
      ((centralizer (rankTwoSeed T M : Set G)).inv_mem (hRC hrR)) hwC
    simpa only [← hmul, inv_mul_cancel_left] using hh
  have huW : u ∈ F.W := by
    change u ∈ F.U ⊓ centralizer (F.Vi 2 : Set G)
    rw [F.last]
    exact ⟨huU,huC⟩
  have hwR : tripleProduct d a ∈ R := hmul ▸ R.mul_mem hrR (hWR huW)
  have hcore := (source_parabolic_residual_core_structure_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2.2.1
  exact source_triple_outside_residual hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
    ((hcore ▸ pCoreIn_le 2 (sourceResidual M Mc)) hwR)

/-- In the cyclic-four branch the actual transfer quotient has order four. -/
theorem source_transfer_subgroup_index
    (hc : CyclicTIInput F (sourceResidual M Mc)) :
    ((localResidual F ⊔ (F.I₂ (sourceResidual M Mc)).pCoreIn 2).subgroupOf F.H).index = 4 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg, he, _, _, _, _, _⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  let K := localResidual F
  let Q := F.H.pCoreIn 2
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let D := supplement F
  have hUQ : F.U ≤ Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hUD : F.U ⊓ D = F.Vi 1 := by
    change F.U ⊓ (Q ⊓ centralizer (F.U : Set G)) = F.Vi 1
    rw [← inf_assoc, inf_eq_left.mpr hUQ]
    exact (centerIn_eq_inf_centralizer F.U).symm.trans hZ
  have hDU : D ≤ normalizer (F.U : Set G) := inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hQ : Q = F.U ⊔ D := core_eq_U_sup_centralizer F dg hZ dU
  have hQc : Nat.card Q = 64 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes F.U D hDU
    rw [dU.card, hc.card, hUD, show Nat.card (F.Vi 1) = 2 from by
      simpa using F.card 1 (by decide), ← hQ] at hh
    omega
  have hHc : Nat.card F.H = 4608 := by
    let q := QuotientGroup.mk' F.terminalHatAction.ker
    have hk : q.ker = pCore 2 F.H := by
      rw [QuotientGroup.ker_mk', terminal_kernel_of_center_point F dg hZ]
    have hQintr : Nat.card (pCore 2 F.H) = 64 := by
      simpa only [Q, pCoreIn, card_map_of_injective F.H.subtype_injective] using hQc
    obtain ⟨ee, _, _⟩ := hr
    have hdot : Nat.card F.TerminalHdot = 72 :=
      (Nat.card_congr (ee.trans topEquiv).toEquiv).trans
        ChapterG.Section09.FittingRecognition.Four.card_orthogonalFour
    have hh := q.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      Nat.card_congr topEquiv.toEquiv, hk, hQintr, hdot] at hh
    exact hh.symm
  have hRT : R ≤ (T : Subgroup G) := (source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1
  have hRH : R ≤ F.H := hRT.trans (F.invariant 1)
  have hKH : K ≤ F.H := map_subtype_le _
  have hUK : F.U ≤ K := U_le_embedded_twoResidual_of_full_orthogonal F dg hZ hne hr
  have hcore : F.U = K.pCoreIn 2 := twoResidual_core_eq_U_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hKQ : K ⊓ Q = F.U := le_antisymm
    ((inf_pCoreIn_le_of_le 2 hKH).trans hcore.ge) (le_inf hUK hUQ)
  obtain ⟨hRQ, _, _, _, hRdot⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hUR : F.U ⊓ R = F.W := le_antisymm
    ((inf_le_inf_right R hUQ).trans (inf_comm Q R ▸ hRQ.le))
    (le_inf inf_le_left (hRQ.ge.trans inf_le_left))
  have hKR : K ⊓ R = F.W := by
    have hh : K ⊓ R = (K ⊓ (T : Subgroup G)) ⊓ R := by
      rw [inf_assoc, inf_eq_right.mpr hRT]
    rw [hh, (source_local_residual_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1, hUR]
  have hRc : Nat.card R = 64 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hh, _⟩ :=
      source_elementary_factors_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    exact hh
  have hWc : Nat.card F.W = 16 := by
    let q := QuotientGroup.mk' F.terminalHatAction.ker
    have hk : q.ker = pCore 2 F.H := by
      rw [QuotientGroup.ker_mk', terminal_kernel_of_center_point F dg hZ]
    have hidx : Q.relIndex R = 4 := by
      have hh := relIndex_map_map_of_injective (pCore 2 F.H) (R.subgroupOf F.H)
        F.H.subtype_injective
      rw [map_subgroupOf_eq_of_le hRH] at hh
      change Q.relIndex R = (pCore 2 F.H).relIndex (R.subgroupOf F.H) at hh
      rw [hh, ← hk, relIndex_ker]
      exact hRdot
    have hh := relIndex_mul_card_of_le (show R ⊓ Q ≤ R from inf_le_left)
    rw [inf_comm R Q, inf_relIndex_right, hidx, inf_comm Q R, hRQ, hRc] at hh
    omega
  have hKc : Nat.card K = 288 :=
    (source_local_residual_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2
  have hRK : R ≤ normalizer (K : Set G) := hRH.trans (le_normalizer_embedded_pResidual 2 F.H)
  have hNc : Nat.card (K ⊔ R : Subgroup G) = 1152 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes K R hRK
    rw [hKc, hRc, hKR, hWc] at hh
    omega
  have hh := ((K ⊔ R).subgroupOf F.H).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (sup_le hKH hRH)).toEquiv, hNc, hHc] at hh
  change ((K ⊔ R).subgroupOf F.H).index = 4
  omega

/-- The constructed opposite involution is outside the actual point-centralizer
commutator, using its normal quotient of order four. -/
theorem source_triple_outside_point_commutator
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a) :
    tripleProduct d a ∉ (_root_.commutator F.H).map F.H.subtype := by
  let N := (localResidual F ⊔ (F.I₂ (sourceResidual M Mc)).pCoreIn 2).subgroupOf F.H
  let : N.Normal := (source_transfer_subgroup_sylow
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1
  have hquot : Nat.card (F.H ⧸ N) = 2 ^ 2 := source_transfer_subgroup_index
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  let : IsMulCommutative (F.H ⧸ N) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hquot
  have hle : _root_.commutator F.H ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rintro ⟨x, hx, he⟩
  exact source_triple_outside_transfer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
    (he ▸ hle hx)

/-- Literal application of the transfer quotient to the constructed opposite
involution. The remaining fusion premise belongs to global recognition. -/
theorem source_false_of_triple_fusion
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
    (hf : ∀ x ∈ centralizer ({tripleProduct d a} : Set G), IsConj z x →
      ∃ c ∈ centralizer ({tripleProduct d a} : Set G), c * z * c⁻¹ = x) : False := by
  have hH : F.H = centralizer ({z} : Set G) := F.H_eq_centralizer (by decide) z s.point
  have hT : (T : Subgroup G) ≤ centralizer ({z} : Set G) := hH ▸ F.invariant 1
  have hwT := (s.product_mem_sylow_and_square hc).1
  have hwC := hT hwT
  have hw1 : tripleProduct d a ≠ 1 := by
    intro hh
    exact source_triple_outside_transfer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
      (hh ▸ (localResidual F ⊔ (F.I₂ (sourceResidual M Mc)).pCoreIn 2).one_mem)
  have hnotC : (⟨tripleProduct d a, hwC⟩ : centralizer ({z} : Set G)) ∉
      _root_.commutator (centralizer ({z} : Set G)) := by
    intro hx
    have hh := mem_map_of_mem (centralizer ({z} : Set G)).subtype hx
    change tripleProduct d a ∈ (_root_.commutator (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype at hh
    rw [← hH] at hh
    exact source_triple_outside_point_commutator
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hh
  let : IsMulCommutative ((centralizer ({z} : Set G)) ⧸
      _root_.commutator (centralizer ({z} : Set G))) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  exact NonabelianSource.false_of_centralizer_fusion hG T z (tripleProduct d a) hT hwC
    (_root_.commutator (centralizer ({z} : Set G))) (s.involution_of_ne_one hc hw1).2 hnotC hf

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
