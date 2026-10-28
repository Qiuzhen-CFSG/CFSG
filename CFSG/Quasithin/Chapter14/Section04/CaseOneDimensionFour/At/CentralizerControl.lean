module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.CentralizerControl
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.InvolutionAssembly

/-!
# Centralizer control and the c₂ order-eighteen branch at the original G,T

The literal block and its omitted-point conjugate show that C_G(U)
centralizes every selected outside involution of Wᵍ, hence T∩L. Odd-index
averaging inside L then places C_G(U) in V C_G(L), with the full order-32
central cover retained.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual block controls the centralizer on every selected outside involution. -/
theorem source_core_centralizer_fixes_involution (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g a : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (haX : a ∈ F.X g) (ha : a ^ 2 = 1) (hout : a ∉ F.U) :
    centralizer (F.U : Set G) ≤ centralizer ({a} : Set G) := by
  let := setup.chosen.elementary
  let H := setup
  obtain ⟨q⟩ := source_quaternion d setup structural
    alternatives F hne hZ hcard
  obtain ⟨hVcore, hUL⟩ := source_block_core d setup structural
    alternatives F hne hZ hcard
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  have hVL : V ≤ L := hVU.trans hUL
  have hVident : V.subgroupOf L = pCore 2 L := by
    rw [hVcore]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let : (V.subgroupOf L).Normal := by rw [hVident]; infer_instance
  let e := (QuotientGroup.quotientMulEquivOfEq hVident).trans
    (H.naturalMarking.quotientEquiv.trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm)
  have haL : a ∈ L := ((source_sylow_product d setup structural
    alternatives F hne hZ hcard g hgP hgH).1 ▸ mem_sup_right haX).2
  have haU : a ∈ normalizer (F.U : Set G) :=
    F.X_normalizes_U g (F.P_le_G₂ (by decide) L setup.chosen.normalizes hgP) haX
  have hgV := F.P_le_seed_normalizer L setup.chosen.normalizes hgP
  have hVUg : V ≤ F.U.map (MulAut.conj g⁻¹).toMonoidHom := by
    exact (mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (V : Set G)).inv_mem hgV)).symm.le.trans (map_mono hVU)
  have haUg : a ∈ F.U.map (MulAut.conj g⁻¹).toMonoidHom :=
    map_mono (show F.W ≤ F.U from inf_le_left) haX
  have hcomm : ⁅F.U, F.U⁆ ≤ F.ZU := by
    apply commutator_le.mpr
    intro x hx y hy
    exact ⟨⁅(⟨x,hx⟩ : F.U), ⟨y,hy⟩⁆, q.commutator_mem_center _ _, rfl⟩
  have hmove : ⁅V, zpowers a⁆ ≤ F.ZU.map (MulAut.conj g⁻¹).toMonoidHom := by
    apply (commutator_mono hVUg (zpowers_le.mpr haUg)).trans
    rw [← map_commutator]
    exact map_mono hcomm
  have hcenters : Disjoint (F.ZU.map (MulAut.conj g⁻¹).toMonoidHom) F.ZU := by
    apply disjoint_iff.mpr
    change conjugate F.ZU g ⊓ F.ZU = ⊥
    simpa only [hZ] using F.conjugate_point_inf_ZU (by decide)
      (by rw [hZ, inf_eq_right.mpr (F.le_seed 1)]) g hgV hgH
  have hdisj : Disjoint (F.U ⊓ centralizer (F.U : Set G)) ⁅V, zpowers a⁆ := by
    apply disjoint_def.mpr
    intro x hx hm
    have hxZ : x ∈ F.ZU :=
      ⟨⟨x,hx.1⟩, mem_center_iff.mpr (fun u => Subtype.ext (hx.2 u u.property)), rfl⟩
    exact disjoint_def.mp hcenters (hmove hm) hxZ
  have hfix := QuaternionResidual.core_centralizer_fixes_A_of_block L V F.U
    (zpowers a ⊔ ⁅F.U, zpowers a⁆) hUL hVU q
    (by simpa [F.last] using F.card 3 (by decide)) e
    (H.centralizer_L.le.trans hVcore.ge)
    (H.seed_centralizer_le_at structural)
    a haL ha hout haU hdisj rfl
  intro c hc
  exact mem_centralizer_singleton_iff.mpr
    ((hfix hc) a (mem_sup_left (mem_zpowers a))).symm

/-- The full ambient centralizer of U is already the centralizer of T∩L. -/
theorem source_core_centralizer_eq_sylow_centralizer (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    centralizer (F.U : Set G) = centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨g,s,_,hgP,hgH,hsX,hs,hout,hTL⟩ := source_involution_sylow_exists
    d setup structural alternatives F hne hZ hcard
  rw [hTL]
  apply le_antisymm _ (centralizer_le (show F.U ≤ F.U ⊔ zpowers (s : G) from le_sup_left))
  intro c hc x hx
  have hfix := source_core_centralizer_fixes_involution d setup structural alternatives
    F hne hZ hcard g s hgP hgH hsX (congrArg Subtype.val hs) hout hc
  have hle : F.U ⊔ zpowers (s : G) ≤ centralizer ({c} : Set G) := by
    apply sup_le
    · intro y hy
      exact mem_centralizer_singleton_iff.mpr (hc y hy)
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hfix).symm)
  exact mem_centralizer_singleton_iff.mp (hle hx)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Inversion of the residual quotient forces the residual to centralize C_G(U). -/
theorem source_residual_centralizes_core_centralizer (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hinv : ∀ k : pResidual 2 F.H,
      QuotientGroup.mk' (pCore 2 F.H) (s * k * s⁻¹) =
        (QuotientGroup.mk' (pCore 2 F.H) k)⁻¹) :
    (pResidual 2 F.H).map F.H.subtype ≤
      centralizer (centralizer (F.U : Set G) : Set G) := by
  let C := centralizer (F.U : Set G)
  have hHN : F.H ≤ normalizer (C : Set G) :=
    (le_normalizer_conjugateSpanBy V F.H).trans (normalizer_le_normalizer_centralizer F.U)
  let f : F.H →* MulAut C := C.normalizerMonoidHom.comp (inclusion hHN)
  have hfs : f s = 1 := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change (s : G) * c * (s : G)⁻¹ = c
    have hc := source_core_centralizer_fixes_involution d setup structural alternatives
      F hne hZ hcard g s hgP hgH hsX (congrArg Subtype.val hs) hout c.property
    rw [← mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have hk := pResidual_le_ker_of_inverts_mod_twoCore f s hfs hinv
  rintro x ⟨k,hkK,rfl⟩ c hc
  have he := congrArg Subtype.val (DFunLike.congr_fun (hk hkK) (⟨c,hc⟩ : C))
  change (k : G) * c * (k : G)⁻¹ = c at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The source uniqueness subgroup makes the full block centralizer trivial. -/
theorem source_block_centralizer_eq_bot_of_inversion (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hinv : ∀ k : pResidual 2 F.H,
      QuotientGroup.mk' (pCore 2 F.H) (s * k * s⁻¹) =
        (QuotientGroup.mk' (pCore 2 F.H) k)⁻¹) :
    centralizer (L : Set G) = ⊥ := by
  let := setup.chosen.elementary
  let H := setup
  let C := centralizer (L : Set G)
  have hUL := (source_block_core d setup structural
    alternatives F hne hZ hcard).2
  have hCT : C ≤ (T : Subgroup G) :=
    (centralizer_le ((le_conjugateSpanBy V F.H).trans hUL)).trans
      (source_seed_centralizer_le_sylow d setup structural alternatives F hne hZ hcard)
  have hTN : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (H.sylow_normalizes_at structural).trans (normalizer_le_normalizer_centralizer L)
  have hLN : L ≤ normalizer (C : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_centralizer L)
  have hKN : (pResidual 2 F.H).map F.H.subtype ≤ normalizer (C : Set G) :=
    ((source_residual_centralizes_core_centralizer d setup structural alternatives F hne
      hZ hcard g hgP hgH s hsX hs hout hinv).trans
        (centralizer_le (centralizer_le hUL))).trans (Subgroup.centralizer_le_normalizer _)
  have hHN : F.H ≤ normalizer (C : Set G) := by
    rw [(source_normalizer_factors d setup structural alternatives F hne hZ hcard).2]
    exact sup_le hKN hTN
  by_contra hC
  have hNM : normalizer (C : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal
      (J := L ⊔ (T : Subgroup G)) _ (T.isPGroup'.to_le hCT) hC (sup_le hLN hTN)
    intro N hN hJN
    exact Set.mem_singleton_iff.mp ((H.maximal_unique_at structural).2 ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN,hJN⟩)
  exact H.flag_escape_at F alternatives (hHN.trans hNM)

/-- The c₂ action discharges the centralizer hypothesis of the subsequent
block-cohomology and fusion argument. -/
theorem source_c2_block_centralizer (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) :
    centralizer (L : Set G) = ⊥ :=
  source_block_centralizer_eq_bot_of_inversion d setup structural alternatives F hne hZ hcard
    g hgP hgH s hsX hs hout
    (source_inversion_of_c2 d setup structural alternatives F hne hZ hcard q s hs hc2)
end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Odd-index averaging in L separates the seed part of the core centralizer. -/
theorem source_core_centralizer_le_seed_join (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    centralizer (F.U : Set G) ≤ V ⊔ centralizer (L : Set G) := by
  let := setup.chosen.elementary
  let H := setup
  let S := (T : Subgroup G) ⊓ L
  obtain ⟨hV,hUL⟩ := source_block_core d setup structural
    alternatives F hne hZ hcard
  have hVL : V ≤ L := hV.le.trans (L.pCoreIn_le 2)
  have hVident : V.subgroupOf L = pCore 2 L := by
    rw [hV]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let : (V.subgroupOf L).Normal := by rw [hVident]; infer_instance
  have hVc : Nat.card (pCore 2 L) = 8 := by
    rw [← hVident, Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv]
    simpa [F.last] using F.card 3 (by decide)
  have hLc : Nat.card L = 1344 := by
    have he := H.naturalMarking.quotientEquiv.trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm
    have hqcard : Nat.card (L ⧸ pCore 2 L) = 168 :=
      (Nat.card_congr he.toEquiv).trans Matrix.PSL3Two.card_PSL
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L), hVc, hqcard]
  have hSc : Nat.card S = 64 := (source_sylow_index d setup structural
    alternatives F hne hZ hcard).1
  have hindex : (S.subgroupOf L).index = 21 := by
    have hh := (S.subgroupOf L).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show S ≤ L from inf_le_right)).toEquiv,
      hSc,hLc] at hh
    omega
  have hbound := centralizer_le_sup_of_odd_index L V S hVL
    (le_inf setup.chosen.le_sylow hVL)
    (H.centralizer_L.le.trans hV.ge) (by rw [hindex]; decide)
  apply (le_inf ?_ ?_).trans hbound
  · exact (centralizer_le (le_conjugateSpanBy V F.H)).trans
      (H.seed_centralizer_le_at structural)
  · exact (source_core_centralizer_eq_sylow_centralizer d setup structural alternatives
      F hne hZ hcard).le

/-- In the c₂ branch the full central-quotient kernel is exactly the actual U. -/
theorem source_twoCore_eq_of_c2 (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) : F.U = F.H.pCoreIn 2 := by
  have hCU : centralizer (F.U : Set G) ≤ F.U := by
    have hh := source_core_centralizer_le_seed_join d setup structural alternatives F hne hZ hcard
    rw [source_c2_block_centralizer d setup structural alternatives F hne hZ hcard
      g hgP hgH q s hsX hs hout hc2, sup_bot_eq] at hh
    exact hh.trans (le_conjugateSpanBy V F.H)
  apply le_antisymm (source_closure_le_twoCore d setup structural
    alternatives F hne)
  rintro x ⟨y,hy,rfl⟩
  have hyker : y ∈ F.uhatAction.ker :=
    (source_uhat_kernel d setup structural alternatives F hZ).symm ▸ hy
  obtain ⟨u,hu⟩ := (q.quotientAut_eq_one_iff_inner (F.uAction y)).mp hyker
  have hc : (u : G)⁻¹ * y ∈ centralizer (F.U : Set G) := by
    intro v hv
    have he := congrArg Subtype.val (DFunLike.congr_fun hu (⟨v,hv⟩ : F.U))
    change (u : G) * v * (u : G)⁻¹ = (y : G) * v * (y : G)⁻¹ at he
    calc
      v * ((u : G)⁻¹ * y) = (u : G)⁻¹ * ((u : G) * v * (u : G)⁻¹) * y := by group
      _ = (u : G)⁻¹ * ((y : G) * v * (y : G)⁻¹) * y := by rw [he]
      _ = ((u : G)⁻¹ * y) * v := by group
  have hm := F.U.mul_mem u.property (hCU hc)
  change (y : G) ∈ F.U
  simpa only [mul_inv_cancel_left] using hm
end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The order-eighteen alternative has no outer Sylow extension once the
selected involution has the source c₂ action. -/
theorem source_fusion_of_c2_and_card_eighteen (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) (h18 : Nat.card (HStar F.H) = 18) :
    normalizer (L : Set G) = L := by
  have hcore := source_twoCore_eq_of_c2 d setup structural alternatives F hne hZ hcard
    g hgP hgH q s hsX hs hout hc2
  have hc : Nat.card (pCore 2 F.H) = 32 := by
    rw [← card_map_of_injective F.H.subtype_injective]
    change Nat.card (F.H.pCoreIn 2) = 32
    rwa [← hcore]
  have hH : Nat.card F.H = 576 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 F.H), hc, h18]
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  have hS : Nat.card S = 64 := by
    rw [S.card_eq_multiplicity, hH]
    decide +kernel
  have hT : Nat.card T = 64 := by
    change Nat.card ((T : Subgroup G).subgroupOf F.H) = 64 at hS
    rwa [Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ F.H from
      F.invariant 1)).toEquiv] at hS
  have hTL : ((T : Subgroup G) ⊓ L) = (T : Subgroup G) :=
    eq_of_le_of_card_ge inf_le_left (by
      rw [(source_sylow_index d setup structural
        alternatives F hne hZ hcard).1, hT])
  rw [source_normalizer_eq_join d setup structural alternatives F hne hZ hcard,
    sup_eq_left.mpr (hTL.symm.le.trans inf_le_right)]

/-- Construct all SourceLocalData fields in the order-eighteen c₂ branch.
The remaining source work is the c₂ conclusion and exclusion of order36. -/
theorem source_localData_of_c2_and_card_eighteen (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) (h18 : Nat.card (HStar F.H) = 18) :
    Nonempty (SourceLocalData L F) :=
  source_localData_of_fusion_and_inversion d setup structural alternatives F hne hZ hcard
    (source_fusion_of_c2_and_card_eighteen d setup structural alternatives F hne hZ hcard
      g hgP hgH q s hsX hs hout hc2 h18)
    g hgP hgH s hsX hs hout
    (source_inversion_of_c2 d setup structural alternatives F hne hZ hcard q s hs hc2)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
