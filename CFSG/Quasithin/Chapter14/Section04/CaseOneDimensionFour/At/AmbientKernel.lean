module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.AmbientKernel
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.CentralizerControl

/-!
# The ambient kernel in the original order-32 branch at the original G,T

Put C=C_G(U) and D=C_G(L). The previously proved odd-index averaging
C≤V D sharpens to C=Z(U) D. Since Z(U) is elementary and central in C,
Φ(C)=Φ(D). Thus H and LT both normalize this Frattini subgroup. The
original uniqueness of the maximal two-local overgroup of LT, together
with the escape of H, forces Φ(C)=1. Consequently C and D are elementary.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)

include d setup structural alternatives hne hZ hcard

/-- The centralizer of U is the product of its center and the block centralizer. -/
theorem source_core_centralizer_eq_center_join :
    centralizer (F.U : Set G) = F.ZU ⊔ centralizer (L : Set G) := by
  let := setup.chosen.elementary
  have hUL := (source_block_core d setup structural
    alternatives F hne hZ hcard).2
  have hZC : F.ZU ≤ centralizer (F.U : Set G) := by
    rintro _ ⟨z,hz,rfl⟩ u hu
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨u,hu⟩)
  have hDC : centralizer (L : Set G) ≤ centralizer (F.U : Set G) := centralizer_le hUL
  apply le_antisymm _ (sup_le hZC hDC)
  intro c hc
  have hm := source_core_centralizer_le_seed_join d setup structural alternatives F hne hZ hcard hc
  have hn : V ≤ normalizer (centralizer (L : Set G) : Set G) :=
    ((le_conjugateSpanBy V F.H).trans hUL).trans
      (L.le_normalizer.trans (normalizer_le_normalizer_centralizer L))
  change c ∈ ((V ⊔ centralizer (L : Set G) : Subgroup G) : Set G) at hm
  rw [coe_mul_of_left_le_normalizer_right V (centralizer (L : Set G)) hn] at hm
  obtain ⟨v,hv,x,hx,rfl⟩ := hm
  have hvC : v ∈ centralizer (F.U : Set G) := by
    have hh := (centralizer (F.U : Set G)).mul_mem hc
      ((centralizer (F.U : Set G)).inv_mem (hDC hx))
    simpa only [mul_inv_cancel_right] using hh
  have hvZ : v ∈ F.ZU :=
    ⟨⟨v,le_conjugateSpanBy V F.H hv⟩,
      mem_center_iff.mpr (fun u => Subtype.ext (hvC u u.property)),rfl⟩
  exact (F.ZU ⊔ centralizer (L : Set G)).mul_mem (mem_sup_left hvZ) (mem_sup_right hx)

/-- Ambient uniqueness and flag escape force the whole core centralizer to be elementary. -/
theorem source_core_centralizer_elementary :
    IsElementaryAbelian 2 (centralizer (F.U : Set G)) := by
  let := setup.chosen.elementary
  let H := setup
  let C := centralizer (F.U : Set G)
  let D := centralizer (L : Set G)
  let B := (frattini C).map C.subtype
  have hUL := (source_block_core d setup structural
    alternatives F hne hZ hcard).2
  have hCT : C ≤ (T : Subgroup G) :=
    (centralizer_le (le_conjugateSpanBy V F.H)).trans
      (source_seed_centralizer_le_sylow d setup structural alternatives F hne hZ hcard)
  have hCtwo : IsPGroup 2 C := T.isPGroup'.to_le hCT
  have hZelem : IsElementaryAbelian 2 F.ZU := by
    rw [hZ]
    exact IsElementaryAbelian.of_le (F.le_seed 1)
  have hZC : F.ZU ≤ centralizer (C : Set G) := by
    apply le_centralizer_iff.mp
    exact centralizer_le (map_subtype_le _)
  have hB : B = (frattini D).map D.subtype :=
    frattini_map_eq_of_central_elementary_supplement C D F.ZU hCtwo hZelem hZC
      (source_core_centralizer_eq_center_join d setup structural alternatives F hne hZ hcard)
  have hHN : F.H ≤ normalizer (B : Set G) :=
    ((le_normalizer_conjugateSpanBy V F.H).trans (normalizer_le_normalizer_centralizer F.U)).trans
      (normalizer_le_normalizer_characteristic_image C (frattini C))
  have hTN : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (F.invariant 1).trans hHN
  have hLN : L ≤ normalizer (B : Set G) := by
    rw [hB]
    exact (L.le_normalizer.trans (normalizer_le_normalizer_centralizer L)).trans
      (normalizer_le_normalizer_characteristic_image D (frattini D))
  have hBbot : B = ⊥ := by
    by_contra hn
    have hNM : normalizer (B : Set G) ≤ normalizer (L : Set G) := by
      apply normalizer_le_of_unique_maximalTwoLocal
        (J := L ⊔ (T : Subgroup G)) _ (T.isPGroup'.to_le ((map_subtype_le _).trans hCT))
        hn (sup_le hLN hTN)
      intro N hN hJN
      exact Set.mem_singleton_iff.mp ((H.maximal_unique_at structural).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN,hJN⟩)
    exact H.flag_escape_at F alternatives (hHN.trans hNM)
  let : Fact (IsPGroup 2 C) := ⟨hCtwo⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    (((frattini C).map_eq_bot_iff_of_injective C.subtype_injective).mp hBbot)


/-- The actual two-core is the product of U with the block centralizer. -/
theorem source_twoCore_eq_closure_join_block_centralizer :
    F.H.pCoreIn 2 = F.U ⊔ centralizer (L : Set G) := by
  obtain ⟨q⟩ := source_quaternion d setup structural
    alternatives F hne hZ hcard
  have hCU : centralizer (F.U : Set G) ≤ F.U ⊔ centralizer (L : Set G) := by
    rw [source_core_centralizer_eq_center_join d setup structural alternatives F hne hZ hcard]
    exact sup_le_sup_right (map_subtype_le _) _
  have hCQ : centralizer (F.U : Set G) ≤ F.H.pCoreIn 2 := by
    intro c hc
    have hcH : c ∈ F.H :=
      (Subgroup.centralizer_le_normalizer _)
        ((centralizer_le ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))) hc)
    let x : F.H := ⟨c,hcH⟩
    have hx : F.uAction x = 1 := by
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      change c * (u : G) * c⁻¹ = u
      rw [← hc u u.property,mul_inv_cancel_right]
    have hk : x ∈ pCore 2 F.H := by
      rw [← source_uhat_kernel d setup structural alternatives F hZ]
      change quotientAut (center F.U) (F.uAction x) = 1
      rw [hx,map_one]
    exact mem_map_of_mem F.H.subtype hk
  have hUL := (source_block_core d setup structural
    alternatives F hne hZ hcard).2
  apply le_antisymm _ (sup_le
    (source_closure_le_twoCore d setup structural alternatives F hne)
    ((centralizer_le hUL).trans hCQ))
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
  have hm := (F.U ⊔ centralizer (L : Set G)).mul_mem (mem_sup_left u.property) (hCU hc)
  change (y : G) ∈ F.U ⊔ centralizer (L : Set G)
  simpa only [mul_inv_cancel_left] using hm

/-- The block centralizer is elementary, without assuming a c₂ action. -/
theorem source_block_centralizer_elementary :
    IsElementaryAbelian 2 (centralizer (L : Set G)) := by
  let := source_core_centralizer_elementary d setup structural alternatives F hne hZ hcard
  exact IsElementaryAbelian.of_le (centralizer_le
    (source_block_core d setup structural alternatives F hne hZ hcard).2)

/-- A nontrivial block centralizer has exactly the original ambient normalizer. -/
theorem source_block_centralizer_normalizer_of_ne_bot
    (hneD : centralizer (L : Set G) ≠ ⊥) :
    normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G) := by
  let H := setup
  have hCT : centralizer (L : Set G) ≤ (T : Subgroup G) :=
    (centralizer_le setup.chosen.le_component).trans
      (source_seed_centralizer_le_sylow d setup structural alternatives F hne hZ hcard)
  apply le_antisymm _ (normalizer_le_normalizer_centralizer L)
  apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G)) _
    (T.isPGroup'.to_le hCT) hneD
    ((sup_le L.le_normalizer (H.sylow_normalizes_at structural)).trans
      (normalizer_le_normalizer_centralizer L))
  intro N hN hJN
  exact Set.mem_singleton_iff.mp ((H.maximal_unique_at structural).2 ▸
    show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
      from ⟨hN,hJN⟩)

/-- No nontrivial subgroup of the block centralizer is normalized by H. -/
theorem source_no_common_normal_block_centralizer
    (D : Subgroup G) (hD : D ≤ centralizer (L : Set G))
    (hHN : F.H ≤ normalizer (D : Set G)) : D = ⊥ := by
  let H := setup
  have hDT : D ≤ (T : Subgroup G) := hD.trans
    ((centralizer_le setup.chosen.le_component).trans
      (source_seed_centralizer_le_sylow d setup structural alternatives F hne hZ hcard))
  have hLN : L ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp hD).trans (Subgroup.centralizer_le_normalizer _)
  by_contra hn
  have hNM : normalizer (D : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G)) _
      (T.isPGroup'.to_le hDT) hn (sup_le hLN ((F.invariant 1).trans hHN))
    intro N hN hJN
    exact Set.mem_singleton_iff.mp ((H.maximal_unique_at structural).2 ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN,hJN⟩)
  exact H.flag_escape_at F alternatives (hHN.trans hNM)


/-- The flag point is disjoint from the block centralizer. -/
theorem source_block_centralizer_disjoint_center :
    Disjoint F.ZU (centralizer (L : Set G)) := by
  have hZc : Nat.card F.ZU = 2 := by rw [hZ]; exact F.card 1 (by decide)
  let : Fact (Nat.card F.ZU).Prime := ⟨hZc ▸ Nat.prime_two⟩
  rcases ((centralizer (L : Set G)).subgroupOf F.ZU).eq_bot_or_eq_top_of_prime_card with hb | ht
  · apply disjoint_def.mpr
    intro x hx hz
    have hh : (⟨x,hx⟩ : F.ZU) ∈ (centralizer (L : Set G)).subgroupOf F.ZU := hz
    rw [hb] at hh
    exact congrArg Subtype.val (mem_bot.mp hh)
  · have hZD : F.ZU ≤ centralizer (L : Set G) := by
      intro x hx
      exact show (⟨x,hx⟩ : F.ZU) ∈ (centralizer (L : Set G)).subgroupOf F.ZU from
        ht ▸ mem_top _
    have hHN : F.H ≤ normalizer (F.ZU : Set G) := by
      rw [hZ]
      exact le_rfl
    have he := source_no_common_normal_block_centralizer d setup structural alternatives F hne hZ hcard
      F.ZU hZD hHN
    rw [he,card_bot] at hZc
    omega

/-- The full quaternion closure is disjoint from the block centralizer. -/
theorem source_block_centralizer_disjoint_closure :
    Disjoint F.U (centralizer (L : Set G)) := by
  have hUL := (source_block_core d setup structural
    alternatives F hne hZ hcard).2
  apply disjoint_def.mpr
  intro x hx hxD
  have hxZ : x ∈ F.ZU := ⟨⟨x,hx⟩,
    mem_center_iff.mpr (fun u => Subtype.ext (hxD u (hUL u.property))),rfl⟩
  exact disjoint_def.mp (source_block_centralizer_disjoint_center d setup structural alternatives
    F hne hZ hcard) hxZ hxD

/-- The literal kernel product gives the exact two cardinality formulas. -/
theorem source_extra_kernel_card :
    Nat.card (centralizer (F.U : Set G)) = 2 * Nat.card (centralizer (L : Set G)) ∧
    Nat.card (F.H.pCoreIn 2) = 32 * Nat.card (centralizer (L : Set G)) := by
  have hUL := (source_block_core d setup structural
    alternatives F hne hZ hcard).2
  have hDU : centralizer (L : Set G) ≤ centralizer (F.U : Set G) := centralizer_le hUL
  constructor
  · rw [source_core_centralizer_eq_center_join d setup structural alternatives F hne hZ hcard]
    rw [card_sup_of_disjoint_of_normalizes F.ZU (centralizer (L : Set G))
      (source_block_centralizer_disjoint_center d setup structural alternatives F hne hZ hcard)
      ((hDU.trans (centralizer_le (map_subtype_le _))).trans
        (Subgroup.centralizer_le_normalizer _)),hZ,F.card 1 (by decide)]
    rfl
  · rw [source_twoCore_eq_closure_join_block_centralizer d setup structural alternatives F hne hZ hcard]
    rw [card_sup_of_disjoint_of_normalizes F.U (centralizer (L : Set G))
      (source_block_centralizer_disjoint_closure d setup structural alternatives F hne hZ hcard)
      (hDU.trans (Subgroup.centralizer_le_normalizer _)),hcard]

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
