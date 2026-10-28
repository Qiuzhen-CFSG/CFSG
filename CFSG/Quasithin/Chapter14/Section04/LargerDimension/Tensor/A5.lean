module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Quotients
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.PermutingConjugateClosure

/-!
# Centralizer and residual reductions for the A₅ tensor branch

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma
14.4.10(3), printed p.1011. The literal X₁, X₂ and K₀ come from
`Tensor.Family`. Once the A₅ calculation gives [X₂,V₂] ≤ Z(U), the
three-subgroups lemma and the two-layer residual centralizer theorem give
X₂ ≤ C_G(V). This excludes X₂ from Y and recovers L₁ = X₁. Normalization
then passes to L₂ and its conjugate closure I₂.

The last source sentence is corrected using 12.8.9(1): I₂ = O²(P)U.
The two-residual fixes a component with orbit at most two, and U ≤ K₀
normalizes K₀. All normality and orbit conditions are relative to G₀,
and only O²(P), not the full P, is required to lie in G₀.

These are intermediate implications. The source action must still provide
the commutator bound; the nontrivial-core argument must still identify K₀
as the selected component. Neither core branch of the full A₅ exclusion
is asserted here.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.A5
variable {G : Type*} [Group G] [Finite G]

theorem second_centralizes_of_two_layers {H T V Z : Subgroup G}
    (hZ : IsPGroup 2 Z) (hfix : second H T ≤ centralizer (Z : Set G))
    (hquot : ⁅second H T, V⁆ ≤ Z) :
    second H T ≤ centralizer (V : Set G) := by
  have h := residual_centralizes_of_two_layer (second H T) V Z hZ hfix hquot
  change twoResidual (second H T) ≤ centralizer (V : Set G) at h
  simpa only [second, twoResidual_idempotent] using h

theorem second_not_mem_Y_of_two_layers {H T V₂ E Z : Subgroup G}
    (hZ : IsPGroup 2 Z) (hfix : second H T ≤ centralizer (Z : Set G))
    (hquot : ⁅second H T, V₂⁆ ≤ Z) :
    second H T ∉ YFamily H T V₂ E := by
  intro hy
  have hc := second_centralizes_of_two_layers hZ hfix hquot
  have he : movedSpace V₂ (second H T) = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
  have hh := hy.2.1
  rw [he, Subgroup.card_bot] at hh
  norm_num at hh

omit [Finite G] in
theorem first_eq_L₁_of_second_not_mem_Y {H T V₂ E L₁ : Subgroup G}
    (hf : XFamily H T = {first H, second H T})
    (hL : L₁ ∈ YFamily H T V₂ E)
    (hsecond : second H T ∉ YFamily H T V₂ E) : first H = L₁ := by
  have hmem : L₁ ∈ ({first H, second H T} : Set (Subgroup G)) := hf ▸ hL.1
  rcases Set.mem_insert_iff.mp hmem with h | h
  · exact h.symm
  · exact False.elim (hsecond ((Set.mem_singleton_iff.mp h) ▸ hL))

private theorem residual_le_index_two {D : Type*} [Group D]
    (N : Subgroup D) (hN : N.index = 2) : pResidual 2 D ≤ N := by
  let : N.Normal := N.normal_of_index_eq_two hN
  apply sInf_le
  refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
  simpa only [← N.index_eq_card, pow_one] using hN

omit [Finite G] in
theorem residual_normalizes_of_small_orbit {D K P : Subgroup G}
    (hKD : K ≤ D) (hPD : P ≤ D)
    (horbit : (K.subgroupOf D).Normal ∨
      (normalizer (K.subgroupOf D : Set D)).index = 2) :
    twoResidual P ≤ normalizer (K : Set G) := by
  rcases horbit with hn | hi
  · exact (map_subtype_le _).trans
      (hPD.trans ((normal_subgroupOf_iff_le_normalizer hKD).mp hn))
  · have hr := residual_le_index_two _ hi
    have hm := map_pResidual_le 2 (inclusion hPD)
    rintro _ ⟨p, hp, rfl⟩
    have hn := hr (hm (mem_map_of_mem (inclusion hPD) hp))
    rw [← subgroupOf_normalizer_eq hKD] at hn
    exact hn

/-- The corrected 12.8.9(1) product only requires I ≤ D; P need not lie in D. -/
theorem residual_product_normalizes {D K P U I : Subgroup G}
    (hKD : K ≤ D) (hID : I ≤ D) (hUK : U ≤ K)
    (hI : I = twoResidual P ⊔ U)
    (horbit : (K.subgroupOf D).Normal ∨
      (normalizer (K.subgroupOf D : Set D)).index = 2) :
    I ≤ normalizer (K : Set G) := by
  have hrD : twoResidual P ≤ D := by rw [hI] at hID; exact le_sup_left.trans hID
  have hr := residual_normalizes_of_small_orbit hKD hrD horbit
  rw [twoResidual_idempotent] at hr
  rw [hI]
  exact sup_le hr (hUK.trans K.le_normalizer)

theorem residual_product_normalizes_center_core {D K P U I V₁ : Subgroup G}
    (hKD : K ≤ D) (hID : I ≤ D) (hUK : U ≤ K)
    (hI : I = twoResidual P ⊔ U)
    (horbit : (K.subgroupOf D).Normal ∨
      (normalizer (K.subgroupOf D : Set D)).index = 2)
    (hV₁ : (center (twoCore K)).map (twoCore K).subtype = V₁) :
    I ≤ normalizer (V₁ : Set G) := by
  rw [← hV₁]
  exact ((residual_product_normalizes hKD hID hUK hI horbit).trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))).trans
      (normalizer_le_normalizer_characteristic_image (twoCore K) (center (twoCore K)))

theorem second_centralizes_first_moved {H T U V₂ Z : Subgroup G}
    (hZ : IsPGroup 2 Z) (hHZ : H ≤ centralizer (Z : Set G))
    (hV₂ : V₂ ≤ U) (hU : U ≤ H) (hclass : ⁅U, U⁆ ≤ Z)
    (hpair : ⁅first H, second H T⁆ ≤ U)
    (hquot : ⁅second H T, V₂⁆ ≤ Z) :
    second H T ≤ centralizer (movedSpace V₂ (first H) : Set G) := by
  have hN : H ≤ normalizer (Z : Set G) :=
    hHZ.trans (Subgroup.centralizer_le_normalizer _)
  apply second_centralizes_of_two_layers hZ ((second_le H T).trans hHZ)
  rw [commutator_comm]
  apply commutator_commutator_le_of_rotate_of_le_normalizer
    ((hV₂.trans hU).trans hN) ((first_le H).trans hN) ((second_le H T).trans hN)
  · exact (commutator_mono hpair hV₂).trans hclass
  · exact (commutator_mono hquot le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp ((first_le H).trans hN))

/-- The first source reduction after the marked A₅ fixed-space calculation. -/
theorem initial_reduction {H T U V₂ E L₁ V Z M : Subgroup G}
    (hf : XFamily H T = {first H, second H T})
    (hL : L₁ ∈ YFamily H T V₂ E) (hV : movedSpace V₂ L₁ = V)
    (hZ : IsPGroup 2 Z) (hHZ : H ≤ centralizer (Z : Set G))
    (hV₂ : V₂ ≤ U) (hU : U ≤ H) (hclass : ⁅U, U⁆ ≤ Z)
    (hpair : ⁅first H, second H T⁆ ≤ U)
    (hquot : ⁅second H T, V₂⁆ ≤ Z)
    (hM : centralizer (V : Set G) ≤ M) :
    second H T ∉ YFamily H T V₂ E ∧ L₁ = first H ∧
      V = movedSpace V₂ (first H) ∧
      second H T ≤ centralizer (V : Set G) ∧ second H T ≤ M := by
  have hn := second_not_mem_Y_of_two_layers (E := E) hZ
    ((second_le H T).trans hHZ) hquot
  have he := first_eq_L₁_of_second_not_mem_Y hf hL hn
  have hv : V = movedSpace V₂ (first H) := by rw [he, hV]
  have hc : second H T ≤ centralizer (V : Set G) := by
    rw [hv]
    exact second_centralizes_first_moved hZ hHZ hV₂ hU hclass hpair hquot
  exact ⟨hn, he.symm, hv, hc, hc.trans hM⟩

omit [Finite G] in
theorem second_normalizes_L₂ {H T L L₂ V₂ M : Subgroup G}
    (hLM : L ≤ M) (hL : (L.subgroupOf M).Normal)
    (hsecond : second H T ≤ M)
    (hV₂ : second H T ≤ centralizer (V₂ : Set G))
    (hL₂ : L₂ = twoResidual (L ⊓ normalizer (V₂ : Set G))) :
    second H T ≤ normalizer (L₂ : Set G) := by
  rw [hL₂]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))
  exact (le_inf (hsecond.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp hL))
    (hV₂.trans ((Subgroup.centralizer_le_normalizer _).trans (normalizer _).le_normalizer))).trans
      inf_normalizer_le_normalizer_inf

omit [Finite G] in
theorem second_normalizes_I₂ {H T L₂ I₂ : Subgroup G}
    (hL₂ : second H T ≤ normalizer (L₂ : Set G))
    (hI₂ : I₂ = closure {x : G | ∃ l : L₂, ∃ u : twoCore H,
      x = (l : G) * (u : G) * (l : G)⁻¹}) :
    second H T ≤ normalizer (I₂ : Set G) := by
  rw [hI₂]
  apply le_normalizer_conjugate_closure_of_mul_subset
  · exact (second_le H T).trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  · rw [← coe_mul_of_right_le_normalizer_left _ _ hL₂]
    rintro _ ⟨x, hx, l, hl, rfl⟩
    exact (L₂ ⊔ second H T).mul_mem
      ((le_sup_right : second H T ≤ L₂ ⊔ second H T) hx)
      ((le_sup_left : L₂ ≤ L₂ ⊔ second H T) hl)

/-- The literal G₀ = ⟨I₂,H∞⟩. -/
def generated (H I₂ : Subgroup G) : Subgroup G := I₂ ⊔ component H

/-- The literal V₀ = ⟨z^{G₀}⟩ when z belongs to G₀. The definition uses
the full inverse image of the singleton and does not choose a lift. -/
def involutionClosure (H I₂ : Subgroup G) (z : G) : Subgroup G :=
  (normalClosure ((generated H I₂).subtype ⁻¹' {z})).map (generated H I₂).subtype

omit [Finite G] in
theorem involutionClosure_le (H I₂ : Subgroup G) (z : G) :
    involutionClosure H I₂ z ≤ generated H I₂ := map_subtype_le _

omit [Finite G] in
theorem mem_involutionClosure {H I₂ : Subgroup G} {z : G}
    (hz : z ∈ generated H I₂) : z ∈ involutionClosure H I₂ z := by
  exact mem_map.mpr ⟨⟨z, hz⟩, subset_normalClosure (by rfl), rfl⟩

omit [Finite G] in
theorem involutionClosure_ne_bot {H I₂ : Subgroup G} {z : G}
    (hz : z ∈ generated H I₂) (hne : z ≠ 1) : involutionClosure H I₂ z ≠ ⊥ := by
  intro he
  have hm := mem_involutionClosure hz
  rw [he, mem_bot] at hm
  exact hne hm

omit [Finite G] in
theorem involutionClosure_normal (H I₂ : Subgroup G) (z : G) :
    ((involutionClosure H I₂ z).subgroupOf (generated H I₂)).Normal := by
  unfold involutionClosure
  rw [← comap_subtype, comap_map_eq_self_of_injective (generated H I₂).subtype_injective]
  infer_instance

/-- Actual application of the corrected residual argument to K₀ = H∞.
The preceding component-selection argument must supply `horbit`. -/
theorem component_orbit_contradiction {H I₂ P U V₁ : Subgroup G}
    (hU : U ≤ component H) (hI : I₂ = twoResidual P ⊔ U)
    (horbit : ((component H).subgroupOf (generated H I₂)).Normal ∨
      (normalizer ((component H).subgroupOf (generated H I₂) : Set (generated H I₂))).index = 2)
    (hV₁ : (center (twoCore (component H))).map (twoCore (component H)).subtype = V₁)
    (houtside : ¬ I₂ ≤ normalizer (V₁ : Set G)) : False := by
  exact houtside (residual_product_normalizes_center_core
    (show component H ≤ generated H I₂ from le_sup_right)
    (show I₂ ≤ generated H I₂ from le_sup_left) hU hI horbit hV₁)


/-! ### Source branch assemblies -/

/-- Raw clauses for constructing genuine F.1.1 in the core-free branch. -/
structure CoreFreeInput (G₀ K₀ I₂ T : Subgroup G) : Prop where
  finite_T : Finite T
  T_isP : IsPGroup 2 T
  T_normalizes : T ≤ normalizer (K₀ : Set G) ∧ T ≤ normalizer (I₂ : Set G)
  sylow_K₀ : ∃ S : Sylow 2 K₀, (S : Subgroup K₀).map K₀.subtype = T ⊓ K₀
  sylow_I₂ : ∃ S : Sylow 2 I₂, (S : Subgroup I₂).map I₂.subtype = T ⊓ I₂
  quotient_K₀ : CFSG.Quasithin.ChapterF.Source.IsRankOneModel (K₀ ⧸ pCore 2 K₀)
  quotient_I₂ : CFSG.Quasithin.ChapterF.Source.IsRankOneModel (I₂ ⧸ pCore 2 I₂)
  cross_K₀ : CFSG.Quasithin.ChapterF.Source.borel I₂ T ≤ normalizer (K₀ : Set G)
  cross_I₂ : CFSG.Quasithin.ChapterF.Source.borel K₀ T ≤ normalizer (I₂ : Set G)
  core_free : pCore 2 G₀ = ⊥
  generated_eq : CFSG.Quasithin.ChapterF.Source.generated ![K₀, I₂] T = G₀
  characteristic_K₀ :
    Theory.GroupTheory.generalizedFitting
        (CFSG.Quasithin.ChapterF.Source.parabolic ![K₀, I₂] T 0) =
      pCore 2 (CFSG.Quasithin.ChapterF.Source.parabolic ![K₀, I₂] T 0)
  characteristic_I₂ :
    Theory.GroupTheory.generalizedFitting
        (CFSG.Quasithin.ChapterF.Source.parabolic ![K₀, I₂] T 1) =
      pCore 2 (CFSG.Quasithin.ChapterF.Source.parabolic ![K₀, I₂] T 1)

omit [Finite G] in
theorem CoreFreeInput.toHypothesis {G₀ K₀ I₂ T : Subgroup G}
    (h : CoreFreeInput G₀ K₀ I₂ T) :
    CFSG.Quasithin.ChapterF.Source.HypothesisF11 ![K₀, I₂] T := by
  refine {
    finite_S := h.finite_T
    S_isP := h.T_isP
    S_normalizes := ?_
    sylow := ?_
    quotient := ?_
    cross := ?_
    twoCore_free := ?_
    characteristic_two := ?_ }
  · intro i; fin_cases i
    · exact h.T_normalizes.1
    · exact h.T_normalizes.2
  · intro i; fin_cases i
    · exact h.sylow_K₀
    · exact h.sylow_I₂
  · intro i; fin_cases i
    · exact h.quotient_K₀
    · exact h.quotient_I₂
  · intro i; fin_cases i
    · simpa [CFSG.Quasithin.ChapterF.Source.other] using h.cross_K₀
    · simpa [CFSG.Quasithin.ChapterF.Source.other] using h.cross_I₂
  · rw [h.generated_eq]
    exact h.core_free
  · intro i; fin_cases i
    · simpa [CFSG.Quasithin.ChapterF.Source.parabolic] using h.characteristic_K₀
    · simpa [CFSG.Quasithin.ChapterF.Source.parabolic] using h.characteristic_I₂

omit [Finite G] in
theorem core_free_excluded {G₀ K₀ I₂ T : Subgroup G}
    (h : CoreFreeInput G₀ K₀ I₂ T)
    (hf112 : ∀ _h : CFSG.Quasithin.ChapterF.Source.HypothesisF11 ![K₀, I₂] T,
      False) : False :=
  hf112 h.toHypothesis

/-- The nontrivial-core source data: selected component, maximality, the
correct residual product, and the relative orbit alternative. -/
structure NontrivialCoreInput (G₀ H I₂ T V₁ U P : Subgroup G) where
  core_nontrivial : twoCore G₀ ≠ ⊥
  generated_eq : generated H I₂ = G₀
  fstar_eq_core : Theory.GroupTheory.generalizedFitting G₀ = pCore 2 G₀
  selected : Subgroup G
  selected_isC : Subgroup.IsCComponent selected
  selected_le : selected ≤ G₀
  k0_le_selected : component H ≤ selected
  k0_local : component H ∈ CFSG.Quasithin.Chapter1.L G T
  selected_local : selected ∈ CFSG.Quasithin.Chapter1.L G T
  maximal_component : ∀ L : Subgroup G, L ∈ CFSG.Quasithin.Chapter1.L G T →
    L ≤ selected → L = selected
  residual_product : I₂ = twoResidual P ⊔ U
  U_le_selected : U ≤ selected
  component_orbit :
    ((component H).subgroupOf G₀).Normal ∨
      (normalizer ((component H).subgroupOf G₀ : Set G₀)).index = 2
  center_V₁ : (center (twoCore (component H))).map
      (twoCore (component H)).subtype = V₁
  outside_normalizer : ¬ I₂ ≤ normalizer (V₁ : Set G)

theorem nontrivial_core_excluded {G₀ H I₂ T V₁ U P : Subgroup G}
    (h : NontrivialCoreInput G₀ H I₂ T V₁ U P) : False := by
  have heq : component H = h.selected :=
    h.maximal_component (component H) h.k0_local h.k0_le_selected
  have hU : U ≤ component H := heq ▸ h.U_le_selected
  have horbit :
      ((component H).subgroupOf (generated H I₂)).Normal ∨
        (normalizer ((component H).subgroupOf (generated H I₂) :
          Set (generated H I₂))).index = 2 := by
    rw [h.generated_eq]
    exact h.component_orbit
  exact component_orbit_contradiction hU h.residual_product horbit h.center_V₁
    h.outside_normalizer

/-- The actual two-core split, retaining both source branches. -/
theorem a5_module_excluded
    {G₀ H I₂ T V₁ U P : Subgroup G}
    (hcore : twoCore G₀ = ⊥ ∨ twoCore G₀ ≠ ⊥)
    (hfree : twoCore G₀ = ⊥ → CoreFreeInput G₀ (component H) I₂ T)
    (hf112 : twoCore G₀ = ⊥ →
      ∀ _h : CFSG.Quasithin.ChapterF.Source.HypothesisF11
          ![component H, I₂] T, False)
    (hnontrivial : twoCore G₀ ≠ ⊥ →
      NontrivialCoreInput G₀ H I₂ T V₁ U P) : False := by
  let _ := ‹Finite G›
  rcases hcore with h | h
  · exact core_free_excluded (hfree h) (hf112 h)
  · exact nontrivial_core_excluded (hnontrivial h)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.A5

end
