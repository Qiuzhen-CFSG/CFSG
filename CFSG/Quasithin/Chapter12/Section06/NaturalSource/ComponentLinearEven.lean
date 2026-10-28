module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentUnitaryEven
public import Theory.SpecificGroups.PSL3.BinarySylowInverter
public import Theory.SpecificGroups.PSL3Four.NineFreeInnerCentralizer
public import Theory.SpecificGroups.PSL3Four.ThreeRank

/-!
# Binary linear-three restrictions at the original selected component

The marked involution fixes a Sylow two-subgroup and the entire component
center. On a binary PSL₃ central quotient it therefore inverts an element
of exact order 2ⁿ−1 upstairs. The original odd-order restriction forces
n=2 whenever n≥2. Thus the only binary linear cubic cover is SL₃(4).

At field order four the full automorphism centralizer of the inner
involution has no factor nine. The original Sylow E₉ action cannot be
faithful. Rank saturation excludes the ordinary PSL₃(4) component, and
in the cubic cover the literal Sylow-action kernel has order three.
All quotient maps, the original component and the action are retained.

The final constructor keeps condition (*), every preceding alternating
exclusion and both rank alternatives. SL₃(4), cubic A₇/M₂₂, the other
faithful rank-two cases and the rank-one argument remain to be excluded.
Earlier geometry and the contrary nonabelian point-span assumption remain
explicit; neither 12.6.26 nor universal NaturalReduction is concluded.
Source: Aschbacher--Smith, proof of 12.6.26, printed pp.832--833.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- A binary PSL₃ central quotient of degree at least two has field order four. -/
theorem SourceHypothesis.original_selectedComponent_binaryLinear_quotient_degree
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn0 : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL
      ((Nonabelian.Setup.star H c.K) ⧸ center (Nonabelian.Setup.star H c.K)) 3 (2^n)) :
    n = 2 := by
  obtain ⟨F,hFfield,hFfinite,hF,⟨eQ⟩⟩ := hm
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hto : orderOf (t : MulAut B) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective t).trans ht
  obtain ⟨P,hP⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn0 c a
  have ho : Odd (2^n-1) := by
    have he : Even ((2:ℕ)^n) := even_two.pow_of_ne_zero (by omega)
    have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
    exact Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  obtain ⟨x,hx,hi⟩ := Matrix.PSL3.BinarySylowInverter.sylow_fixer_inverts_split_generator_of_fixes_center
    hn hF eQ t hto P (hP t t.property)
    (S.original_action_component_center_fixed D hZ z hz hTV hTz hbound hH hn0 c a t t.property)
  obtain ⟨v,hv,he⟩ := t.property
  let u := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have hu : u ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
  have hxorder : orderOf (x : Nonabelian.Setup.Hstar H) = 2^n-1 := (Subgroup.orderOf_coe x).trans hx
  have hxne : (x : Nonabelian.Setup.Hstar H) ≠ 1 := by
    intro hh
    rw [hh,orderOf_one] at hxorder
    have hl : (2:ℕ)^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
    norm_num at hl
    omega
  have hinv : u*x.val*u⁻¹=x.val⁻¹ := by
    rw [←a.conjugation v x,he]
    exact congrArg Subtype.val hi
  have hord := S.original_star_inverted_odd_order D hZ z hz hTV hTz hbound hns hH u hu x.val hxne
    (hxorder.symm ▸ ho) hinv
  have hpow : (2:ℕ)^n ≤ 6 := by rw [hxorder] at hord; omega
  have hn3 : n < 3 := by
    by_contra! hh
    have hb : (2:ℕ)^3 ≤ 2^n := Nat.pow_le_pow_right (by decide) hh
    norm_num at hb
    omega
  omega

/-- Every binary SL₃ model for the selected component has field order four. -/
theorem SourceHypothesis.original_selectedComponent_binaryLinearCover_degree
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn0 : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    {n : ℕ} (hn : 1 ≤ n) (hmod : (2^n)%3=1)
    (hm : Chapter1.Section02.LocalModels.IsSL (Nonabelian.Setup.star H c.K) 3 (2^n)) :
    n = 2 := by
  obtain ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩ := hm
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  have hn2 : 2 ≤ n := by
    by_contra! hh
    have hn1 : n=1 := by omega
    norm_num [hn1] at hmod
  let eQ : (B ⧸ center B) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro y hy
        exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  exact S.original_selectedComponent_binaryLinear_quotient_degree D hZ z hz hTV hTz hbound hns
    hH hn0 c a hn2 ⟨F,hFfield,hFfinite,hF,⟨eQ⟩⟩

/-- The non-simple catalogue reduces to SL₃(4) and the cubic A₇/M₂₂ covers. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_smallLinear_cover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    let B := Nonabelian.Setup.star H c.K
    IsSimpleGroup B ∨
      (Nonempty (center B ≃* Multiplicative (ZMod 3)) ∧
        (Chapter1.Section02.LocalModels.IsSL B 3 4 ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
        Chapter1.Section02.LocalModels.IsM22Cover B)) := by
  rcases S.original_selectedComponent_simple_or_linear_cover D hZ z hz hTV hTz hbound hns
    hH hn c a with hs|⟨hc,hl|hr⟩
  · exact Or.inl hs
  · obtain ⟨f,hf,hmod,hm⟩ := hl
    have hf2 := S.original_selectedComponent_binaryLinearCover_degree D hZ z hz hTV hTz hbound hns
      hH hn c a hf hmod hm
    exact Or.inr ⟨hc,Or.inl (by simpa only [hf2, Nat.reducePow] using hm)⟩
  · exact Or.inr ⟨hc,Or.inr hr⟩

/-- The marked Sylow E₉ cannot act faithfully on a PSL₃(4) central quotient. -/
theorem SourceHypothesis.original_linearFour_quotient_sylow_not_faithful
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : ClassicalGroup.IsPSL
      ((Nonabelian.Setup.star H c.K) ⧸ center (Nonabelian.Setup.star H c.K)) 3 4)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    ¬ Function.Injective (a.residualSylowAction P) := by
  intro hi
  obtain ⟨F,hFfield,hFfinite,hF,⟨eQ⟩⟩ := hm
  let := hFfield
  let := hFfinite
  let := Fintype.ofFinite F
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
    (by simp only [←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  let e := eQ.trans (Atlas.fieldEquivPSL 3 eF)
  let f := MulAut.centralQuotientAction e
  have hf := MulAut.centralQuotientAction_injective e
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hto : orderOf (t : MulAut B) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective t).trans ht
  have hfo : orderOf (f t) = 2 := (orderOf_injective f hf t).trans hto
  obtain ⟨R,hR⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn c a
  obtain ⟨Q,hQ⟩ := MulAut.centralQuotientAction_exists_fixed_sylow e t R (hR t t.property)
  obtain ⟨w,_,hw⟩ := Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv
    Matrix.PSL3Four.F (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F)
    (MulEquiv.refl _) Q (f t) hQ
  have hw2 : orderOf w = 2 := by
    let : Group.IsPerfect Matrix.PSL3Four.PSL := Atlas.psl_perfect 3 (by decide)
    let : IsSimpleGroup Matrix.PSL3Four.PSL := Atlas.psl_simple_high_rank 3 (by decide)
    exact (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect) w).symm.trans
      (hw ▸ hfo)
  let C := centralizer ({f t} : Set (MulAut Matrix.PSL3Four.PSL))
  let g₀ := f.comp (a.residualSylowAction P)
  have hgmem (p : P) : g₀ p ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    have hAX : E.L₁ ≤ c.localActor := le_sup_right.trans le_sup_left
    have hm : a.residualSylowAction P p ∈ (E.L₁.subgroupOf c.localActor).map a.action :=
      ⟨⟨p.val.val,hAX p.val.property⟩,p.val.property,rfl⟩
    have he := (a.residual_centralizes hm t t.property).symm
    change f (a.residualSylowAction P p) * f t = f t * f (a.residualSylowAction P p)
    simpa only [map_mul] using congrArg f he
  let g := g₀.codRestrict C hgmem
  have hg : Function.Injective g := fun x y he => hi (hf (congrArg Subtype.val he))
  have hPc := (S.original_point_residual_sylow D hZ z hz hTz P).2
  have h9 : 9 ∣ Nat.card C := hPc ▸ card_dvd_of_injective g hg
  have hnot := Matrix.PSL3Four.not_nine_dvd_inner_involution_centralizer w hw2
  apply hnot
  simpa only [C,hw] using h9

/-- All ordinary binary PSL₃ models of degree at least two are excluded. -/
theorem SourceHypothesis.original_selectedComponent_not_binaryLinear
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn0 : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 3 (2^n) := by
  rintro ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let := Fintype.ofFinite F
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup B := e.isSimpleGroup
  have hc : center B = ⊥ := center_eq_bot_of_simple_perfect
  let e₀ : (B ⧸ center B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hn2 := S.original_selectedComponent_binaryLinear_quotient_degree D hZ z hz hTV hTz hbound hns
    hH hn0 c a hn ⟨F,hFfield,hFfinite,hF,⟨e₀.trans e⟩⟩
  have hF4 : Nat.card F = 4 := by simpa only [hn2,Nat.reducePow] using hF
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
    (by simp only [←Nat.card_eq_fintype_card,hF4,Matrix.PSL3Four.card_F])
  have hr : primeRank 3 c.K = 2 := by
    rw [c.three_rank_eq_star]
    apply le_antisymm
    · exact (_root_.primeRank_le_of_injective 3 B.subtype B.subtype_injective).trans
        (S.original_star_three_rank D hZ z hz hH)
    · rw [primeRank_congr 3 (e.trans (Atlas.fieldEquivPSL 3 eF))]
      exact Matrix.PSL3Four.ThreeRank.three_rank_ge_two
  let P : Sylow 3 (D.fullSetup hZ T z).L₁ := default
  exact S.original_linearFour_quotient_sylow_not_faithful D hZ z hz hTV hTz hbound hH hn0 c a
    ⟨F,hFfield,hFfinite,hF4,⟨e₀.trans e⟩⟩ P
    (S.original_rank_two_centerless_sylow_faithful D hZ z hz hTz hH c a hr hc P)

/-- The remaining SL₃(4) cover has a kernel of order three in every original Sylow E₉ action. -/
theorem SourceHypothesis.original_linearFourCover_sylow_kernel_card
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsSL (Nonabelian.Setup.star H c.K) 3 4)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    Nat.card (a.residualSylowAction P).ker = 3 := by
  obtain ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩ := hm
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  have hc : Nat.card (center B) = 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,hF]
    norm_num
  let eQ : (B ⧸ center B) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro y hy
        exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  have hr : primeRank 3 c.K = 2 := by
    rw [c.three_rank_eq_star]
    apply le_antisymm
    · exact (_root_.primeRank_le_of_injective 3 B.subtype B.subtype_injective).trans
        (S.original_star_three_rank D hZ z hz hH)
    · exact two_le_primeRank_of_nontrivial_prime_center (by decide)
        (IsPGroup.of_card (p := 3) (n := 1) hc) (by
          intro heq
          rw [heq,card_bot] at hc
          omega)
  have hd := S.original_rank_two_sylow_kernel_card_dvd_center D hZ z hz hTz hH c a hr P
  rw [hc] at hd
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h1|h3
  · have hk : (a.residualSylowAction P).ker = ⊥ := Subgroup.card_eq_one.mp h1
    exact (S.original_linearFour_quotient_sylow_not_faithful D hZ z hz hTV hTz hbound hH hn c a
      ⟨F,hFfield,hFfinite,hF,⟨eQ⟩⟩ P ((MonoidHom.ker_eq_bot_iff _).mp hk)).elim
  · exact h3

/-- The same original component retains condition (*), all previous exclusions
and rank alternatives, the reduced cover list, the ordinary binary linear
exclusions and the literal SL₃(4) Sylow-action kernel. -/
theorem SourceHypothesis.original_selectedComponent_reduced_linear_cases
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    ∃ c : (D.fullSetup hZ T z).SelectedComponent H, ∃ a : c.ActionMarking,
      let A := (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let C := centralizer (U : Set a.action.range)
      (Nat.card U = 2 ∧ 3 ∣ Nat.card A ∧
        A.subgroupOf C ≤ (pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C)) ∧
        ∃ R : Sylow 2 a.action.range, U ≤ (R : Subgroup a.action.range) ∧
          U ≤ centralizer (R : Set a.action.range)) ∧
      (primeRank 3 c.K = 1 ∨ (primeRank 3 c.K = 2 ∧
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁,
          Function.Injective (a.residualSylowAction P) ∨
            (Nonempty (center (Nonabelian.Setup.star H c.K) ≃* Multiplicative (ZMod 3)) ∧
              Chapter1.Section02.LocalModels.ThreeCoverModel (Nonabelian.Setup.star H c.K)))) ∧
      (∀ n : ℕ, 6 ≤ n → n ≤ 8 →
        ¬ Chapter1.Section02.LocalModels.IsAlternating (Nonabelian.Setup.star H c.K) n) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 6 ∧
      (Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7 →
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁, Nat.card (a.residualSylowAction P).ker = 3) ∧
      (let B := Nonabelian.Setup.star H c.K
       IsSimpleGroup B ∨
         (Nonempty (center B ≃* Multiplicative (ZMod 3)) ∧
           (Chapter1.Section02.LocalModels.IsSL B 3 4 ∨
           Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
           Chapter1.Section02.LocalModels.IsM22Cover B))) ∧
      (∀ n : ℕ, 2 ≤ n → ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 3 (2^n)) ∧
      (Chapter1.Section02.LocalModels.IsSL (Nonabelian.Setup.star H c.K) 3 4 →
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁, Nat.card (a.residualSylowAction P).ker = 3) := by
  obtain ⟨c,a,hc,hr,hAlt,h6,h7⟩ :=
    S.original_selectedComponent_without_alternating_rank_two D hZ z hz hTV hTz hbound hns hH hn
  exact ⟨c,a,hc,hr,hAlt,h6,h7,
    S.original_selectedComponent_simple_or_smallLinear_cover D hZ z hz hTV hTz hbound hns hH hn c a,
    fun n hn2 => S.original_selectedComponent_not_binaryLinear D hZ z hz hTV hTz hbound hns
      hH hn c a hn2,
    fun hm P => S.original_linearFourCover_sylow_kernel_card D hZ z hz hTV hTz hbound hH hn c a hm P⟩

end CFSG.Quasithin.Chapter12.Section06
