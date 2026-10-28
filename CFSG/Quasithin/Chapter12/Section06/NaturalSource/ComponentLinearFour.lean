module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentLinearEven
public import Theory.SpecificGroups.SL3.FourCubicFixedPlane

/-!
# Excluding the final linear-three cover at the original component

The actual Sylow E₉ action on a putative SL₃(4) component has kernel of
order three. Choose a nonidentity cubic in that action. The marked V-star
involution fixes a Sylow two-subgroup, so it is inner. Its inner projective
centralizer has order 64: the chosen cubic actor is therefore outer.

The cubic commutes with the marked involution, so the concrete SL₃(4)
calculation supplies a pointwise fixed E₉ in the same component. The
original cubic lift through H → H/O₂(H) has order three and lies outside
the component. It consequently generates an E₂₇ with that fixed plane,
contradicting the original ambient three-rank bound of two.

The final constructor retains condition (*), both rank alternatives and
all previous exclusions. Only cubic A₇ and M₂₂ remain among nonsimple
components. Their exclusions, the remaining simple-component branches,
abelian point span and universal NaturalReduction remain obligations;
the earlier geometry is still explicit throughout.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original selected component cannot be the remaining SL₃(4) cover.
Its actual cubic actor would centralize an E₉ inside the component and
produce an E₂₇ in the unchanged H-star. -/
theorem SourceHypothesis.original_selectedComponent_not_linearFourCover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    ¬ Chapter1.Section02.LocalModels.IsSL (Nonabelian.Setup.star H c.K) 3 4 := by
  intro hm
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let P : Sylow 3 E.L₁ := default
  have hker := S.original_linearFourCover_sylow_kernel_card D hZ z hz hTV hTz hbound hH hn c a hm P
  obtain ⟨hP,hPc⟩ := S.original_point_residual_sylow D hZ z hz hTz P
  let := hP
  obtain ⟨p,hp⟩ : ∃ p : P, a.residualSylowAction P p ≠ 1 := by
    by_contra! hh
    have hk : (a.residualSylowAction P).ker = ⊤ := by
      ext p
      simp only [MonoidHom.mem_ker,mem_top,iff_true]
      exact hh p
    rw [hk,card_top,hPc] at hker
    omega
  let j : P →* c.localActor := (inclusion (show E.L₁ ≤ c.localActor from
    le_sup_right.trans le_sup_left)).comp (P : Subgroup E.L₁).subtype
  let α := a.residualSylowAction P p
  have hp3 : p^3=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 3 P) p
  have hα3 : α^3=1 := by
    change a.residualSylowAction P p ^ 3=1
    rw [←map_pow,hp3,map_one]
  have hαo : orderOf α=3 := orderOf_eq_prime hα3 hp
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U=2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  let β : MulAut B := t
  have hβo : orderOf β=2 := (orderOf_injective U.subtype U.subtype_injective t).trans ht
  have hab : Commute α β := by
    have hm : α ∈ (E.L₁.subgroupOf c.localActor).map a.action :=
      ⟨j p,p.val.property,rfl⟩
    exact (a.residual_centralizes hm t t.property).symm
  obtain ⟨F,hFfield,hFfinite,hF,⟨e₀⟩⟩ := hm
  let := hFfield
  let := hFfinite
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
    (by simp only [←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  let e : B ≃* Matrix.PSL3Four.SL := e₀.trans (Atlas.fieldEquivSL 3 eF)
  let eQ : (B ⧸ center B) ≃* Matrix.PSL3Four.PSL := QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  let f := MulAut.centralQuotientAction eQ
  have hf := MulAut.centralQuotientAction_injective eQ
  obtain ⟨R,hR⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn c a
  obtain ⟨Q,hQ⟩ := MulAut.centralQuotientAction_exists_fixed_sylow eQ β R (hR t t.property)
  obtain ⟨w,_,hw⟩ := Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv
    Matrix.PSL3Four.F (n := 2) (by decide) Matrix.PSL3Four.card_F
    (MulEquiv.refl _) Q (f β) hQ
  obtain ⟨v,hv⟩ := (MulAut.centralQuotientAction_inner_iff eQ β).mp ⟨w,hw⟩
  have hβi : MulAut.congr e β ∈ MulAut.innerSubgroup Matrix.PSL3Four.SL := by
    refine ⟨e v,?_⟩
    rw [hv]
    ext x
    simp
  obtain ⟨N,hN,hNc,hNfix⟩ := Matrix.SL3.FourCubicFixedPlane.exists_fixed_nine_of_commuting_inner_involution
    (MulAut.congr e α) (MulAut.congr e β)
    (by rw [←map_pow,hα3,map_one]) ((MulAut.congr e).orderOf_eq β |>.trans hβo)
    hβi (hab.map (MulAut.congr e).toMonoidHom)
  let := hN
  let N₀ := N.map e.symm.toMonoidHom
  let W := N₀.map B.subtype
  let : IsElementaryAbelian 3 N₀ := IsElementaryAbelian.map e.symm.toMonoidHom
  let : IsElementaryAbelian 3 W := IsElementaryAbelian.map B.subtype
  have hWc : Nat.card W=3^2 := by
    rw [card_map_of_injective B.subtype_injective,card_map_of_injective e.symm.injective]
    exact hNc
  let q := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion a.local_le)
  let x := q (j p)
  have hx3 : x^3=1 := by
    change q (j p)^3=1
    rw [←map_pow,←map_pow,hp3,map_one,map_one]
  have hxB : x ∉ B := by
    intro hx
    have hαi : α=MulAut.conj (⟨x,hx⟩ : B) := by
      ext k
      exact a.conjugation (j p) k
    let C := Matrix.PSL3Four.InnerInvolutionCentralizers.innerCentralizer (f β)
    have hmem : f α ∈ C := by
      refine ⟨?_,mem_centralizer_singleton_iff.mpr (hab.map f).eq⟩
      rw [hαi,MulAut.centralQuotientAction_conj]
      exact ⟨_,rfl⟩
    have hbc : Nat.card C=64 :=
      Matrix.PSL3Four.InnerInvolutionCentralizers.card_innerCentralizer (f β) ⟨w,hw.symm⟩
        (by intro he; have hh := (orderOf_injective f hf β).trans hβo; rw [he,orderOf_one] at hh; omega)
        (by rw [←map_pow]; have hh : β^2=1 := by simpa only [hβo] using pow_orderOf_eq_one β
            rw [hh,map_one])
    have hac : orderOf (⟨f α,hmem⟩ : C)=3 :=
      (Subgroup.orderOf_coe _).symm.trans ((orderOf_injective f hf α).trans hαo)
    have hd := _root_.orderOf_dvd_natCard (⟨f α,hmem⟩ : C)
    rw [hac,hbc] at hd
    norm_num at hd
  have hxo : orderOf x=3 := orderOf_eq_prime hx3 (fun he => hxB (he ▸ B.one_mem))
  have hfix : W ≤ centralizer ({x} : Set (Nonabelian.Setup.Hstar H)) := by
    rintro _ ⟨b,⟨n,hn,rfl⟩,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hb : α (e.symm n)=e.symm n := by
      apply e.injective
      exact (hNfix n hn).trans (e.apply_symm_apply n).symm
    have hh := a.conjugation (j p) (e.symm n)
    change (α (e.symm n) : Nonabelian.Setup.Hstar H) = x*(e.symm n).val*x⁻¹ at hh
    rw [hb] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hl := IsElementaryAbelian.primeRank_ge_of_fixed_join W x hxo
    (fun hx => hxB (map_subtype_le _ hx)) hfix hWc
  have hu := S.original_star_three_rank D hZ z hz hH
  change primeRank 3 (Nonabelian.Setup.Hstar H) ≤ 2 at hu
  omega

/-- Every nonsimple original selected component is a cubic A₇ or M₂₂ cover. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_alternating_mathieu_cover
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
        (Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
        Chapter1.Section02.LocalModels.IsM22Cover B)) := by
  rcases S.original_selectedComponent_simple_or_smallLinear_cover D hZ z hz hTV hTz
    hbound hns hH hn c a with hs|⟨hc,hl|hr⟩
  · exact Or.inl hs
  · exact (S.original_selectedComponent_not_linearFourCover D hZ z hz hTV hTz hbound hH hn c a hl).elim
  · exact Or.inr ⟨hc,hr⟩

/-- The original selected component retains condition (*), both rank branches
and all preceding exclusions; only cubic A₇ and M₂₂ remain among its covers. -/
theorem SourceHypothesis.original_selectedComponent_reduced_cover_cases
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
           (Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
           Chapter1.Section02.LocalModels.IsM22Cover B))) ∧
      (∀ n : ℕ, 2 ≤ n → ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 3 (2^n)) ∧
      ¬ Chapter1.Section02.LocalModels.IsSL (Nonabelian.Setup.star H c.K) 3 4 := by
  obtain ⟨c,a,hc,hr,hAlt,h6,h7,_,hlin,_⟩ :=
    S.original_selectedComponent_reduced_linear_cases D hZ z hz hTV hTz hbound hns hH hn
  exact ⟨c,a,hc,hr,hAlt,h6,h7,
    S.original_selectedComponent_simple_or_alternating_mathieu_cover D hZ z hz hTV hTz
      hbound hns hH hn c a,hlin,
    S.original_selectedComponent_not_linearFourCover D hZ z hz hTV hTz hbound hH hn c a⟩

end CFSG.Quasithin.Chapter12.Section06
