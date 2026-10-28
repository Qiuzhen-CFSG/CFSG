module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalResidualComponentAction
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneRadical
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.BinarySection
public import Theory.SpecificGroups.Janko1.Model.Certification
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.ThreeFree
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.GroupAction.InnerCentralizerRadical
public import Theory.SpecificGroups.PSL2.QuadraticFieldRadical
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import Theory.Representation.BinaryPrimeDisplacement

/-!
# Two terminal rows for the original selected component

The actual selected action excludes J1 through its involution centralizer
radical. For PSL2(25), the same radical excludes a field involution, while
an inner involution inverts an element of order thirteen. The literal
faithful section U_H/V₁ then requires at least six moved dimensions,
contradicting the original four-dimensional displacement bound.

Neither argument assumes the nonsingular-centralizer conclusion or a
natural-module classification. Source: Aschbacher--Smith, proof of 12.6.26,
printed pp.832--833, applied to the selected action in the proof of 12.6.34.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)

include hz hTV hTz hbound hH hn a in
/-- Condition (*) excludes J1 on the original selected component. -/
theorem SourceHypothesis.original_hs_selected_not_jankoOne :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* Janko1.Model) := by
  classical
  rintro ⟨e⟩
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : Group.IsPerfect Janko1.Model := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hzJ : center Janko1.Model = ⊥ := center_eq_bot_of_simple_perfect
  have hinner : Function.Surjective (MulAut.conj : B →* MulAut B) := by
    intro α
    obtain ⟨g,hg⟩ := Janko1.OuterCertificate.aut_inner (MulAut.congr e α)
    refine ⟨e.symm g,(MulAut.congr e).injective ?_⟩
    rw [MulAut.congr_conj,e.apply_symm_apply]
    exact hg
  have htop : a.action.range = ⊤ := by
    apply top_unique
    rw [←MonoidHom.range_eq_top.mpr hinner]
    change MulAut.innerSubgroup B ≤ a.action.range
    rw [←a.component_image]
    exact map_le_range _ _
  let j1Aut := MulEquiv.ofBijective (MulAut.conj : Janko1.Model →* MulAut Janko1.Model)
    ⟨Theory.GroupTheory.conj_injective_of_center_eq_bot hzJ,
      Janko1.OuterCertificate.aut_inner⟩
  let f : a.action.range ≃* Janko1.Model :=
    ((MulEquiv.subgroupCongr htop).trans topEquiv).trans
      ((MulAut.congr e).trans j1Aut.symm)
  let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
  have hU : Nat.card U = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (map_le_range _ _)).toEquiv]
    exact a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have ht' : orderOf (t : a.action.range) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hgen : zpowers (t : a.action.range) = U :=
    eq_of_le_of_card_ge (zpowers_le.mpr t.property) (by rw [Nat.card_zpowers,ht',hU])
  let C := centralizer (U : Set a.action.range)
  have hC : C = centralizer ({(t : a.action.range)} : Set a.action.range) := by
    change centralizer (U : Set a.action.range) = _
    calc
      centralizer (U : Set a.action.range) =
          centralizer (zpowers (t : a.action.range) : Set a.action.range) :=
        congrArg (fun A : Subgroup a.action.range => centralizer (A : Set a.action.range)) hgen.symm
      _ = _ := by rw [zpowers_eq_closure,centralizer_closure]
  let eC := (MulEquiv.subgroupCongr hC).trans
    (CentralizerSmallKernelTransport.centralizerEquiv f (t : a.action.range))
  let eR := (eC.subgroupMap (solvableRadical C)).trans
    (MulEquiv.subgroupCongr (map_solvableRadical_equiv eC))
  have hp := Janko1.InvolutionCentralizer.involution_radical_isTwoGroup
    (f t) ((f.orderOf_eq _).trans ht')
  have hd := S.original_action_centralizer_radical_three_dvd D hZ z hz hTV hTz
    hbound hH hn c a
  change 3 ∣ Nat.card (solvableRadical C) at hd
  rw [Nat.card_congr eR.toEquiv] at hd
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  rw [hk] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)


include hz hTV hTz hbound hH hn a in
private theorem model_fixed_radical_not_two
    (hzK : center (Nonabelian.Setup.star H c.K) = ⊥)
    {B : Type*} [Group B] [Finite B] (e : Nonabelian.Setup.star H c.K ≃* B)
    (ho : IsPGroup 2 (MulAut.Outer B))
    (b : MulAut (Nonabelian.Setup.star H c.K))
    (hb : b ∈ (V.subgroupOf c.localActor).map a.action) (hb2 : orderOf b = 2) :
    ¬ IsPGroup 2 (solvableRadical (MulAut.congr e b).fixedSubgroup) := by
  intro hf
  let K := Nonabelian.Setup.star H c.K
  let t : a.action.range := ⟨b,(map_le_range _ _) hb⟩
  let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
  have hU : Nat.card U = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (map_le_range _ _)).toEquiv]
    exact a.module_card
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t).symm.trans hb2
  have hgen : zpowers t = U :=
    eq_of_le_of_card_ge (zpowers_le.mpr hb) (by rw [Nat.card_zpowers,ht,hU])
  have hC : centralizer (U : Set a.action.range) = centralizer ({t} : Set a.action.range) := by
    rw [←hgen,zpowers_eq_closure,centralizer_closure]
  let j := MulAut.fixedSubgroupCongr e b
  let jR := (j.subgroupMap (solvableRadical b.fixedSubgroup)).trans
    (MulEquiv.subgroupCongr (map_solvableRadical_equiv j))
  have hfixed := hf.of_equiv jR.symm
  have hinner : MulAut.innerSubgroup K ≤ a.action.range := by
    rw [←a.component_image]
    exact map_le_range _ _
  have htwo := MulAut.centralizer_radical_isTwoGroup_of_fixed hzK
    (ho.of_equiv (MulAut.outerCongr e).symm) a.action.range hinner t hfixed
  have hd := S.original_action_centralizer_radical_three_dvd D hZ z hz hTV hTz
    hbound hH hn c a
  change 3 ∣ Nat.card (solvableRadical (centralizer (U : Set a.action.range))) at hd
  rw [hC] at hd
  obtain ⟨k,hk⟩ := htwo.exists_card_eq
  rw [hk] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)


private theorem model_inverts_thirteen {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 25)
    (t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (ht : orderOf t = 2) :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      orderOf x = 13 ∧ t * x * t⁻¹ = x⁻¹ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨S, w, _, hS, _, hwS, hw2, hwinv, _, _⟩ :=
    BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data
      (p := 5) (f := 2) (by simpa using hF)
  have hS13 : Nat.card S = 13 := by simpa [hF] using hS
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 13 (by rw [hS13])
  have hw1 : w ≠ 1 := fun hh => hwS (hh ▸ S.one_mem)
  have hw : orderOf w = 2 := orderOf_eq_prime (by simpa [pow_two] using hw2) hw1
  obtain ⟨c, hc⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj w t hw ht)
  refine ⟨c * (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * c⁻¹, ?_, ?_⟩
  · change orderOf (MulAut.conj c (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = 13
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
  · rw [← hc]
    calc
      _ = c * (w * (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * w⁻¹) * c⁻¹ := by group
      _ = c * (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)⁻¹ * c⁻¹ := by rw [hwinv x x.property]
      _ = _ := by group

private theorem thirteen_commutator_displacement {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) A W) (hσ : Function.Injective σ) (u x : A)
    (hc : orderOf (u*x*u⁻¹*x⁻¹) = 13)
    (hsmall : Module.finrank (ZMod 2) (σ u - LinearMap.id).range ≤ 4) : False := by
  have hlo : 12 ≤ fixedCodim σ (zpowers (u*x*u⁻¹*x⁻¹)) := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_thirteen] using
      prime_order_le_fixedCodim σ hσ (by decide : Nat.Prime 13) (by decide) _ hc
  have hup := fixedCodim_commutator_le_twice σ u x
  rw [←fixedCodim_zpowers_eq_displacement_rank σ u] at hsmall
  omega

include hz hTV hTz hbound hH hn a in
/-- The original faithful section and the selected action exclude PSL₂(25). -/
theorem SourceHypothesis.original_hs_selected_not_linearTwoTwentyFive :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 2 25 := by
  classical
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let B := Nonabelian.Setup.star H c.K
  have hzB : center B = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : e x ∈ center PSL(2,F) := (centerCongr e ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F] at hh
    exact (e.map_eq_one_iff).mp hh
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨b₀,hb₀⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  let b : MulAut B := b₀
  have hb : b ∈ U := b₀.property
  have hb2 : orderOf b = 2 := (Subgroup.orderOf_coe b₀).trans hb₀
  let α := MulAut.congr e b
  have hα : orderOf α = 2 := ((MulAut.congr e).orderOf_eq b).trans hb2
  obtain ⟨R,hR⟩ := S.original_action_module_fixes_component_sylow
    D hZ z hz hTV hTz hbound hH hn c a
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : ∀ x ∈ P, α x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e (b (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hR b hb x hx]
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩
  have hlarge : 3 < Nat.card F := by omega
  have hi : ∃ t, α = MulAut.conj t := by
    rcases Theory.PSL2.odd_sylow_fixed_involution_inner_or_field hodd hlarge P α hα hP
      with hi | ⟨σ,β,hσ,he⟩
    · exact hi
    · have hrad := Theory.PSL2.quadratic_field_involution_radical_bot
        (by decide : Nat.Prime 5) (by decide) (by decide) (by simpa using hF) σ hσ
      let j := MulAut.fixedSubgroupCongr β α
      let jR := (j.subgroupMap (solvableRadical α.fixedSubgroup)).trans
        (MulEquiv.subgroupCongr (map_solvableRadical_equiv j))
      have htwo : IsPGroup 2 (solvableRadical (MulAut.congr β α).fixedSubgroup) := by
        rw [he,hrad]
        exact IsPGroup.of_subsingleton 2 _
      exact (model_fixed_radical_not_two S D hZ z hz hTV hTz hbound hH hn c a
        hzB e (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
          (by decide : Nat.Prime 5) (by decide) (by decide : 2 ≤ 2) (by simpa using hF))
        b hb hb2 (htwo.of_equiv jR.symm)).elim
  obtain ⟨t,ht⟩ := hi
  have ht2 : orderOf t = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot F) t).symm.trans
      (ht ▸ hα)
  obtain ⟨y,hy,hinv⟩ := model_inverts_thirteen hF t ht2
  let x : B := e.symm y
  have hbx : b x = x⁻¹ := by
    apply e.injective
    have hh := congrArg (fun f : MulAut PSL(2,F) => f y) ht
    change e (b (e.symm y)) = t * y * t⁻¹ at hh
    simpa only [x,map_inv,e.apply_symm_apply] using hh.trans hinv
  obtain ⟨v,hv,hvb⟩ := hb
  let u : Nonabelian.Setup.Hstar H :=
    QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have hu : u ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
  have hinv' : u * x.val * u⁻¹ = x.val⁻¹ := by
    rw [←a.conjugation v x,hvb]
    exact congrArg Subtype.val hbx
  have hx : orderOf x.val = 13 :=
    (Subgroup.orderOf_coe x).trans ((e.symm.orderOf_eq y).trans hy)
  have hc : orderOf (u*x.val*u⁻¹*x.val⁻¹) = 13 := by
    rw [hinv',←mul_inv_rev,←pow_two,orderOf_inv]
    have ho : Odd (orderOf x.val) := by rw [hx]; decide
    rw [ho.coprime_two_right.orderOf_pow,hx]
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let := h.point_normal_in_UH
  let := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,_⟩ := h.faithful_point_quotient
  exact thirteen_commutator_displacement σ hσ u x.val hc
    (S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ κ u hu)

end CFSG.Quasithin.Chapter12.Section06
