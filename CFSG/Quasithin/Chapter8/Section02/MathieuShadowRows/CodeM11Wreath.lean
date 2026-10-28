module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.WreathXi
public import Theory.GroupTheory.SolvableSemidihedralInvolution
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.Mathieu.M11.Properties.SylowOvergroups

/-!
# The original wreath residual excludes an M₁₁ component

A full-Sylow overgroup in M₁₁ with nontrivial two-core centralizes the
characteristic involution supplied by its semidihedral Sylow. That
centralizer has order 48. Thus an overgroup with order divisible by nine
has trivial two-core. A group with quotient S₃ wr C₂ modulo its two-core
cannot map onto such an overgroup: the overgroup's Sylow has order sixteen,
whereas the wreath quotient has order 72.

For a normal C-component with full two-core quotient M₁₁, pass through the
ambient two-core and use the native inner-automorphism theorem to project
onto M₁₁. The original two-residual, when contained in that component,
retains its elementary-nine quotient through the two-group kernel. This
supplies the factor of nine and gives the contradiction. The original
component, Sylow and residual maps are retained in the construction.
The Chapter12 consumer is M22CodeHeldReduction.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, refs/quasithin.pdf;
the semidihedral Sylow and involution-centralizer calculations are the
native M₁₁ facts cited by the imported model modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Sporadic.Mathieu

private theorem m11_sylow_presentation (S : Sylow 2 M11) :
    ∃ a b : S, orderOf a = 8 ∧ orderOf b = 2 ∧
      b * a * b⁻¹ = a ^ 3 ∧ closure ({a,b} : Set S) = ⊤ := by
  obtain ⟨P,a,b,ha,hb,hc,hg⟩ := m11_exists_semidihedral_sylow
  let e := P.equiv S
  refine ⟨e a,e b,(e.orderOf_eq a).trans ha,(e.orderOf_eq b).trans hb,?_,?_⟩
  · rw [←map_inv,←map_mul,←map_mul,hc,map_pow]
  · have hh := congrArg (Subgroup.map e.toMonoidHom) hg
    rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
      map_top_of_surjective e.toMonoidHom e.surjective] at hh
    exact hh

private theorem m11_involution_centralizer_card (z : M11) (hz : orderOf z = 2) :
    Nat.card (centralizer ({z} : Set M11)) = 48 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (m11_involution_isConj_generatorA z hz)
  let f : M11 ≃* M11 := MulAut.conj g
  have hf : f z = m11GeneratorAInM11 := hg
  have hc : Nat.card (centralizer ({z} : Set M11)) = Nat.card m11InvolutionCentralizer := by
    apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
    intro a
    change a ∈ centralizer ({z} : Set M11) ↔
      f a ∈ centralizer ({m11GeneratorAInM11} : Set M11)
    simp only [mem_centralizer_singleton_iff,←hf,←map_mul,f.injective.eq_iff]
  exact hc.trans m11_involutionCentralizer_card

/-- A full-Sylow overgroup in M₁₁ with a factor of nine has trivial two-core. -/
theorem m11_sylow_overgroup_twoCore_eq_bot
    (S : Sylow 2 M11) (A : Subgroup M11)
    (hSA : (S : Subgroup M11) ≤ A) (h9 : 9 ∣ Nat.card A) : pCore 2 A = ⊥ := by
  by_contra hn
  obtain ⟨a,b,ha,hb,hc,hg⟩ := m11_sylow_presentation S
  let P := S.subtype hSA
  let e : S ≃* P := (subgroupOfEquivOfLe hSA).symm
  have hgen : closure ({e a,e b} : Set P) = ⊤ := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) hg
    rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
      map_top_of_surjective e.toMonoidHom e.surjective] at hh
    exact hh
  have hrel : e b * e a * (e b)⁻¹ = (e a)^3 := by
    rw [←map_inv,←map_mul,←map_mul,hc,map_pow]
  let z : A := ((e a : P) : A)^4
  have hz : orderOf z = 2 := by
    rw [orderOf_pow,Subgroup.orderOf_coe,e.orderOf_eq,ha]
    decide
  let : (zpowers z).Characteristic :=
    Semidihedral.characteristic_zpowers_fourth_of_twoCore_ne_bot P (e a) (e b)
      ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb) hrel hgen hn
  have hAz : A ≤ centralizer ({(z : M11)} : Set M11) := by
    intro x hx
    let y : A := ⟨x,hx⟩
    have hh : y ∈ normalizer (zpowers z : Set A) := by rw [normalizer_eq_top]; exact mem_top _
    rw [normalizer_zpowers_eq_centralizer_of_order_two z hz] at hh
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_centralizer_singleton_iff.mp hh))
  have hd := h9.trans (card_dvd_of_le hAz)
  rw [m11_involution_centralizer_card z (by rwa [Subgroup.orderOf_coe])] at hd
  norm_num at hd

/-- A group with wreath quotient cannot have an M₁₁ image containing a full Sylow and a three-plane. -/
theorem no_m11_image_of_wreath_quotient
    {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor)
    (f : H →* M11) (S : Sylow 2 M11)
    (hS : (S : Subgroup M11) ≤ f.range) (h9 : 9 ∣ Nat.card f.range) : False := by
  have hz := m11_sylow_overgroup_twoCore_eq_bot S f.range hS h9
  have hk : pCore 2 H ≤ f.rangeRestrict.ker := by
    have hh : (pCore 2 H).map f.rangeRestrict ≤ pCore 2 f.range :=
      le_sSup ⟨Normal.map inferInstance _ f.rangeRestrict_surjective,pCore_isPGroup.map _⟩
    rwa [hz,map_le_iff_le_comap,MonoidHom.comap_bot] at hh
  let q := QuotientGroup.lift (pCore 2 H) f.rangeRestrict hk
  have hq : Function.Surjective q := QuotientGroup.lift_surjective_of_surjective _ _
    f.rangeRestrict_surjective _
  have hd := (card_dvd_of_le hS).trans (card_dvd_of_surjective q hq)
  have hcard : Nat.card WreathTwoResidual.Actor = 72 := by
    rw [RegularWreathProduct.card]
    have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Nat.card_congr SLTwoPermThree.sl2Two_equiv_perm_three.some.toEquiv]
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    rw [hc]
    norm_num [Nat.card_eq_fintype_card]
  have hSCard : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity,m11_order]
    decide +kernel
  rw [hSCard,Nat.card_congr e.toEquiv,hcard] at hd
  norm_num at hd

/-- The full original wreath quotient is incompatible with its two-residual lying in a normal C-component whose full two-core quotient is M₁₁. -/
theorem no_wreath_residual_in_normal_m11_component
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (H K : Subgroup G) [K.Normal]
    (hTH : (T : Subgroup G) ≤ H) (hK : K.IsCComponent)
    (hXK : (pResidual 2 H).map H.subtype ≤ K)
    (eK : (K ⧸ pCore 2 K) ≃* M11)
    (eH : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) : False := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let Kq := K.map π
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let : Kq.Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  let a : Kq ≃* M11 := (cComponentTwoCoreQuotientEquiv hK).symm.trans eK
  obtain ⟨q,hq,hqK⟩ := exists_normal_m11_projection Kq a
  let f := q.comp π
  have hf : Function.Surjective f := hq.comp (QuotientGroup.mk'_surjective _)
  have hfK (k : K) : f k = eK (QuotientGroup.mk' (pCore 2 K) k) := by
    change q ((π.subgroupMap K k) : G ⧸ pCore 2 G) = _
    rw [hqK]
    exact congrArg eK ((cComponentTwoCoreQuotientEquiv hK).symm_apply_apply
      (QuotientGroup.mk' (pCore 2 K) k))
  let r := f.comp H.subtype
  let S := T.mapSurjective hf
  have hS : (S : Subgroup M11) ≤ r.range := by
    rintro _ ⟨t,ht,rfl⟩
    exact ⟨⟨t,hTH ht⟩,rfl⟩
  let X := pResidual 2 H
  let j : X →* K := {
    toFun x := ⟨(x : H),hXK (mem_map_of_mem H.subtype x.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun k : K => (k : G)) he))
  let u := r.comp X.subtype
  have hu : IsPGroup 2 u.rangeRestrict.ker := by
    have hk : u.ker = (pCore 2 K).comap j := by
      ext x
      change f (x : H) = 1 ↔ j x ∈ pCore 2 K
      rw [show f (x : H) = eK (QuotientGroup.mk' (pCore 2 K) (j x)) from hfK (j x),
        eK.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff _
    rw [MonoidHom.ker_rangeRestrict,hk]
    exact pCore_isPGroup.comap_of_injective j hj
  let b := u.rangeRestrict.pCoreQuotientEquiv u.rangeRestrict_surjective hu
  have hc : Nat.card (X ⧸ pCore 2 X) = 9 := by
    rw [Nat.card_congr (wreath_residual_core_equiv eH).toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hd : 9 ∣ Nat.card u.range := by
    rw [←hc,Nat.card_congr b.toEquiv]
    exact card_quotient_dvd_card _
  have hr : u.range ≤ r.range := by rintro _ ⟨x,rfl⟩; exact ⟨x,rfl⟩
  exact no_m11_image_of_wreath_quotient eH r S hS (hd.trans (card_dvd_of_le hr))

end CFSG.Quasithin.Chapter8.MathieuShadowRows
