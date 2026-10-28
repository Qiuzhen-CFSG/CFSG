module
public import CFSG.Quasithin.ChapterI.Section03.ComponentQuotients
public import CFSG.Quasithin.ChapterI.Section03.GeneralTwoOrbit.Source

/-!
# The original involution two-component alternative I.3.2

The unconditional GLS5.22 orbit theorem gives the odd-E normal closure as
one orbit under the actual involution. That orbit is a single component or
the join of two transposed components. In the latter case, GLS5.22(iv)
preserves the local component under the literal quotient by O_{2',2}.
The checked product coordinates identify its fixed subgroup with the full
simple diagonal, giving the source quotient equivalence.

All earlier balance premises are discharged. No prescribed component orbit,
quotient identification, B₂ property or model list is assumed.
Source: Aschbacher–Smith I.3.2, printed p.415; GLS II B.5.22(i)–(iv).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.InvolutionSource
variable {G : Type*} [Group G] [Finite G]

private theorem cyclic_two_cases {A : Type*} [Group A] [Finite A] (a : A) (ha : orderOf a = 2)
    (b : zpowers a) : b = 1 ∨ b = ⟨a, mem_zpowers a⟩ := by
  classical
  have hb := b.property
  rw [mem_zpowers_iff_mem_range_orderOf, ha] at hb
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hb
  have hn2 : n < 2 := Finset.mem_range.mp hn
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · left
    apply Subtype.ext
    change (b : A) = 1
    simpa only [pow_zero] using he.symm
  · right
    apply Subtype.ext
    simpa only [pow_one] using he.symm

/-- The literal fixed-subgroup quotient in I.3.2 preserves two-components. -/
theorem map_fixed_oddTwoCore_twoComponent (hG : twoComponentLayer G = ⊤)
    (σ : MulAut G) (hσ : orderOf σ = 2)
    (L : Subgroup σ.fixedSubgroup) (hL : L.IsTwoComponent) :
    (L.map (MulAut.oddTwoCoreFixedMap σ)).IsTwoComponent := by
  let A := zpowers σ
  let a : A := ⟨σ,mem_zpowers σ⟩
  have hA : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hσ,pow_one])
  have he : fixedPointSubgroup A G = σ.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup _ _).mpr (hx a)
    · intro hx b
      rcases cyclic_two_cases σ hσ b with rfl | rfl
      · exact one_smul A x
      · exact (MulAut.mem_fixedSubgroup _ _).mp hx
  let e : σ.fixedSubgroup ≃* fixedPointSubgroup A G := MulEquiv.subgroupCongr he.symm
  let N := oddTwoCore G
  have hN : IsInvariant A G N := isInvariant_of_characteristic N
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  have heq : fixedPointSubgroup A (G ⧸ N) = (MulAut.oddTwoCoreQuotientAut σ).fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup _ _).mpr (hx a)
    · intro hx b
      rcases cyclic_two_cases σ hσ b with rfl | rfl
      · exact one_smul A x
      · exact (MulAut.mem_fixedSubgroup _ _).mp hx
  let e' : fixedPointSubgroup A (G ⧸ N) ≃*
      (MulAut.oddTwoCoreQuotientAut σ).fixedSubgroup := MulEquiv.subgroupCongr heq
  have hp := GeneralTwoOrbit.map_fixed_twoComponent_oddTwoCore_quotient
    hG hA N hN le_rfl (hL.map_equiv e)
  have hmap : e'.toMonoidHom.comp ((FixedPoints.quotientMap N hN).comp e.toMonoidHom) =
      MulAut.oddTwoCoreFixedMap σ := by
    ext x
    rfl
  have hout := hp.map_equiv e'
  simpa only [map_map,MonoidHom.comp_assoc,hmap] using hout
end CFSG.Quasithin.ChapterI.InvolutionSource

namespace CFSG.Quasithin.ChapterI.InvolutionSource
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem componentOrbit_zpowers_two (J : Subgroup G) (t : G)
    (ht : orderOf t = 2) :
    componentOrbit J (zpowers t) = J ⊔ J.map (MulAut.conj t).toMonoidHom := by
  apply le_antisymm
  · apply iSup_le
    intro a
    rcases cyclic_two_cases t ht a with rfl | rfl
    · simp only [Subgroup.coe_one,map_one]
      change J.map (MonoidHom.id G) ≤ _
      rw [Subgroup.map_id]
      exact le_sup_left
    · exact le_sup_right
  · apply sup_le (le_componentOrbit _ _)
    exact le_iSup (fun a : zpowers t => J.map (MulAut.conj (a : G)).toMonoidHom)
      ⟨t,mem_zpowers t⟩

omit [Finite G] in
private theorem twoLayer_pair_top {J J' : Subgroup G}
    (hJ : J.IsTwoComponent) (hJ' : J'.IsTwoComponent) :
    twoComponentLayer (J ⊔ J' : Subgroup G) = ⊤ := by
  apply top_unique
  have he : J.subgroupOf (J ⊔ J') ⊔ J'.subgroupOf (J ⊔ J') = ⊤ := by
    apply map_injective (J ⊔ J').subtype_injective
    simp only [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
  rw [←he]
  exact sup_le (hJ.subgroupOf le_sup_left).le_twoComponentLayer
    (hJ'.subgroupOf le_sup_right).le_twoComponentLayer

private noncomputable def fixedJoinEquiv (t : G) (X : Subgroup G)
    (σ : MulAut X) (hσx : ∀ x : X, (σ x : G) = t * (x : G) * t⁻¹) :
    (X ⊓ centralizer (zpowers t : Set G) : Subgroup G) ≃* σ.fixedSubgroup where
  toFun x := ⟨⟨x,x.property.1⟩, by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    rw [hσx]
    have hc := mem_centralizer_iff.mp x.property.2 t (mem_zpowers t)
    rw [hc,mul_inv_cancel_right]⟩
  invFun x := ⟨x.val.val, x.val.property, by
    change (x.val : G) ∈ centralizer (zpowers t : Set G)
    rw [zpowers_eq_closure,centralizer_closure]
    apply mem_centralizer_singleton_iff.mpr
    have hc := congrArg (fun y : X => (y : G))
      ((MulAut.mem_fixedSubgroup σ x.val).mp x.property)
    rw [hσx] at hc
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- I.3.2, with the literal odd-E orbit and both actual intrinsic core quotients.
All GLS5.22 premises are discharged; no K-group restriction is required. -/
theorem involution_twoComponent_alternatives (t : G) (ht : orderOf t = 2)
    (L : Subgroup (centralizer (zpowers t : Set G))) (hL : L.IsTwoComponent) :
    let D := L.map (centralizer (zpowers t : Set G)).subtype
    let K := componentOrbit D (oddELayer G)
    (K.IsTwoComponent ∧ K.map (MulAut.conj t).toMonoidHom = K) ∨
      ∃ J : Subgroup G, J.IsTwoComponent ∧ J ≠ J.map (MulAut.conj t).toMonoidHom ∧
        K = J ⊔ J.map (MulAut.conj t).toMonoidHom ∧
        Nonempty ((J ⧸ oddTwoCore J) ≃* (L ⧸ oddTwoCore L)) := by
  let C := centralizer (zpowers t : Set G)
  let D := L.map C.subtype
  let K := componentOrbit D (oddELayer G)
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ht,pow_one])
  obtain ⟨J,hJ,hDX,_,_,hK,_,_,hfixed⟩ :=
    GeneralTwoOrbit.Source.internal_orbit_and_closures (zpowers t) hp L hL
  let J' := J.map (MulAut.conj t).toMonoidHom
  have horbit := componentOrbit_zpowers_two J t ht
  have hKX : K = J ⊔ J' := hK.trans horbit
  by_cases he : J = J'
  · left
    have hKJ : K = J := by rw [hKX,←he,sup_idem]
    change K.IsTwoComponent ∧ K.map (MulAut.conj t).toMonoidHom = K
    rw [hKJ]
    exact ⟨hJ,he.symm⟩
  · right
    refine ⟨J,hJ,he,hKX,?_⟩
    have htt : t*t=1 := by
      have hh : t^2=1 := by rw [←ht];exact pow_orderOf_eq_one t
      simpa only [pow_two] using hh
    have hinv : Function.Involutive (MulAut.conj t) := by
      intro g
      change t*(t*g*t⁻¹)*t⁻¹=g
      calc
        _=(t*t)*g*(t*t)⁻¹ := by group
        _=g := by rw [htt];simp
    obtain ⟨σ,hσ,hJJ',hJ'J,hσx⟩ := MulAut.exists_involutive_swap_on_join
      (MulAut.conj t) hinv (A:=J) rfl
    let X := J ⊔ J'
    have hσorder : orderOf σ = 2 := by
      apply orderOf_eq_prime
      · apply MulEquiv.ext
        intro x
        change σ (σ x) = x
        exact hσ x
      · intro hσone
        have heq : J.subgroupOf X = J'.subgroupOf X := by
          rw [hσone] at hJJ'
          change (J.subgroupOf X).map (MonoidHom.id X) = J'.subgroupOf X at hJJ'
          rwa [Subgroup.map_id] at hJJ'
        apply he
        have hh := congrArg (map X.subtype) heq
        simpa only [map_subgroupOf_eq_of_le (show J ≤ X from le_sup_left),
          map_subgroupOf_eq_of_le (show J' ≤ X from le_sup_right)] using hh
    have hDX' : D ≤ X := hDX.trans horbit.le
    have hDM : D ≤ X ⊓ C := le_inf hDX' (map_subtype_le _)
    have hfixed' : (D.subgroupOf (X ⊓ C)).IsTwoComponent := by
      change (D.subgroupOf (componentOrbit J (zpowers t) ⊓ C)).IsTwoComponent at hfixed
      rw [horbit] at hfixed
      exact hfixed
    let e := fixedJoinEquiv t X σ hσx
    let L' := (D.subgroupOf (X ⊓ C)).map e.toMonoidHom
    have hL' : L'.IsTwoComponent := hfixed'.map_equiv e
    have hquot := map_fixed_oddTwoCore_twoComponent
      (twoLayer_pair_top hJ (hJ.map_equiv (MulAut.conj t))) σ hσorder L' hL'
    let eL : L ≃* L' :=
      (equivMapOfInjective L C.subtype C.subtype_injective).trans
        ((subgroupOfEquivOfLe hDM).symm.trans (e.subgroupMap _))
    let eQ := QuotientGroup.congr _ _ eL (oddTwoCore_map_equiv eL)
    exact ⟨(ComponentQuotients.local_quotient_equiv_factor hJ
      (hJ.map_equiv (MulAut.conj t)) he σ hσ hJJ' hJ'J hL' hquot).symm.trans eQ.symm⟩
end CFSG.Quasithin.ChapterI.InvolutionSource

namespace CFSG.Quasithin.ChapterI
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- I.3.2 on the original involution centralizer and literal odd-E orbit. -/
theorem lemma_I_3_2 (t : G) (ht : orderOf t = 2)
    (L : Subgroup (centralizer ({t} : Set G))) (hL : L.IsTwoComponent) :
    let D := L.map (centralizer ({t} : Set G)).subtype
    let K := componentOrbit D (oddELayer G)
    (K.IsTwoComponent ∧ K.map (MulAut.conj t).toMonoidHom = K) ∨
      ∃ J : Subgroup G, J.IsTwoComponent ∧ J ≠ J.map (MulAut.conj t).toMonoidHom ∧
        K = J ⊔ J.map (MulAut.conj t).toMonoidHom ∧
        Nonempty ((J ⧸ oddTwoCore J) ≃* (L ⧸ oddTwoCore L)) := by
  have hc : centralizer (zpowers t : Set G) = centralizer ({t} : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
  have h := InvolutionSource.involution_twoComponent_alternatives t ht
  rw [hc] at h
  exact h L hL
end CFSG.Quasithin.ChapterI
