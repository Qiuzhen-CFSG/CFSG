module
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.Group

/-!
# Cubic SL₂(3) factors cannot normalize elementary eights

Let L be a normal SL₂(3) subgroup of the centralizer H of an involution z.
If a cubic x in L has quaternion-eight Sylow two-subgroups in its ambient
centralizer, x cannot normalize an elementary eight E.

An order-three action on the seven nonidentity points of E fixes an
involution v. Sylow conjugacy inside C(x) carries v to z while fixing x,
so we may place E inside H. For each u in E, the commutator of x and u
belongs to E intersect L. Square-one elements of SL₂(3) are central, so
the resulting action of x on E has square one. Its cube is also one;
hence x centralizes E. This contradicts the quaternion Sylow subgroup of
C(x), whose elementary two-subgroups have order at most two.

This is a direct local consequence of the actual marked configuration
(G1)–(G2) preceding Aschbacher–Smith I.4.5, printed p.417. Its consumer
`G2Recognition.MarkedCubic` separates the cubic elements of the marked
M from the two factor classes. It does not exclude the exceptional
strongly-three-embedded branch or assert ambient recognition.
-/

@[expose] public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory

private abbrev BT := QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
  Multiplicative (ZMod 3)
private instance : DecidableEq BT := SemidirectProduct.equivProd.injective.decidableEq
private instance : Fintype BT := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
private theorem square_one_commutes : ∀ d x : BT, d^2=1 → d*x=x*d := by decide +kernel

private theorem cubic_centralizes_elementary_normalized
    {K : Type*} [Group K] (L : Subgroup K) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (E : Subgroup K) [IsElementaryAbelian 2 E]
    (x : L) (hx : x^3=1) (hn : (x:K) ∈ normalizer (E : Set K)) :
    (x:K) ∈ centralizer (E : Set K) := by
  intro u hu
  let a : MulAut K := MulAut.conj (x:K)
  let d : K := a u * u⁻¹
  have hau : a u ∈ E := (mem_normalizer_iff.mp hn u).mp hu
  have hdE : d ∈ E := E.mul_mem hau (E.inv_mem hu)
  have hdL : d ∈ L := by
    change (x:K)*u*(x:K)⁻¹*u⁻¹ ∈ L
    have hh := L.mul_mem x.property
      ((inferInstance : L.Normal).conj_mem (x:K)⁻¹ (L.inv_mem x.property) u)
    simpa only [mul_assoc] using hh
  have hd2 : d*d=1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) d hdE
  have hdx : d*(x:K)=(x:K)*d := by
    let f := e.trans GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.symm
    have hh := square_one_commutes (f ⟨d,hdL⟩) (f x) (by
      rw [←map_pow,show (⟨d,hdL⟩:L)^2=1 from Subtype.ext (by change d^2=1; simpa only [pow_two] using hd2),map_one])
    exact congrArg Subtype.val (f.injective (by simpa only [map_mul] using hh : f (⟨d,hdL⟩*x)=f (x*⟨d,hdL⟩)))
  have had : a d=d := by
    change (x:K)*d*(x:K)⁻¹=d
    rw [←hdx,mul_inv_cancel_right]
  have hau' : a u=d*u := by dsimp only [d]; group
  have ha2 : a (a u)=u := by
    rw [hau',map_mul,had,hau',←mul_assoc,hd2,one_mul]
  have ha3 : a (a (a u))=u := by
    change (x:K)*((x:K)*((x:K)*u*(x:K)⁻¹)*(x:K)⁻¹)*(x:K)⁻¹=u
    calc
      _ = (x:K)^3*u*((x:K)^3)⁻¹ := by simp only [pow_succ,pow_zero]; group
      _ = u := by rw [show (x:K)^3=1 from congrArg Subtype.val hx,one_mul,inv_one,mul_one]
  rw [ha2] at ha3
  exact (mul_inv_eq_iff_eq_mul.mp ha3).symm


private theorem quaternion_square_one_eq {K : Type*} [Group K]
    (e : K ≃* QuaternionGroup 2) (a b : K) (ha : orderOf a=2) (hb : orderOf b=2) : a=b := by
  apply e.injective
  have ha1 : e a≠1 := fun h => by
    have hh := e.orderOf_eq a
    rw [h,orderOf_one,ha] at hh
    omega
  have hb1 : e b≠1 := fun h => by
    have hh := e.orderOf_eq b
    rw [h,orderOf_one,hb] at hh
    omega
  exact (by decide : ∀ a b : QuaternionGroup 2,
    a≠1 → a^2=1 → b≠1 → b^2=1 → a=b) _ _ ha1
    (by simpa only [e.orderOf_eq,ha] using pow_orderOf_eq_one (e a)) hb1
    (by simpa only [e.orderOf_eq,hb] using pow_orderOf_eq_one (e b))

private theorem quaternion_sylow_elementary_bound {K : Type*} [Group K] [Finite K]
    (P : Sylow 2 K) (e : P ≃* QuaternionGroup 2)
    (E : Subgroup K) [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  obtain ⟨Q,hQ⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let f : E →* QuaternionGroup 2 := e.toMonoidHom.comp
    ((Q.equiv P).toMonoidHom.comp (inclusion hQ))
  have hf : Function.Injective f := e.injective.comp
    ((Q.equiv P).injective.comp (inclusion_injective hQ))
  let j : E → {q : QuaternionGroup 2 // q^2=1} := fun a => ⟨f a,by
    rw [←map_pow,show a^2=1 from Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) a,map_one]⟩
  have hj : Function.Injective j := fun a b h => hf (congrArg Subtype.val h)
  have hh := Nat.card_le_card_of_injective j hj
  have hc : Nat.card {q : QuaternionGroup 2 // q^2=1}=2 := by
    rw [Nat.card_eq_fintype_card]; decide
  rwa [hc] at hh

private theorem quaternion_sylow_involutions_conjugate {K : Type*} [Group K] [Finite K]
    (P : Sylow 2 K) (e : P ≃* QuaternionGroup 2)
    (a b : K) (ha : orderOf a=2) (hb : orderOf b=2) : IsConj a b := by
  have hpa : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers,ha,pow_one])
  have hpb : IsPGroup 2 (zpowers b) := IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers,hb,pow_one])
  obtain ⟨A,hA⟩ := hpa.exists_le_sylow
  obtain ⟨B,hB⟩ := hpb.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq K A B
  have hag : MulAut.conj g a ∈ (B : Subgroup K) := by
    rw [←hg,Sylow.coe_subgroup_smul]
    exact mem_map_of_mem _ (hA (mem_zpowers a))
  have hbb : b ∈ (B : Subgroup K) := hB (mem_zpowers b)
  have heq := quaternion_square_one_eq ((B.equiv P).trans e)
    (⟨_,hag⟩ : B) (⟨_,hbb⟩ : B)
    ((orderOf_coe _).symm.trans (((MulAut.conj g).orderOf_eq a).trans ha))
    ((orderOf_coe _).symm.trans hb)
  exact isConj_iff.mpr ⟨g,congrArg Subtype.val heq⟩

private theorem cubic_fixed_involution_of_eight {K : Type*} [Group K] [Finite K]
    (E : Subgroup K) [IsElementaryAbelian 2 E] (hE : Nat.card E=8)
    (x : K) (hx : orderOf x=3) (hn : x ∈ normalizer (E : Set K)) :
    ∃ v ∈ E, orderOf v=2 ∧ x*v=v*x := by
  let ρ : zpowers x →* MulAut E := E.normalizerMonoidHom.comp
    (inclusion (zpowers_le.mpr hn))
  let : MulAction (zpowers x) E := MulAction.compHom E ρ
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers,hx,pow_one])
  have hmod := hp.card_modEq_card_fixedPoints E
  have hex : ∃ v : E, v ∈ MulAction.fixedPoints (zpowers x) E ∧ v≠1 := by
    by_contra! h
    have heq : MulAction.fixedPoints (zpowers x) E = {1} := by
      ext v
      constructor
      · exact fun hv => h v hv
      · intro hv
        have hv1 : v=1 := hv
        subst v
        intro a
        exact map_one (ρ a)
    rw [heq,hE,Nat.card_unique] at hmod
    norm_num [Nat.ModEq] at hmod
  obtain ⟨v,hv,hvne⟩ := hex
  have he := congrArg Subtype.val (hv ⟨x,mem_zpowers x⟩)
  refine ⟨v,v.property,orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (v:K) v.property)
    (fun he => hvne (Subtype.ext he)),?_⟩
  exact mul_inv_eq_iff_eq_mul.mp he


/-- A cubic in a normal SL₂(3) factor of an involution centralizer cannot
normalize an elementary eight when its own centralizer has quaternion Sylow
subgroups. All factors and centralizers use their literal ambient embeddings. -/
theorem no_elementary_eight_normalized_by_sl23_cubic
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (z : H) (hz : orderOf z=2) (hH : H=centralizer ({(z:G)} : Set G))
    (x : L) (hx : orderOf x=3)
    (P : Sylow 2 (centralizer ({((x:H):G)} : Set G)))
    (eP : P ≃* QuaternionGroup 2)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E=8) :
    ((x:H):G) ∉ normalizer (E : Set G) := by
  intro hn
  let C := centralizer ({((x:H):G)} : Set G)
  obtain ⟨v,hv,hv2,hxv⟩ := cubic_fixed_involution_of_eight E hE ((x:H):G)
    ((orderOf_coe (x:H)).trans ((orderOf_coe x).trans hx)) hn
  have hvC : v∈C := mem_centralizer_singleton_iff.mpr hxv.symm
  have hzC : (z:G)∈C := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hH ▸ x.val.property)).symm
  obtain ⟨g,hg⟩ := isConj_iff.mp (quaternion_sylow_involutions_conjugate P eP
    (⟨v,hvC⟩ : C) (⟨z,hzC⟩ : C)
    ((orderOf_coe _).symm.trans hv2)
    ((orderOf_coe _).symm.trans ((orderOf_coe z).trans hz)))
  let a : MulAut G := MulAut.conj (g:G)
  let F : Subgroup G := E.map a.toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map a.toMonoidHom
  have hzF : (z:G) ∈ F := by
    have he : a v=(z:G) := congrArg Subtype.val hg
    exact he ▸ mem_map_of_mem a.toMonoidHom hv
  have hFH : F ≤ H := by
    rw [hH]
    intro f hf
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨f,hf⟩ : F) ⟨z,hzF⟩))
  have hax : a ((x:H):G)=((x:H):G) :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property)
  have hxnF : ((x:H):G) ∈ normalizer (F : Set G) := by
    rw [←map_equiv_normalizer_eq E a]
    exact hax ▸ mem_map_of_mem a.toMonoidHom hn
  let F' := F.subgroupOf H
  let : IsElementaryAbelian 2 F' := IsElementaryAbelian.subgroupOf hFH
  have hxnF' : (x:H) ∈ normalizer (F' : Set H) :=
    le_normalizer_comap H.subtype hxnF
  have hxc := cubic_centralizes_elementary_normalized L e F' x
    (hx ▸ pow_orderOf_eq_one x) hxnF'
  have hFC : F ≤ C := by
    intro f hf
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hxc ⟨f,hFH hf⟩ hf))
  let : IsElementaryAbelian 2 (F.subgroupOf C) := IsElementaryAbelian.subgroupOf hFC
  have hb := quaternion_sylow_elementary_bound P eP (F.subgroupOf C)
  rw [Nat.card_congr (subgroupOfEquivOfLe hFC).toEquiv,
    card_map_of_injective a.injective,hE] at hb
  omega

end Theory.GroupTheory
