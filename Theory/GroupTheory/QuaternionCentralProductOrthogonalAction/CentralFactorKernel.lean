module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.CentralFactor
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.Perm.Support

/-!
# The binary central-factor quotient kernel

For E=P×D with P a quaternion central product and |D|≤2, an automorphism
trivial on E/Z(E) fixes every square. A nontrivial square and the identity
are two fixed points in the center, which has at most four elements. Its
restriction to the center therefore squares to one. The square of the
automorphism then fixes both the center and the quotient, and squares to one
by the central displacement calculation. Thus the orthogonal kernel has
exponent dividing four.

A nontrivial action of a two-perfect group consequently has an orthogonal
image whose order is divisible by three. These are the intrinsic action
inputs to Aschbacher--Smith 2.4.29, printed p.545.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative

private theorem perm_square_of_two_fixed {A : Type*} [Finite A]
    (hc : Nat.card A ≤ 4) (f : Equiv.Perm A) (x y : A)
    (hxy : x ≠ y) (hx : f x = x) (hy : f y = y) : f ^ 2 = 1 := by
  classical
  let := Fintype.ofFinite A
  have hs : f.support ⊆ Finset.univ \ {x,y} := by
    intro z hz
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_singleton,not_or]
    exact ⟨fun h => Equiv.Perm.mem_support.mp hz (h ▸ hx),
      fun h => Equiv.Perm.mem_support.mp hz (h ▸ hy)⟩
  have hb := Finset.card_le_card hs
  have hp : ({x,y} : Finset A).card = 2 := by simp [hxy]
  rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,hp] at hb
  have hle : f.support.card ≤ 2 := by rw [Nat.card_eq_fintype_card] at hc; omega
  by_cases hf : f = 1
  · simp [hf]
  · have he := Equiv.Perm.two_le_card_support_of_ne_one hf
    obtain ⟨a,b,hab,rfl⟩ := Equiv.Perm.card_support_eq_two.mp (by omega : f.support.card = 2)
    ext z
    exact Equiv.swap_apply_self _ _ _

private theorem quotient_kernel_pow_four {G : Type*} [Group G] [Finite G]
    (hc : Nat.card (center G) ≤ 4) (hs : ∀ z : center G, z ^ 2 = 1)
    (x : G) (hx : x ^ 2 ≠ 1) (hxZ : x ^ 2 ∈ center G)
    (a : (quotientAut (center G)).ker) : a ^ 4 = 1 := by
  have hquot (y : G) : QuotientGroup.mk' (center G) y =
      QuotientGroup.mk' (center G) ((a : MulAut G) y) := by
    have h := DFunLike.congr_fun a.property (QuotientGroup.mk' (center G) y)
    simpa only [quotientAut_apply_mk,MulAut.one_apply] using h.symm
  have hsq (y : G) : (a : MulAut G) (y ^ 2) = y ^ 2 := by
    have hm := QuotientGroup.eq.mp (hquot y)
    have hcomm : Commute y (y⁻¹ * (a : MulAut G) y) := mem_center_iff.mp hm y
    have hh : (y⁻¹ * (a : MulAut G) y)^2=1 := congrArg Subtype.val (hs ⟨_,hm⟩)
    rw [map_pow]
    calc
      (a : MulAut G) y ^ 2 = (y*(y⁻¹ * (a : MulAut G) y))^2 := by simp
      _ = y^2 * (y⁻¹ * (a : MulAut G) y)^2 := hcomm.mul_pow 2
      _ = y^2 := by rw [hh,mul_one]
  let z : center G := ⟨x^2,hxZ⟩
  have hz : z ≠ 1 := fun h => hx (congrArg Subtype.val h)
  have hcenter : (centerCongr (a : MulAut G)).toEquiv ^ 2 = 1 :=
    perm_square_of_two_fixed hc _ 1 z (Ne.symm hz)
      (show (centerCongr (a : MulAut G)) 1 = 1 from (centerCongr (a : MulAut G)).map_one) (Subtype.ext (hsq x))
  have hfix (y : center G) : ((a : MulAut G)^2) y = y := by
    exact congrArg Subtype.val (Equiv.congr_fun hcenter y)
  let b : MulAut G := (a : MulAut G)^2
  have hbquot : quotientAut (center G) b = 1 := by
    change quotientAut (center G) ((a : MulAut G)^2) = 1
    rw [map_pow,show quotientAut (center G) (a : MulAut G) = 1 from a.property,one_pow]
  have hb (y : G) : b (b y) = y := by
    have h := DFunLike.congr_fun hbquot (QuotientGroup.mk' (center G) y)
    have h' : QuotientGroup.mk' (center G) y = QuotientGroup.mk' (center G) (b y) := by
      simpa only [quotientAut_apply_mk,MulAut.one_apply] using h.symm
    have hm : y⁻¹ * b y ∈ center G := QuotientGroup.eq.mp h'
    have hf : b (y⁻¹*b y) = y⁻¹*b y := hfix ⟨_,hm⟩
    have hs' : (y⁻¹*b y)^2=1 := congrArg Subtype.val (hs ⟨_,hm⟩)
    have he : b y = y*(y⁻¹*b y) := by simp
    calc
      b (b y) = b (y*(y⁻¹*b y)) := congrArg b he
      _ = (y*(y⁻¹*b y))*(y⁻¹*b y) := by rw [map_mul,hf,← he]
      _ = y := by rw [mul_assoc,←pow_two,hs',mul_one]
  apply Subtype.ext
  change (a : MulAut G)^4=1
  have he : b^2=1 := by ext y; exact hb y
  simpa only [b,←pow_mul] using he

namespace Subgroup.QuaternionCentralProductData
variable {P D E : Type*} [Group P] [Finite P] [Group D] [Finite D]
  [IsElementaryAbelian 2 D] [Group E] (d : QuaternionCentralProductData P)
  (e : E ≃* P × D)

omit [Finite P] [Finite D] in
private theorem center_first (z : center E) : (e z).1 ∈ center P := by
  have h : (z:E) ∈ (centralFactorProjection e).ker := by rw [centralFactorProjection_ker]; exact z.property
  exact (QuotientGroup.eq_one_iff _).mp h

include d e in
private theorem center_bound (hD : Nat.card D ≤ 2) : Nat.card (center E) ≤ 4 := by
  let f : center E → center P × D := fun z => (⟨(e z).1,center_first e z⟩,(e z).2)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z : center P × D => ((z.1:P),z.2)) h
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,d.center_card] at hh
  omega

omit [Finite D] in
include d e in
private theorem center_pow_two (z : center E) : z ^ 2 = 1 := by
  apply Subtype.ext
  apply e.injective
  change e ((z:E)^2) = e 1
  rw [map_pow,map_one]
  apply Prod.ext
  · exact congrArg Subtype.val (d.center_square ⟨_,center_first e z⟩)
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 D) _

omit [Finite D] in
include d e in
private theorem square_center (x : E) : x^2 ∈ center E := by
  rw [←centralFactorProjection_ker e]
  change QuotientGroup.mk' (center P) (e (x^2)).1 = 1
  rw [map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (d.square_mem_center (e x).1)

omit [Finite P] [Finite D] in
include d e in
private theorem exists_nonsingular_square : ∃x : E, x^2≠1 := by
  let l := d.left_model.some
  let p : d.left := l.symm (QuaternionGroup.a 1)
  have hp : (p:P)^2≠1 := by
    intro h
    have hh : p^2=1 := Subtype.ext h
    have ht := congrArg l hh
    have he : (QuaternionGroup.a (1 : ZMod 4) : QuaternionGroup 2)^2≠1 := by decide
    exact he (by simpa only [map_pow,map_one,l.apply_symm_apply,p] using ht)
  refine ⟨e.symm ((p:P),1),fun h => hp ?_⟩
  have hh := congrArg (fun y => (e y).1) h
  simpa only [map_pow,map_one,e.apply_symm_apply,Prod.pow_mk,Prod.fst_one] using hh

/-- With a central factor of order at most two, the intrinsic quotient kernel
has exponent dividing four. -/
theorem centralFactorWreathAction_kernel_pow_four (hD : Nat.card D ≤ 2)
    (a : (d.centralFactorWreathAction e).ker) : a ^ 4 = 1 := by
  let : Finite E := Finite.of_equiv (P×D) e.symm.toEquiv
  have ha : (a : MulAut E) ∈ (quotientAut (center E)).ker := by
    rw [← d.centralFactorWreathAction_ker e]; exact a.property
  obtain ⟨x,hx⟩ := d.exists_nonsingular_square e
  apply Subtype.ext
  have ht := quotient_kernel_pow_four
    (d.center_bound e hD) (d.center_pow_two e) x hx (d.square_center e x) ⟨a,ha⟩
  exact congrArg (fun b : (quotientAut (center E)).ker => (b : MulAut E)) ht

theorem centralFactorWreathAction_ker_isPGroup (hD : Nat.card D ≤ 2) :
    IsPGroup 2 (d.centralFactorWreathAction e).ker := by
  intro a
  exact ⟨2,d.centralFactorWreathAction_kernel_pow_four e hD a⟩


/-- A nontrivial action of a two-perfect group has a cubic in its orthogonal image. -/
theorem three_dvd_centralFactorWreathAction_range {K : Type*} [Group K]
    (hD : Nat.card D ≤ 2) (hK : IsPPerfect 2 K) (f : K →* MulAut E)
    (hne : f ≠ 1) : 3 ∣ Nat.card ((d.centralFactorWreathAction e).comp f).range := by
  classical
  let w := d.centralFactorWreathAction e
  let g := w.comp f
  by_contra h3
  change ¬3 ∣ Nat.card g.range at h3
  have hc : Nat.card BinaryFourPlus.Wreath = 72 :=
    (Nat.card_congr BinaryFourPlus.isometryEquivWreath.toEquiv).symm.trans
      BinaryFourPlus.card_isometrySubgroup
  have hd : Nat.card g.range ∣ 72 := by
    rw [←hc]
    exact g.range.card_subgroup_dvd_card
  have h2 : IsPGroup 2 g.range := by
    apply IsPGroup.of_card_dvd_pow (n:=3)
    have small : ∀ n : ℕ, n ∣ 72 → ¬3 ∣ n → n ∣ 8 := by
      intro n hn h3n
      have hh := Nat.mem_divisors.mpr ⟨hn,by decide⟩
      have he : (72:ℕ).divisors = {1,2,3,4,6,8,9,12,18,24,36,72} := by decide
      rw [he] at hh
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with h|h|h|h|h|h|h|h|h|h|h|h <;> subst n <;> norm_num at *
    exact small _ hd h3

  have hp : IsPGroup 2 (g.range.comap w) := h2.comap_of_ker_isPGroup w
    (d.centralFactorWreathAction_ker_isPGroup e hD)
  let ff : K →* g.range.comap w := f.codRestrict _ (fun k => ⟨k,rfl⟩)
  have hf : ff = 1 := hK.hom_eq_one_of_isPGroup hp ff
  apply hne
  apply MonoidHom.ext
  intro k
  exact congrArg Subtype.val (DFunLike.congr_fun hf k)

end Subgroup.QuaternionCentralProductData

