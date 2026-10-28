module
public import Theory.GroupTheory.ElementaryTwoKernelFusion
public import Theory.GroupTheory.PrimeCyclicCoverage
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Cubic fusion in an elementary extension of PSL₃(2)

The group SL₃(2) has one factor of three in its order. An explicit cubic
matrix is conjugate to its inverse; Sylow conjugacy therefore gives a single
cubic class. Transport to the actual projective quotient and the elementary
kernel fusion lemma give the same result for every elementary two-extension.

If an ambient group has one involution class, move commuting involutions to
one representative and use this centralizer fusion to fuse the corresponding
cubics. These are the steps used in Aschbacher–Smith 5.2.14(1), printed p.654
(`refs/quasithin.pdf`). Commuting-pair fusion also conjugates any two involutions inside a cubic
centralizer, with the conjugator in that literal centralizer, as needed in
5.2.15. No extension splitting is assumed.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.QuasithinM23
private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
private def cubic : SL := ⟨!![0,1,0;1,1,0;0,0,1], by decide⟩
private def inverter : SL := ⟨!![1,1,0;0,1,0;0,0,1], by decide⟩
private theorem cubic_order : orderOf cubic = 3 :=
  orderOf_eq_prime (by decide : cubic^3=1) (by decide : cubic ≠ 1)
private theorem cubic_inverted : IsConj cubic (cubic^2) :=
  isConj_iff.mpr ⟨inverter,by decide⟩

private theorem sl_cubic_conjugate (x : SL) (hx : orderOf x = 3) : IsConj cubic x := by
  obtain ⟨k,g,hg⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    Nat.prime_three (by rw [Matrix.PSL3Two.card_SL]; decide) cubic_order hx
  have hk : cubic^k = cubic^(k%3) := by simpa only [cubic_order] using (pow_mod_orderOf cubic k).symm
  rw [hk] at hg
  have hb : k%3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hm : k%3
  · simp only [pow_zero,mul_one,mul_inv_cancel] at hg
    simp [hg] at hx
  · simp only [pow_one] at hg
    exact isConj_iff.mpr ⟨g,hg.symm⟩
  · exact cubic_inverted.trans (isConj_iff.mpr ⟨g,hg.symm⟩)

/-- The actual PSL₃(2) has one class of elements of order three. -/
theorem psl3Two_cubics_isConj
    (x y : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hx : orderOf x = 3) (hy : orderOf y = 3) : IsConj x y := by
  let e := Matrix.PSL3Two.equiv
  have hh := (sl_cubic_conjugate (e.symm x) ((e.symm.orderOf_eq x).trans hx)).symm.trans
    (sl_cubic_conjugate (e.symm y) ((e.symm.orderOf_eq y).trans hy))
  simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using e.toMonoidHom.map_isConj hh

/-- Cubic fusion lifts through the literal elementary two-core quotient. -/
theorem elementary_psl3Two_cubics_isConj {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (e : X ⧸ U ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    {x y : X} (hx : orderOf x = 3) (hy : orderOf y = 3) : IsConj x y := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' U)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = U := (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans
    (QuotientGroup.ker_mk' _)
  have hk2 (a : X) (ha : q a = 1) : a^2=1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) a (hk ▸ (show a ∈ q.ker from ha))
  have horder (a : X) (ha : orderOf a = 3) : orderOf (q a) = 3 := by
    apply orderOf_eq_prime
    · simpa only [map_pow,map_one,ha] using congrArg q (pow_orderOf_eq_one a)
    · intro hz
      have hd := orderOf_dvd_of_pow_eq_one (hk2 a hz)
      rw [ha] at hd
      norm_num at hd
  exact q.isConj_of_map_isConj_of_cube_eq_one_of_square_kernel hq hk2
    (hx ▸ pow_orderOf_eq_one x) (hy ▸ pow_orderOf_eq_one y)
    (psl3Two_cubics_isConj (q x) (q y) (horder x hx) (horder y hy))
/-- One involution class and one cubic class in its centralizer fuse all
cubics that centralize involutions. -/
theorem cubics_isConj_of_involution_fusion {X : Type*} [Group X]
    (z : X)
    (hinv : ∀ x : X, orderOf x = 2 → IsConj x z)
    (hc : ∀ a b : centralizer ({z} : Set X), orderOf a = 3 → orderOf b = 3 → IsConj a b)
    {a b : X} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (ha2 : ∃ x : X, orderOf x = 2 ∧ Commute a x)
    (hb2 : ∃ x : X, orderOf x = 2 ∧ Commute b x) : IsConj a b := by
  have move (a : X) (ha : orderOf a = 3)
      (ha2 : ∃ x : X, orderOf x = 2 ∧ Commute a x) :
      ∃ a' : centralizer ({z} : Set X), orderOf a' = 3 ∧ IsConj a (a' : X) := by
    obtain ⟨x,hx,hax⟩ := ha2
    obtain ⟨g,hg⟩ := isConj_iff.mp (hinv x hx)
    have hgC : g*a*g⁻¹ ∈ centralizer ({z} : Set X) := by
      rw [mem_centralizer_singleton_iff,←hg]
      have hh := congrArg (MulAut.conj g) hax.eq
      simpa only [map_mul,MulAut.conj_apply] using hh
    let a' : centralizer ({z} : Set X) := ⟨g*a*g⁻¹,hgC⟩
    refine ⟨a',(Subgroup.orderOf_coe a').symm.trans (((MulAut.conj g).orderOf_eq a).trans ha),?_⟩
    exact isConj_iff.mpr ⟨g,rfl⟩
  obtain ⟨a',ha',haa⟩ := move a ha ha2
  obtain ⟨b',hb',hbb⟩ := move b hb hb2
  exact haa.trans (((centralizer ({z} : Set X)).subtype.map_isConj (hc a' b' ha' hb')).trans hbb.symm)

/-- Centralizer fusion transports along the original ambient conjugation. -/
theorem involution_centralizer_cubics_isConj {X : Type*} [Group X]
    (z : X) (hinv : ∀ x : X, orderOf x = 2 → IsConj x z)
    (hc : ∀ a b : centralizer ({z} : Set X), orderOf a = 3 → orderOf b = 3 → IsConj a b)
    (t : X) (ht : orderOf t = 2)
    (a b : centralizer ({t} : Set X)) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    IsConj a b := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hinv t ht)
  let e : centralizer ({t} : Set X) ≃* centralizer ({z} : Set X) :=
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) t).trans
      (MulEquiv.subgroupCongr (congrArg (fun w : X => centralizer ({w} : Set X)) hg))
  have hh := hc (e a) (e b) ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb)
  simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using
    e.symm.toMonoidHom.map_isConj hh

/-- Fusion of commuting pairs conjugates involutions inside each cubic
centralizer. The conjugator lies in the literal centralizer of the cubic. -/
theorem cubic_centralizer_involutions_isConj {X : Type*} [Group X]
    (z : X) (hinv : ∀ x : X, orderOf x = 2 → IsConj x z)
    (hc : ∀ a b : centralizer ({z} : Set X), orderOf a = 3 → orderOf b = 3 → IsConj a b)
    (c : X) (hc3 : orderOf c = 3)
    (s t : centralizer ({c} : Set X)) (hs : orderOf s = 2) (ht : orderOf t = 2) :
    IsConj s t := by
  have hs2 : orderOf (s : X) = 2 := (Subgroup.orderOf_coe s).trans hs
  have ht2 : orderOf (t : X) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨g,hg⟩ := isConj_iff.mp ((hinv s hs2).trans (hinv t ht2).symm)
  let Ct := centralizer ({(t : X)} : Set X)
  have hcT : c ∈ Ct := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp t.property).symm
  have hgcT : g*c*g⁻¹ ∈ Ct := by
    rw [mem_centralizer_singleton_iff,←hg]
    have hh := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp s.property).symm
    simpa only [map_mul,MulAut.conj_apply] using hh
  have hh := involution_centralizer_cubics_isConj z hinv hc t ht2
    (⟨g*c*g⁻¹,hgcT⟩ : Ct) (⟨c,hcT⟩ : Ct)
    ((Subgroup.orderOf_coe _).symm.trans (((MulAut.conj g).orderOf_eq c).trans hc3))
    ((Subgroup.orderOf_coe _).symm.trans hc3)
  obtain ⟨k,hk⟩ := isConj_iff.mp hh
  have hkX : (k : X)*(g*c*g⁻¹)*(k : X)⁻¹ = c := congrArg Subtype.val hk
  have hrc : (k : X)*g ∈ centralizer ({c} : Set X) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      ((k : X)*g)*c*((k : X)*g)⁻¹ = (k : X)*(g*c*g⁻¹)*(k : X)⁻¹ := by group
      _ = c := hkX
  apply isConj_iff.mpr
  refine ⟨⟨(k : X)*g,hrc⟩,Subtype.ext ?_⟩
  change ((k : X)*g)*(s : X)*((k : X)*g)⁻¹ = t
  calc
    _ = (k : X)*(g*(s : X)*g⁻¹)*(k : X)⁻¹ := by group
    _ = (k : X)*(t : X)*(k : X)⁻¹ := by rw [hg]
    _ = t := by rw [mem_centralizer_singleton_iff.mp k.property,mul_inv_cancel_right]

end Theory.GroupTheory.QuasithinM23
