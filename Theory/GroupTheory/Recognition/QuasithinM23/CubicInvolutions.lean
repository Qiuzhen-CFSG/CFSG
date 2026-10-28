module
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.SylowNormalizerRank
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FiveLines
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FieldDescent
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Adjusting two cubic-inverting involutions in ΓL₂(4)

The five-line action has the scalar cubic as its kernel. A normal subgroup
of order three must be this kernel, since S₅ has no nontrivial normal cubic.
An involution inverting it has Frobenius coefficients and induces a
transposition on the five lines. Multiplying the first involution by a scalar
makes its product with the second determinant one. The faithful SL₂(4)
action then transfers the transposition product bound back to ΓL₂(4).

The last theorem transports the adjustment through an equivalence of the
actual ambient cubic normalizer. The multiplier stays in the original cubic,
which lets the source consumer preserve its entire overlap and both endpoints.
Only the 120 permutations on five letters and their 625 swap pairs are used
in the small kernel-checked permutation calculations.

Source: Aschbacher–Smith 5.2.16, printed p.655 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Matrix
open Representation.SL2FourNatural Representation.SL2FourNatural.SemilinearNormalizer
namespace Theory.GroupTheory.QuasithinM23
private theorem scalar_natural (a : Fˣ) (v : V) : natural (scalar a) v = (a : F) • v := by
  rw [natural_apply]
  change (Matrix.GeneralLinearGroup.scalar (Fin 2) a).val.mulVec v = _
  rw [Matrix.GeneralLinearGroup.coe_scalar,Matrix.scalar_apply,Matrix.diagonal_const_mulVec]

private theorem scalar_injective : Function.Injective scalar := by
  intro a b h
  apply Units.ext
  have hh := congrArg (fun g : Gamma => natural g (fun _ => 1) 0) h
  simpa only [scalar_natural,Pi.smul_apply,smul_eq_mul,mul_one] using hh

private theorem fiveLines_scalar (a : Fˣ) : fiveLines (scalar a) = 1 := by
  ext i
  rw [fiveLines_apply,scalar_natural,lineIndex_smul _ a.ne_zero,lineIndex_vector]
  rfl

private theorem scalarSpecial_surjective : Function.Surjective scalarSpecial := by
  let : Finite LinearGroup := inferInstance
  have hc : Nat.card scalarSpecial.range = Nat.card LinearGroup := by
    rw [← Nat.card_congr (MonoidHom.ofInjective scalarSpecial_injective).toEquiv,
      Nat.card_prod,Nat.card_eq_fintype_card (α := Fˣ),card_labels,
      Nat.card_congr alternatingFiveEquiv.toEquiv,nat_card_alternatingGroup,
      Matrix.card_GL_field,card_field]
    norm_num
  exact MonoidHom.range_eq_top.mp (eq_top_of_card_eq _ hc)

private theorem gamma_decomposition (g : Gamma) :
    ∃ a : Fˣ, ∃ b : SL, g = scalar a * special b * SemidirectProduct.inr g.right := by
  obtain ⟨⟨a,b⟩,hab⟩ := scalarSpecial_surjective g.left
  refine ⟨a,b,?_⟩
  rw [←SemidirectProduct.inl_left_mul_inr_right g,←hab]
  change SemidirectProduct.inl
      (Matrix.GeneralLinearGroup.scalar (Fin 2) a * Matrix.SpecialLinearGroup.toGL b) * _ = _
  rw [map_mul]
  rfl

private theorem fiveLines_ker : fiveLines.ker = scalar.range := by
  have hle : scalar.range ≤ fiveLines.ker := by
    rintro _ ⟨a,rfl⟩
    exact fiveLines_scalar a
  have hs : Function.Surjective fiveLines := by
    intro p
    obtain ⟨x,hx⟩ := specialFieldFiveLines_surjective p
    exact ⟨x,hx⟩
  have hsCard : Nat.card scalar.range = 3 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective scalar_injective).toEquiv,
      Nat.card_eq_fintype_card,card_labels]
  let : Finite Gamma := Nat.finite_of_card_ne_zero (by rw [gamma_card]; decide)
  have hq : Nat.card (Gamma ⧸ fiveLines.ker) = 120 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective fiveLines hs).toEquiv,
      Nat.card_perm,Nat.card_fin]
    norm_num
  have hk := fiveLines.ker.card_mul_index
  rw [index_eq_card,hq,gamma_card] at hk
  exact (eq_of_le_of_card_ge hle (by rw [hsCard]; omega)).symm

private theorem normal_cubic_scalar (c : Gamma) (hc : orderOf c = 3)
    (hn : (zpowers c).Normal) : zpowers c = scalar.range := by
  let : Finite Gamma := Nat.finite_of_card_ne_zero (by rw [gamma_card]; decide)
  let N := (zpowers c).map fiveLines
  have hs : Function.Surjective fiveLines := by
    intro p
    obtain ⟨x,hx⟩ := specialFieldFiveLines_surjective p
    exact ⟨x,hx⟩
  let : N.Normal := Normal.map hn fiveLines hs
  have hN : Nat.card N ∣ 3 := by
    have hd := card_map_dvd (zpowers c) fiveLines
    rwa [Nat.card_zpowers,hc] at hd
  have hz : N = ⊥ := by
    by_contra hh
    have hnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hh
    have ha := Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt
    have hd := (card_dvd_of_le ha).trans hN
    rw [nat_card_alternatingGroup,Nat.card_fin] at hd
    norm_num at hd
  have hle : zpowers c ≤ scalar.range := by
    rw [←fiveLines_ker]
    intro x hx
    have hm := mem_map_of_mem fiveLines hx
    change fiveLines x ∈ N at hm
    rw [hz,mem_bot] at hm
    exact hm
  apply eq_of_le_of_card_ge hle
  rw [Nat.card_zpowers,hc,
    ←Nat.card_congr (MonoidHom.ofInjective scalar_injective).toEquiv,
    Nat.card_eq_fintype_card,card_labels]

private theorem field_fiveLines_odd (g : Gamma) (hr : g.right = fieldFrobenius) :
    Equiv.Perm.sign (fiveLines g) = -1 := by
  obtain ⟨a,b,hg⟩ := gamma_decomposition g
  rw [hr] at hg
  rw [hg,fiveLines.map_mul,fiveLines.map_mul,fiveLines_scalar,one_mul]
  change Equiv.Perm.sign (fiveLines (special b) * fiveLines fieldElement) = _
  rw [map_mul,fiveLines_fieldElement,Equiv.Perm.sign_swap (by decide)]
  have hb : fiveLines (special b) ∈ alternatingGroup (Fin 5) := by
    rw [←specialFiveLines_range]
    exact ⟨b,rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup] at hb
  rw [hb,one_mul]

private theorem odd_involution_swap (p : Equiv.Perm (Fin 5))
    (hp : p^2=1) (hs : Equiv.Perm.sign p = -1) : p.IsSwap := by
  change ∃ a b : Fin 5, a ≠ b ∧ p = Equiv.swap a b
  revert p
  decide +kernel

private theorem swaps_small (a b c d : Fin 5) :
    ((Equiv.swap a b) * (Equiv.swap c d))^2=1 ∨
    ((Equiv.swap a b) * (Equiv.swap c d))^3=1 := by
  revert a b c d
  decide +kernel

private theorem inverter_field (c s : Gamma) (hc : orderOf c = 3)
    (hn : (zpowers c).Normal) (hs : s^2=1) (hi : s*c*s⁻¹=c⁻¹) :
    s.right = fieldFrobenius := by
  apply field_coefficient_of_involution s hs
  rintro ⟨b,rfl⟩
  have hcm : c ∈ scalar.range := normal_cubic_scalar c hc hn ▸ mem_zpowers c
  obtain ⟨a,rfl⟩ := hcm
  have hh : scalar a = (scalar a)⁻¹ := by
    simpa only [←(scalar_special_commute a b).eq,mul_assoc,mul_inv_cancel,mul_one] using hi
  have hp : (scalar a)^2=1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr hh
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hc] at hd
  norm_num at hd

/-- In ΓL₂(4), adjust an inverting involution by an element of the same
normal cubic so that the two involutions have product of order at most three. -/
theorem cubic_adjustment (c s t : Gamma) (hc : orderOf c = 3)
    (hn : (zpowers c).Normal) (hs : orderOf s = 2) (ht : orderOf t = 2)
    (his : s*c*s⁻¹=c⁻¹) (hit : t*c*t⁻¹=c⁻¹) :
    ∃ a ∈ zpowers c, orderOf (a*s) = 2 ∧ orderOf ((a*s)*t) ≤ 3 := by
  have hs2 : s^2=1 := by simpa only [hs] using pow_orderOf_eq_one s
  have ht2 : t^2=1 := by simpa only [ht] using pow_orderOf_eq_one t
  have hrs := inverter_field c s hc hn hs2 his
  have hrt := inverter_field c t hc hn ht2 hit
  let d : Fˣ := Matrix.GeneralLinearGroup.det (s*t).left
  let a := scalar d
  have ha : a ∈ zpowers c := by rw [normal_cubic_scalar c hc hn]; exact ⟨d,rfl⟩
  have hai : s*a*s⁻¹=a⁻¹ := by
    obtain ⟨k,hk⟩ := ha
    rw [←hk]
    change MulAut.conj s (c^k) = (c^k)⁻¹
    rw [map_zpow]
    change (s*c*s⁻¹)^k=(c^k)⁻¹
    rw [his,_root_.inv_zpow]
  have has2 : (a*s)^2=1 := by
    calc
      (a*s)^2 = a*(s*a*s⁻¹)*s^2 := by simp only [pow_two]; group
      _ = 1 := by rw [hai,hs2]; group
  have hasr : (a*s).right = fieldFrobenius := by
    change (1 : F ≃+* F)*s.right = _
    rw [one_mul,hrs]
  have has : orderOf (a*s)=2 := orderOf_eq_prime has2 (by
    intro hh
    have hh' := congrArg SemidirectProduct.right hh
    exact fieldFrobenius_ne_one (hasr.symm.trans hh'))
  have hst : (a*s)*t ∈ special.range := by
    rw [mem_special_range]
    constructor
    · change ((1 : F ≃+* F)*s.right)*t.right=1
      rw [one_mul,hrs,hrt]
      apply RingEquiv.ext
      intro x
      exact fieldFrobenius_involutive x
    · have hleft : ((a*s)*t).left = Matrix.GeneralLinearGroup.scalar (Fin 2) d * (s*t).left := by
        change (scalar d*s*t).left = _
        rw [mul_assoc]
        rfl
      rw [hleft,map_mul,Matrix.GeneralLinearGroup.det_scalar,Fintype.card_fin]
      change d^2*d=1
      exact (pow_succ d 2).symm.trans (units_cube d)
  have hpow (k : ℕ) (hk : (fiveLines ((a*s)*t))^k=1) : ((a*s)*t)^k=1 := by
    obtain ⟨b,hb⟩ := hst
    have hbpow : b^k=1 := specialFiveLines_injective (by
      change fiveLines (special (b^k)) = fiveLines (special 1)
      simpa only [map_pow,map_one,hb] using hk)
    rw [←hb,←map_pow,hbpow,map_one]
  have hss := odd_involution_swap (fiveLines (a*s))
    (by rw [←map_pow,has2,map_one]) (field_fiveLines_odd _ hasr)
  have hts := odd_involution_swap (fiveLines t)
    (by rw [←map_pow,ht2,map_one]) (field_fiveLines_odd _ hrt)
  obtain ⟨i,j,_,hij⟩ := hss
  obtain ⟨k,l,_,hkl⟩ := hts
  have hsmall : (fiveLines ((a*s)*t))^2=1 ∨ (fiveLines ((a*s)*t))^3=1 := by
    rw [fiveLines.map_mul,hij,hkl]
    exact swaps_small i j k l
  refine ⟨a,ha,has,?_⟩
  rcases hsmall with hsmall | hsmall
  · exact (orderOf_le_of_pow_eq_one (by decide) (hpow 2 hsmall)).trans (by decide)
  · exact orderOf_le_of_pow_eq_one (by decide) (hpow 3 hsmall)

/-- The same adjustment in an arbitrary group, using its actual cubic normalizer. -/
theorem cubic_adjustment_of_normalizer_equiv
    {G : Type*} [Group G] (c s t : G) (hc : orderOf c = 3)
    (e : normalizer (zpowers c : Set G) ≃* Gamma)
    (hs : orderOf s = 2) (ht : orderOf t = 2)
    (his : s*c*s⁻¹=c⁻¹) (hit : t*c*t⁻¹=c⁻¹) :
    ∃ a ∈ zpowers c, orderOf (a*s) = 2 ∧ orderOf ((a*s)*t) ≤ 3 := by
  let N := normalizer (zpowers c : Set G)
  have hinN (x : G) (hx : x*c*x⁻¹=c⁻¹) : x ∈ N := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (x*c*x⁻¹)=zpowers c
    rw [hx,zpowers_inv]
  let cN : N := ⟨c,(zpowers c).le_normalizer (mem_zpowers c)⟩
  let sN : N := ⟨s,hinN s his⟩
  let tN : N := ⟨t,hinN t hit⟩
  have hcyc : zpowers cN = (zpowers c).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [MonoidHom.map_zpowers,map_subgroupOf_eq_of_le (zpowers c).le_normalizer]
    rfl
  have hn : (zpowers cN).Normal := by
    rw [hcyc]
    exact normal_subgroupOf_of_le_normalizer le_rfl
  have hec : (zpowers (e cN)).Normal := by
    have hh := Normal.map hn e.toMonoidHom e.surjective
    rwa [MonoidHom.map_zpowers] at hh
  have hc3 : orderOf (e cN)=3 := (e.orderOf_eq cN).trans
    ((Subgroup.orderOf_coe cN).symm.trans hc)
  have hs2 : orderOf (e sN)=2 := (e.orderOf_eq sN).trans
    ((Subgroup.orderOf_coe sN).symm.trans hs)
  have ht2 : orderOf (e tN)=2 := (e.orderOf_eq tN).trans
    ((Subgroup.orderOf_coe tN).symm.trans ht)
  have hes : e sN*e cN*(e sN)⁻¹=(e cN)⁻¹ := by
    simpa only [map_mul,map_inv] using congrArg e (show sN*cN*sN⁻¹=cN⁻¹ from Subtype.ext his)
  have het : e tN*e cN*(e tN)⁻¹=(e cN)⁻¹ := by
    simpa only [map_mul,map_inv] using congrArg e (show tN*cN*tN⁻¹=cN⁻¹ from Subtype.ext hit)
  obtain ⟨a,ha,has,hast⟩ := cubic_adjustment (e cN) (e sN) (e tN) hc3 hec hs2 ht2 hes het
  have haN : e.symm a ∈ zpowers cN := by
    obtain ⟨k,hk⟩ := ha
    refine ⟨k,?_⟩
    apply e.injective
    rw [map_zpow,e.apply_symm_apply]
    exact hk
  have ham : (e.symm a : G) ∈ zpowers c := by
    rw [hcyc] at haN
    exact haN
  refine ⟨e.symm a,ham,?_,?_⟩
  · have hh := (e.orderOf_eq (e.symm a*sN)).trans (Subgroup.orderOf_coe (e.symm a*sN)).symm
    rw [map_mul,e.apply_symm_apply] at hh
    exact hh.symm.trans has
  · have hh := (e.orderOf_eq ((e.symm a*sN)*tN)).trans
      (Subgroup.orderOf_coe ((e.symm a*sN)*tN)).symm
    rw [map_mul,map_mul,e.apply_symm_apply] at hh
    exact hh.symm.le.trans hast
end Theory.GroupTheory.QuasithinM23
