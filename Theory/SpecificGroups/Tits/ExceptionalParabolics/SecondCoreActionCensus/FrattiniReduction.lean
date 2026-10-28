module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.CoreAutomorphisms
public import Theory.Frattini.PGroup

/-!
# Intrinsic restrictions on the two core generator images

Neither s3 nor s7 lies in the Frattini subgroup: otherwise nongeneration
would make the order-1024 core cyclic of order at most four. The positive
words for the seven generators compute their images in the elementary
abelian Frattini quotient. Two parity coordinates therefore give a
sufficient Frattini membership test. With s3 fixed, the s7 image must lie
outside the s3 line, giving the second parity restriction.

The final two image lemmas apply these tests to arbitrary automorphisms of
the literal core. They feed the finite exhaustion in the marked outer
quotient, which remains owned by qt-e-quintic-second-parabolic.
Source and marking: Parrott (1972), §5, p.683; see `CoreGenerators`.
-/

public section
namespace Tits.ExceptionalParabolics.SecondCoreAction
open CoreGenerators Subgroup

private theorem powers : (generator 2) ^ 4 = 1 ∧ (generator 6) ^ 4 = 1 := by
  constructor
  all_goals
    apply eq_of_points
    all_goals
      simp only [map_pow,map_one,perm_generator]
      decide +kernel

private theorem not_frattini_of_pair (i : Fin 2) : pairGenerator i ∉ frattini Core := by
  intro hi
  let j : Fin 2 := 1-i
  let K := zpowers (pairGenerator j)
  have hle : Submonoid.closure (Set.range pairGenerator) ≤
      (K ⊔ frattini Core).toSubmonoid := by
    apply Submonoid.closure_le.mpr
    rintro x ⟨k,rfl⟩
    by_cases hki : k = i
    · exact Subgroup.mem_sup_right (by simpa only [hki] using hi)
    · have hkj : k = j := by
        fin_cases i <;> fin_cases k <;> simp_all [j]
      exact Subgroup.mem_sup_left (by simpa only [hkj] using mem_zpowers (pairGenerator j))
  have hsup : K ⊔ frattini Core = ⊤ := by
    apply top_unique
    intro x _
    apply hle
    rw [positive_generates]
    trivial
  have hK : K = ⊤ := frattini_nongenerating hsup
  have ho : orderOf (pairGenerator j) = Nat.card Core :=
    orderOf_eq_card_of_zpowers_eq_top hK
  have hall : ∀ k : Fin 2, (pairGenerator k)^4 = 1 := by
    intro k
    fin_cases k
    · exact powers.1
    · exact powers.2
  have hp := hall j
  have hd : Nat.card Core ∣ 4 := by
    rw [← ho]
    exact orderOf_dvd_of_pow_eq_one hp
  have hc : Nat.card Core = 1024 :=
    (Nat.card_congr CoreGenerators.equiv).symm.trans (by simp)
  rw [hc] at hd
  norm_num at hd

theorem first_not_frattini : generator 2 ∉ frattini Core := not_frattini_of_pair 0
theorem second_not_frattini : generator 6 ∉ frattini Core := not_frattini_of_pair 1

theorem first_image_not_frattini (a : MulAut Core) : a (generator 2) ∉ frattini Core := by
  intro h
  have h' := (characteristic_iff_le_comap.mp
    (inferInstance : (frattini Core).Characteristic) a.symm) h
  exact first_not_frattini (by simpa using h')


private theorem generatorWord_mod_two {A : Type*} [CommGroup A]
    (x y : A) (hx : x^2=1) (hy : y^2=1) (i : Fin 7) :
    generatorWord x y i = ![1,1,x,1,x,1,y] i := by
  have hw : generatorWord x y i =
      x ^ (![10,4,1,4,1,4,0] i) * y ^ (![4,4,0,4,4,4,1] i) := by
    fin_cases i <;> simp [generatorWord,pow_succ,mul_left_comm,mul_comm]
  have hx4 : x^4=1 := by
    rw [show 4=2*2 from rfl,pow_mul,hx,one_pow]
  have hy4 : y^4=1 := by
    rw [show 4=2*2 from rfl,pow_mul,hy,one_pow]
  have hx10 : x^10=1 := by
    rw [show 10=2*5 from rfl,pow_mul,hx,one_pow]
  rw [hw]
  fin_cases i <;> simp [hx4,hy4,hx10]

local instance : Fact (IsPGroup 2 Core) := ⟨pCore_isPGroup⟩
open scoped IsMulCommutative

private theorem quotient_generator (i : Fin 7) :
    QuotientGroup.mk' (frattini Core) (generator i) =
      ![1,1,QuotientGroup.mk' (frattini Core) (generator 2),1,
        QuotientGroup.mk' (frattini Core) (generator 2),1,
        QuotientGroup.mk' (frattini Core) (generator 6)] i := by
  let q := QuotientGroup.mk' (frattini Core)
  let : IsElementaryAbelian 2 (Core ⧸ frattini Core) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  have hpow (z : Core) : q z ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := frattini Core) (x := z^2)).mpr
      (pth_power_mem_frattini_of_isPGroup (p := 2) z)
  rw [← generatorWord_eq,map_generatorWord]
  exact generatorWord_mod_two (q (generator 2)) (q (generator 6))
    (hpow _) (hpow _) i

/-- The two parity tests suffice for membership in the actual Frattini subgroup. -/
theorem parity_mem_frattini (n : Fin 1024)
    (hx : (n.val/4+n.val/32)%2=0) (hy : (n.val/256)%2=0) :
    coreNormalForm n ∈ frattini Core := by
  let q := QuotientGroup.mk' (frattini Core)
  have hp (z : Core) : q z ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := frattini Core) (x := z^2)).mpr
      (pth_power_mem_frattini_of_isPGroup (p := 2) z)
  apply (QuotientGroup.eq_one_iff (N := frattini Core) (x := coreNormalForm n)).mp
  have h0 : q (generator 0) = 1 := by simpa [q] using quotient_generator 0
  have h1 : q (generator 1) = 1 := by simpa [q] using quotient_generator 1
  have h3 : q (generator 3) = 1 := by simpa [q] using quotient_generator 3
  have h4 : q (generator 4) = q (generator 2) := by simpa [q] using quotient_generator 4
  have h5 : q (generator 5) = 1 := by simpa [q] using quotient_generator 5
  have he : q (coreNormalForm n) =
      q (generator 2) ^ (n.val/4%4+n.val/32%4) * q (generator 6) ^ (n.val/256%4) := by
    rw [normal_form]
    simp only [map_mul,map_pow,h0,h1,h3,h4,h5,one_pow,one_mul,mul_one,← pow_add]
  change q (coreNormalForm n) = 1
  rw [he]
  have hxd : 2 ∣ n.val/4%4+n.val/32%4 := Nat.dvd_of_mod_eq_zero (by omega)
  have hyd : 2 ∣ n.val/256%4 := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨a,ha⟩ := hxd
  obtain ⟨b,hb⟩ := hyd
  rw [ha,hb,pow_mul,pow_mul,hp,hp,one_pow,one_pow,one_mul]


/-- The literal core generator-image census may discard every normal form
with both Frattini parity coordinates zero. -/
theorem first_image_parity (a : MulAut Core) (n : Fin 1024)
    (hn : a (generator 2) = coreNormalForm n) :
    (n.val/4+n.val/32)%2 ≠ 0 ∨ (n.val/256)%2 ≠ 0 := by
  by_contra h
  push Not at h
  exact first_image_not_frattini a (hn.symm ▸ parity_mem_frattini n h.1 h.2)


private theorem first_zpowers_ne_top : zpowers (generator 2) ≠ ⊤ := by
  intro htop
  have ho := orderOf_eq_card_of_zpowers_eq_top htop
  have hd : Nat.card Core ∣ 4 := by
    rw [← ho]
    exact orderOf_dvd_of_pow_eq_one powers.1
  have hc : Nat.card Core = 1024 :=
    (Nat.card_congr CoreGenerators.equiv).symm.trans (by simp)
  rw [hc] at hd
  norm_num at hd

/-- The second generator is outside the line generated by the first in the
Frattini quotient; otherwise Frattini nongeneration makes the core cyclic. -/
theorem second_not_line : generator 6 ∉ zpowers (generator 2) ⊔ frattini Core := by
  intro hy
  let K := zpowers (generator 2) ⊔ frattini Core
  have hle : Submonoid.closure (Set.range pairGenerator) ≤ K.toSubmonoid := by
    apply Submonoid.closure_le.mpr
    rintro x ⟨i,rfl⟩
    fin_cases i
    · exact Subgroup.mem_sup_left (mem_zpowers _)
    · exact hy
  have hK : K = ⊤ := by
    apply top_unique
    intro x _
    apply hle
    rw [positive_generates]
    trivial
  exact first_zpowers_ne_top (frattini_nongenerating hK)

theorem second_image_not_line (a : MulAut Core) (ha : a (generator 2) = generator 2) :
    a (generator 6) ∉ zpowers (generator 2) ⊔ frattini Core := by
  intro h
  let K := zpowers (generator 2) ⊔ frattini Core
  have hx : a.symm (generator 2) = generator 2 :=
    a.symm_apply_eq.mpr ha.symm
  have hle : K ≤ K.comap a.symm.toMonoidHom := by
    apply sup_le
    · apply zpowers_le.mpr
      change a.symm (generator 2) ∈ K
      rw [hx]
      exact Subgroup.mem_sup_left (mem_zpowers _)
    · intro z hz
      have hz' := (characteristic_iff_le_comap.mp
        (inferInstance : (frattini Core).Characteristic) a.symm) hz
      exact Subgroup.mem_sup_right hz'
  exact second_not_line (by simpa [K] using hle h)

/-- An even last-generator exponent is on the first-generator line. -/
theorem parity_mem_line (n : Fin 1024) (hy : (n.val/256)%2=0) :
    coreNormalForm n ∈ zpowers (generator 2) ⊔ frattini Core := by
  let K := zpowers (generator 2) ⊔ frattini Core
  have h0 : generator 0 ∈ frattini Core := by
    exact parity_mem_frattini 1 (by decide) (by decide)
  have h1 : generator 1 ∈ frattini Core := by
    exact parity_mem_frattini 2 (by decide) (by decide)
  have h3 : generator 3 ∈ frattini Core := by
    exact parity_mem_frattini 16 (by decide) (by decide)
  have h5 : generator 5 ∈ frattini Core := by
    exact parity_mem_frattini 128 (by decide) (by decide)
  have h4 : generator 4 ∈ K := by
    have hq := quotient_generator 4
    change QuotientGroup.mk' (frattini Core) (generator 4) =
      QuotientGroup.mk' (frattini Core) (generator 2) at hq
    have hf : (generator 2)⁻¹ * generator 4 ∈ frattini Core := by
      apply (QuotientGroup.eq_one_iff (N := frattini Core)
        (x := (generator 2)⁻¹ * generator 4)).mp
      change QuotientGroup.mk' (frattini Core) _ = _
      rw [map_mul,map_inv,hq,inv_mul_cancel]
    have hprod := K.mul_mem (show generator 2 ∈ K from Subgroup.mem_sup_left (mem_zpowers _))
      (Subgroup.mem_sup_right hf)
    simpa only [mul_inv_cancel_left] using hprod
  have hlast : generator 6 ^ (n.val/256%4) ∈ K := by
    have hyd : 2 ∣ n.val/256%4 := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨b,hb⟩ := hyd
    rw [hb,pow_mul]
    exact K.pow_mem (Subgroup.mem_sup_right
      (pth_power_mem_frattini_of_isPGroup (p := 2) (generator 6))) b
  rw [normal_form]
  exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
    (K.pow_mem (Subgroup.mem_sup_right h0) _)
    (K.pow_mem (Subgroup.mem_sup_right h1) _))
    (K.pow_mem (Subgroup.mem_sup_left (mem_zpowers _)) _))
    (K.pow_mem (Subgroup.mem_sup_right h3) _))
    (K.pow_mem h4 _)) (K.pow_mem (Subgroup.mem_sup_right h5) _)) hlast

theorem second_image_parity (a : MulAut Core) (ha : a (generator 2) = generator 2)
    (n : Fin 1024) (hn : a (generator 6) = coreNormalForm n) :
    (n.val/256)%2 ≠ 0 := by
  intro hy
  exact second_image_not_line a ha (hn.symm ▸ parity_mem_line n hy)

end Tits.ExceptionalParabolics.SecondCoreAction
