module
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.QuaternionGenerated
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Order-eight groups with a cubic action on a central Klein quotient

A group of order eight with a central subgroup of order two and elementary
quotient of order four is either elementary abelian or quaternion whenever
an automorphism induces a nonidentity automorphism of cube one on that
quotient. The automorphism upstairs is not required to have odd order.

The cubic quotient automorphism permutes all three nonidentity elements in
one orbit. Every square upstairs lies in the central subgroup; the upstairs
automorphism fixes this subgroup pointwise, and equal quotient cosets have
equal squares. If all squares are one, the group is elementary abelian.
Otherwise choose `x` with nontrivial square `z`, and put `y=alpha(x)`. The
quotient orbit identity gives the same square `z` for `x`, `y`, and `xy`.
These equations give the quaternion inversion relation. Distinct nonidentity
quotient images put `y` outside the cyclic subgroup of `x`, so the quaternion
presentation theorem produces an order-eight generated subgroup, which must
be the whole group.

This elementary central-extension calculation supplies the intrinsic
order-eight recognition step in Stellmacher (9.1), Journal of Algebra 190
(1997), p.48, `refs/files/stellmacher-n-group.pdf`. No ambient factor action,
classification, or splitting hypothesis is used.
-/

private theorem cubic_four_fixed_free {W : Type*} [Group W] [Finite W]
    (hW : Nat.card W = 4) (b : MulAut W) (hb : b ^ 3 = 1) (hne : b ≠ 1) :
    ∀ w : W, w ≠ 1 → b w ≠ w := by
  classical
  have h3 (w : W) : b (b (b w)) = w := by
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using
      congrArg (fun f : MulAut W => f w) hb
  obtain ⟨a, ha⟩ : ∃ a : W, b a ≠ a := by
    by_contra! hh
    exact hne (MulEquiv.ext hh)
  have ha1 : a ≠ 1 := by intro hh; subst a; simp at ha
  have hba1 : b a ≠ 1 := by simpa using ha1
  have hbba1 : b (b a) ≠ 1 := by simpa using ha1
  have haa : b (b a) ≠ a := by
    intro hh
    apply ha
    have := congrArg b hh
    rw [h3] at this
    exact this.symm
  have hab : b (b a) ≠ b a := fun hh => ha (b.injective hh)
  let : Fintype W := Fintype.ofFinite W
  have hall : ({1,a,b a,b (b a)} : Finset W) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card,hW]
    simp [Ne.symm ha1, Ne.symm hba1,
      Ne.symm hbba1, Ne.symm ha, Ne.symm haa, Ne.symm hab]
  intro w hw
  have hwmem : w ∈ ({1,a,b a,b (b a)} : Finset W) := hall ▸ Finset.mem_univ w
  simp only [Finset.mem_insert,Finset.mem_singleton] at hwmem
  rcases hwmem with rfl | rfl | rfl | rfl
  · exact (hw rfl).elim
  · exact ha
  · exact hab
  · rw [h3]
    exact haa.symm

private theorem cubic_four_product {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (b : MulAut W) (hb : b ^ 3 = 1) (hne : b ≠ 1) (w : W) (hw : w ≠ 1) :
    w * b w = b (b w) := by
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour W := ⟨hW, IsElementaryAbelian.exponent_eq_prime⟩
  have hfree := cubic_four_fixed_free hW b hb hne
  have hbw : b w ≠ 1 := by simpa using hw
  have hbbw : b (b w) ≠ 1 := by simpa using hw
  apply (IsKleinFour.eq_mul_of_ne_all hw hbw (hfree w hw).symm hbbw ?_ ?_).symm
  · intro hh
    have h3 : b (b (b w)) = w := by
      simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
        congrArg (fun f : MulAut W => f w) hb
    exact hfree w hw ((congrArg b hh).symm.trans h3)
  · exact hfree (b w) hbw

/-- A cubic automorphism on a central Klein quotient forces an order-eight
group to be elementary abelian or quaternion. -/
public theorem elementary_or_quaternion_of_cubic_quotient_action
    {U : Type*} [Group U] [Finite U] (hU : Nat.card U = 8)
    (Z : Subgroup U) [Z.Normal] (hZ : Nat.card Z = 2) (hcentral : Z ≤ Subgroup.center U)
    [IsElementaryAbelian 2 (U ⧸ Z)] (hW : Nat.card (U ⧸ Z) = 4)
    (a : MulAut U) (b : MulAut (U ⧸ Z))
    (hcompat : ∀ u : U, b (QuotientGroup.mk' Z u) = QuotientGroup.mk' Z (a u))
    (hb3 : b ^ 3 = 1) (hbne : b ≠ 1) :
    IsElementaryAbelian 2 U ∨ Nonempty (U ≃* QuaternionGroup 2) := by
  classical
  let q := QuotientGroup.mk' Z
  have hZsq (z : U) (hz : z ∈ Z) : z ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : Z))
    rw [hZ] at hh
    exact congrArg Subtype.val hh
  have hsquare (u : U) : u ^ 2 ∈ Z := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (u ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (U ⧸ Z)) (q u)
  have hfix (z : U) (hz : z ∈ Z) : a z = z := by
    have haz : a z ∈ Z := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (a z) = 1
      rw [← hcompat]
      have hqz : q z = 1 := (QuotientGroup.eq_one_iff _).mpr hz
      rw [hqz,map_one]
    by_cases hz1 : z = 1
    · simp [hz1]
    obtain ⟨t, _, ht⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
    have hn : (⟨a z,haz⟩ : Z) ≠ 1 := by
      intro hh
      exact hz1 (a.injective ((congrArg Subtype.val hh).trans (map_one a).symm))
    have hn' : (⟨z,hz⟩ : Z) ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
    exact congrArg Subtype.val ((ht _ hn).trans (ht _ hn').symm)
  have heqsquare (u v : U) (he : q u = q v) : u ^ 2 = v ^ 2 := by
    have hz : u⁻¹ * v ∈ Z := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (u⁻¹ * v) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hc : Commute u (u⁻¹ * v) := (Subgroup.mem_center_iff.mp (hcentral hz) u)
    have hh := hc.mul_pow 2
    rw [mul_inv_cancel_left,hZsq _ hz,mul_one] at hh
    exact hh.symm
  by_cases hexp : ∀ u : U, u ^ 2 = 1
  · left
    have hdiv := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hexp
    have hcomm : ∀ x y : U, x*y=y*x := by
      intro x y
      have hinv (t : U) : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hexp t)
      calc
        x*y = (x*y)⁻¹ := (hinv _).symm
        _ = y*x := by rw [mul_inv_rev,hinv,hinv]
    exact { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := hdiv }
  · right
    push Not at hexp
    obtain ⟨x,hx⟩ := hexp
    let z := x ^ 2
    let y := a x
    have hzZ : z ∈ Z := hsquare x
    have hz2 : z ^ 2 = 1 := hZsq z hzZ
    have hy2 : y ^ 2 = z := by rw [← map_pow,hfix _ hzZ]
    have hxq : q x ≠ 1 := by
      intro hh
      exact hx (hZsq x ((QuotientGroup.eq_one_iff _).mp hh))
    have hxyq : q (x*y) = q (a (a x)) := by
      change q (x*a x) = q (a (a x))
      rw [map_mul,← hcompat,← hcompat,← hcompat]
      exact cubic_four_product hW b hb3 hbne (q x) hxq
    have hxy2 : (x*y)^2=z := by
      rw [heqsquare _ _ hxyq,← map_pow,← map_pow,hfix _ hzZ,hfix _ hzZ]
    have hx4 : orderOf x = 4 := by
      apply orderOf_eq_prime_pow (p := 2) (n := 1)
      · simpa using hx
      · simpa only [show 2^(1+1)=4 by decide,show 4=2*2 by decide,pow_mul] using hz2
    have hyx : y*x*y⁻¹=x⁻¹ := by
      have he : (x*y)*(x*y)=y*y := by rw [← pow_two,← pow_two,hxy2,hy2]
      have he' : x*y*x=y := mul_right_cancel (by simpa only [mul_assoc] using he)
      calc
        y*x*y⁻¹ = x⁻¹*(x*y*x)*y⁻¹ := by group
        _ = x⁻¹ := by rw [he']; group
    have hynot : y ∉ Subgroup.zpowers x := by
      rintro ⟨n, hn⟩
      have hqxy : q y ≠ q x := by
        rw [← hcompat]
        exact cubic_four_fixed_free hW b hb3 hbne (q x) hxq
      have hq2 : (q x)^2=1 := by
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (U ⧸ Z)) (q x)
      have hord : orderOf (q x)=2 := orderOf_eq_prime hq2 hxq
      have hnq : (q x)^n=q y := by simpa only [map_zpow] using congrArg q hn
      have hred : (q x)^n=(q x)^(n%2) := by
        simpa only [hord,Nat.cast_ofNat] using (zpow_mod_orderOf (q x) n).symm
      rcases Int.emod_two_eq_zero_or_one n with hh | hh
      · rw [hred,hh,zpow_zero] at hnq
        have hyq : q y ≠ 1 := by
          change q (a x) ≠ 1
          rw [← hcompat]
          exact fun hh => hxq (b.injective (hh.trans b.map_one.symm))
        exact hyq hnq.symm
      · rw [hred,hh,zpow_one] at hnq
        exact hqxy hnq.symm
    obtain ⟨hcard,⟨e⟩⟩ := QuaternionGroup.closure_equiv_of_relations
      (m := 2) (by decide) x y hx4 (hy2) hyx hynot
    have ht : Subgroup.closure ({x,y} : Set U)=⊤ :=
      Subgroup.eq_top_of_card_eq _ (hcard.trans (by omega))
    exact ⟨(Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr ht).symm)).trans e⟩
