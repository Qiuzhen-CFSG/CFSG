module
public import ABG.ChapterII.Section1.LargeCyclicIntersection
public import Theory.GroupTheory.SpecificGroups.SmallInvertedCyclicModels
/-!
# Small subgroups of a quasi-dihedral group

Every subgroup of order at most eight in a quasi-dihedral group is cyclic,
a Klein four group, a dihedral group of order eight, or a quaternion group
of order eight. The final two alternatives give actual multiplicative
isomorphisms to the standard models.

This elementary presentation consequence supplies the subgroup alternatives
needed for the fusion analysis in Alperin–Brauer–Gorenstein, Chapter II,
§1, Proposition 1, following Lemma 1 of
`refs/latex/alperin-brauer-gorenstein.tex`. The ambient group uses the
production semidihedral presentation, whose order parameter is at least four.

Intersect a noncyclically contained subgroup with the cyclic maximal subgroup.
The intersection is cyclic of index two. Since the subgroup has order dividing
eight, the intersection has order dividing four. Conjugation by an outer
normal form acts on it by the semidihedral exponent, which is minus one
modulo four. The generic inverted-cyclic-subgroup recognition theorem now
identifies the small group using its generators and relations.
-/

namespace ABG.QuasiDihedral
universe u
variable {G : Type u} [Group G]
private theorem small_rotation_inverted {n : ℕ} (hn : 4 ≤ n) (a b x t : G)
    (hab : b * a * b⁻¹ = a ^ (2^(n-2)-1))
    (hx : ∃ i : ℕ, x = a^i*b) (ht : t ∈ Subgroup.zpowers a)
    (ht4 : t^4=1) : x*t*x⁻¹=t⁻¹ := by
  obtain ⟨j, hj⟩ := ht
  have hbt : b*t*b⁻¹=t^(2^(n-2)-1) := by
    change a ^ j = t at hj
    rw [← hj]
    change (MulAut.conj b) (a^j) = (a^j)^(2^(n-2)-1)
    rw [map_zpow, MulAut.conj_apply, hab]
    simp only [← zpow_natCast, ← zpow_mul, mul_comm]
  have hti : t^(2^(n-2)-1)=t⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide) : 1 ≤ 2^(n-2))]
    have hd : 4 ∣ 2^(n-2) := by
      change 2^2 ∣ 2^(n-2)
      exact pow_dvd_pow 2 (by omega)
    obtain ⟨k,hk⟩ := hd
    rw [hk,pow_mul,ht4,one_pow]
  obtain ⟨i,rfl⟩ := hx
  calc
    _ = a^i*(b*t*b⁻¹)*(a^i)⁻¹ := by group
    _ = a^i*t⁻¹*(a^i)⁻¹ := by rw [hbt,hti]
    _ = t⁻¹ := by
      have hc : Commute (a^i) t := by rw [←hj]; exact (Commute.refl a).pow_left i |>.zpow_right j
      rw [hc.inv_right.eq]
      group

private theorem subgroup_card_dvd_eight {n : ℕ} (hcard : Nat.card G=2^n)
    (X : Subgroup G) (hXcard : Nat.card X ≤ 8) : Nat.card X ∣ 8 := by
  have hd : Nat.card X ∣ 2^n := hcard ▸ X.card_subgroup_dvd_card
  obtain ⟨k,hkn,hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hk3 : k ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [←hk] using hXcard
  exact hk ▸ (pow_dvd_pow 2 hk3 : 2^k ∣ 2^3)

/-- A subgroup of order at most eight has one of the four standard small models. -/
public theorem small_subgroup_models
    (hG : Stellmacher.IsSemidihedralGroup G) (X : Subgroup G)
    (hXcard : Nat.card X ≤ 8) :
    IsCyclic X ∨ IsKleinFour X ∨ Nonempty (X ≃* DihedralGroup 4) ∨
      Nonempty (X ≃* QuaternionGroup 2) := by
  obtain ⟨n, hn, hcard, a, b, ha, hb, hab, hgen⟩ := hG
  let : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  by_cases hX : X ≤ Subgroup.zpowers a
  · exact Or.inl (Subgroup.isCyclic_of_le hX)
  let A := (Subgroup.zpowers a).subgroupOf X
  let f : A →* Subgroup.zpowers a :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Subgroup.zpowers a => z.val) h))
  let : IsCyclic A := isCyclic_of_injective f hf
  have hidx : A.index=2 := cyclic_intersection_index_two hn hcard a b ha hb hab hgen X hX
  have hX8 : Nat.card X ∣ 8 := subgroup_card_dvd_eight hcard X hXcard
  apply small_inverted_cyclic_models A inferInstance hidx hX8
  intro x hx t ht
  have hAc : Nat.card A ∣ 4 := by
    have hm := A.index_mul_card
    rw [hidx] at hm
    obtain ⟨k,hk⟩ := hX8
    refine ⟨k,?_⟩
    nlinarith
  have ht4 : (t:G)^4=1 := by
    let u : A := ⟨t,ht⟩
    have hd : orderOf u ∣ 4 := (orderOf_dvd_natCard u).trans hAc
    exact congrArg (fun v : A => (v.val:G)) (orderOf_dvd_iff_pow_eq_one.mp hd)
  apply Subtype.ext
  apply small_rotation_inverted hn a b (x:G) (t:G) hab ?_ ht ht4
  have hb2 : b^2=1 := by rw [←hb]; exact pow_orderOf_eq_one b
  obtain ⟨i,_,hi|hi⟩ := normal_form a b _ _ (by positivity) ha hb2 hab hgen (x:G)
  · exfalso
    apply hx
    change (x:G) ∈ Subgroup.zpowers a
    rw [hi]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · exact ⟨i,hi⟩
end ABG.QuasiDihedral
