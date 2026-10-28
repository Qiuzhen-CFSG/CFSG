module
public import ABG.ChapterII.Section1.GeneratorNoncommutative
public import ABG.ChapterII.Section1.PresentationCalculus

/-!
# The normalizer of the canonical quaternion subgroup

For the semidihedral presentation of order `2^n`, `n ≥ 4`, the subgroup
`U = ⟨a^(2^(n-3)), ab⟩` has relative index two in its normalizer. This is
the canonical quaternion-subgroup normalizer calculation in ABG Chapter II,
§1, Lemma 1(ii), article p. 9, in
`refs/latex/alperin-brauer-gorenstein.tex` (included page-010). The canonical
quaternion model and transport to all quaternion subgroups are proved in
separate modules. Our order parameter is one larger than the article's.

Put `q = 2^(n-4)`, so `a` has order `8q`. The imported two-form closure
lemma shows that a rotation `a^i` lies in `U` exactly when `2q` divides `i`.
Conjugating `ab` by a normalizing rotation and cancelling `ab` then forces
`q` to divide its exponent. Conversely, `a^q` normalizes the two generators
of `U` and lies outside `U`. Splitting multiples of `q` by parity gives the
two normalizer cosets. Ambient normal forms reduce the outer coset to this
rotation calculation. The proof includes the boundary case `n = 4`.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

private theorem rotation_conj_outer (a c : G) (k : ℕ)
    (hconj : c*a*c⁻¹=a^k) (i : ℤ) :
    a^i*c*(a^i)⁻¹=a^((1-(k:ℤ))*i)*c := by
  rw [← zpow_neg, mul_assoc, move_zpow a c k hconj, ← mul_assoc, ← zpow_add]
  congr 2
  ring

private theorem rotation_mem_iff (a c : G) (q : ℕ)
    (ha : orderOf a=8*q) (hc : c ∉ Subgroup.zpowers a)
    (U : Subgroup G) (hau : a^(2*q) ∈ U)
    (hnf : ∀ x ∈ U, ∃ j : ℤ, x=(a^(2*q))^j ∨ x=(a^(2*q))^j*c)
    (i : ℤ) : a^i ∈ U ↔ (2*(q:ℤ)) ∣ i := by
  constructor
  · intro hi
    obtain ⟨j,hj|hj⟩ := hnf _ hi
    · have he : a^i=a^((2*(q:ℤ))*j) := by simpa only [← zpow_natCast, ← zpow_mul, Nat.cast_mul, Nat.cast_ofNat] using hj
      have hd := zpow_eq_zpow_iff_modEq.mp he
      rw [ha, Int.modEq_iff_dvd] at hd
      have hdiv : (2*(q:ℤ)) ∣ (8*(q:ℤ)) := ⟨4, by ring⟩
      have hx : (2*(q:ℤ)) ∣ (2*(q:ℤ))*j-i := by exact dvd_trans hdiv (by simpa using hd)
      have hh := dvd_sub (dvd_mul_right (2*(q:ℤ)) j) hx
      simpa only [sub_sub_cancel] using hh
    · apply False.elim
      apply hc
      have hm := (Subgroup.zpowers a).mul_mem
        ((Subgroup.zpowers a).inv_mem ((Subgroup.zpowers a).zpow_mem
          ((Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) (2*q)) j))
        ((Subgroup.zpowers a).zpow_mem (Subgroup.mem_zpowers a) i)
      have he : ((a^(2*q))^j)⁻¹*a^i=c := by rw [hj]; group
      simpa only [he] using hm
  · rintro ⟨j,rfl⟩
    have he : a^((2*(q:ℤ))*j)=(a^(2*q))^j := by
      rw [← zpow_natCast, ← zpow_mul]
      push_cast
      rfl
    rw [he]
    exact U.zpow_mem hau _

private theorem rotation_normalizer_divisible (a c : G) (q : ℕ) (hq : 0<q)
    (ha : orderOf a=8*q) (hc : c ∉ Subgroup.zpowers a)
    (hconj : c*a*c⁻¹=a^(4*q-1))
    (U : Subgroup G) (hau : a^(2*q) ∈ U) (hcu : c ∈ U)
    (hnf : ∀ x ∈ U, ∃ j : ℤ, x=(a^(2*q))^j ∨ x=(a^(2*q))^j*c)
    (i : ℤ) (hi : a^i ∈ Subgroup.normalizer (U:Set G)) : (q:ℤ) ∣ i := by
  have hm := (Subgroup.mem_normalizer_iff.mp hi c).mp hcu
  have hh := U.mul_mem hm (U.inv_mem hcu)
  rw [rotation_conj_outer a c _ hconj, mul_assoc, mul_inv_cancel, mul_one] at hh
  have hd := (rotation_mem_iff a c q ha hc U hau hnf _).mp hh
  have hk : (4*q-1:ℕ) = (4:ℤ)*q-1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [hk] at hd
  have he : (1-(4*(q:ℤ)-1))*i = 2*(i-2*(q:ℤ)*i) := by ring
  rw [he] at hd
  have hd' : (q:ℤ) ∣ i-2*(q:ℤ)*i := (mul_dvd_mul_iff_left (by norm_num : (2:ℤ)≠0)).mp hd
  have ht : (q:ℤ) ∣ 2*(q:ℤ)*i := ⟨2*i, by ring⟩
  have := dvd_add hd' ht
  simpa only [sub_add_cancel] using this

private theorem normalizer_index_from_forms [Finite G] (a c : G) (q : ℕ) (hq : 0<q)
    (ha : orderOf a=8*q) (hc : c ∉ Subgroup.zpowers a)
    (hconj : c*a*c⁻¹=a^(4*q-1))
    (U : Subgroup G) (hU : U=Subgroup.closure ({a^(2*q),c}:Set G))
    (hnf : ∀ x ∈ U, ∃ j : ℤ, x=(a^(2*q))^j ∨ x=(a^(2*q))^j*c)
    (hGnf : ∀ x : G, ∃ i : ℤ, x=a^i ∨ x=a^i*c) :
    U.relIndex (Subgroup.normalizer (U:Set G))=2 := by
  have hau : a^(2*q) ∈ U := by rw [hU]; exact Subgroup.subset_closure (by simp)
  have hcu : c ∈ U := by rw [hU]; exact Subgroup.subset_closure (by simp)
  have hmem := rotation_mem_iff a c q ha hc U hau hnf
  have hk : (4*q-1:ℕ) = (4:ℤ)*q-1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hqN : a^(q:ℤ) ∈ Subgroup.normalizer (U:Set G) := by
    apply Subgroup.mem_normalizer_fintype
    have hmap : U ≤ U.comap (MulAut.conj (a^(q:ℤ))).toMonoidHom := by
      rw [hU]
      apply (Subgroup.closure_le _).mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · subst x
        change a^(q:ℤ)*a^(2*q)*(a^(q:ℤ))⁻¹ ∈ Subgroup.closure ({a^(2*q),c}:Set G)
        have he : a^(q:ℤ)*a^(2*q)*(a^(q:ℤ))⁻¹ = a^(2*q) := by
          rw [← zpow_natCast, ← zpow_neg, ← zpow_add, ← zpow_add]
          congr 1
          ring
        rw [he]
        exact Subgroup.subset_closure (by simp)
      · subst x
        change a^(q:ℤ)*c*(a^(q:ℤ))⁻¹ ∈ Subgroup.closure ({a^(2*q),c}:Set G)
        rw [rotation_conj_outer a c _ hconj]
        rw [← hU]
        apply U.mul_mem _ hcu
        apply (hmem _).mpr
        rw [hk]
        exact ⟨1-2*(q:ℤ), by ring⟩
    intro x hx
    exact hmap hx
  have hqnot : a^(q:ℤ) ∉ U := by
    intro hh
    have hd := (hmem _).mp hh
    have hd' : 2*q ∣ q := by exact_mod_cast hd
    have hl := Nat.le_of_dvd hq hd'
    omega
  have hrot (i : ℤ) (hi : a^i ∈ Subgroup.normalizer (U:Set G)) :
      a^(q:ℤ)*a^i ∈ U ∨ a^i ∈ U := by
    obtain ⟨j,rfl⟩ := rotation_normalizer_divisible a c q hq ha hc hconj U hau hcu hnf i hi
    have hj : (2:ℤ) ∣ j ∨ (2:ℤ) ∣ j+1 := by omega
    rcases hj with ⟨t,ht⟩ | ⟨t,ht⟩
    · right
      apply (hmem _).mpr
      exact ⟨t, by rw [ht]; ring⟩
    · left
      rw [← zpow_add]
      apply (hmem _).mpr
      refine ⟨t,?_⟩
      calc
        (q:ℤ)+(q:ℤ)*j = (q:ℤ)*(j+1) := by ring
        _ = (2*(q:ℤ))*t := by rw [ht]; ring
  apply Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨a^(q:ℤ), hqN, hqnot, ?_⟩
  intro x hx
  obtain ⟨i,rfl|rfl⟩ := hGnf x
  · exact hrot i hx
  · have hh : a^i ∈ Subgroup.normalizer (U:Set G) := by
      have hcN := U.le_normalizer hcu
      have := (Subgroup.normalizer (U:Set G)).mul_mem hx
        ((Subgroup.normalizer (U:Set G)).inv_mem hcN)
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using this
    rcases hrot i hh with hi | hi
    · left
      simpa only [mul_assoc] using U.mul_mem hi hcu
    · right
      exact U.mul_mem hi hcu

/-- The canonical quaternion subgroup has index two in its normalizer. -/
public theorem quaternion_representative_normalizer {n : ℕ} (hn : 4≤n) (a b : G)
    (hcard : Nat.card G=2^n) (ha : orderOf a=2^(n-1)) (hb : orderOf b=2)
    (hconj : b*a*b⁻¹=a^(2^(n-2)-1))
    (hgen : Subgroup.closure ({a,b}:Set G)=⊤) :
    (Subgroup.closure ({a^(2^(n-3)),a*b}:Set G)).relIndex
      (Subgroup.normalizer (Subgroup.closure ({a^(2^(n-3)),a*b}:Set G):Set G))=2 := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let q := 2^(n-4)
  have hq : 0<q := by dsimp [q]; positivity
  have h2q : 2^(n-3)=2*q := by
    dsimp [q]
    rw [show n-3=(n-4)+1 by omega,pow_succ,Nat.mul_comm]
  have h4q : 2^(n-2)=4*q := by
    dsimp [q]
    rw [show n-2=(n-4)+2 by omega,pow_add]
    ring
  have h8q : 2^(n-1)=8*q := by
    dsimp [q]
    rw [show n-1=(n-4)+3 by omega,pow_add]
    ring
  have hbn : b ∉ Subgroup.zpowers a := by
    rintro ⟨i,rfl⟩
    exact generators_not_commute hn ha hconj (Commute.self_zpow a i)
  have hcn : a*b ∉ Subgroup.zpowers a := by
    intro hh
    have := (Subgroup.zpowers a).mul_mem ((Subgroup.zpowers a).inv_mem
      (Subgroup.mem_zpowers a)) hh
    exact hbn (by simpa only [← mul_assoc,inv_mul_cancel,one_mul] using this)
  have hca : (a*b)*a*(a*b)⁻¹=a^(4*q-1) := by
    calc
      (a*b)*a*(a*b)⁻¹=a*(b*a*b⁻¹)*a⁻¹ := by group
      _ = a^(4*q-1) := by rw [hconj,h4q,(Commute.self_pow a _).eq]; group
  rw [h2q]
  apply normalizer_index_from_forms a (a*b) q hq (by rw [ha,h8q]) hcn hca _ rfl
  · intro x hx
    have hsq : (a*b)^2=(a^(2*q))^(2:ℤ) := by
      have hh := outer_square hn a b hb hconj 1
      rw [pow_one,mul_one,h4q] at hh
      rw [hh,zpow_ofNat,← pow_mul]
      congr 1
      ring
    have hpow : (a*b)*a^(2*q)*(a*b)⁻¹=(a^(2*q))^(4*q-1) := by
      have hh := congrArg (fun x : G => x^(2*q)) hca
      rw [← MulAut.conj_apply,← map_pow,MulAut.conj_apply] at hh
      simpa only [← pow_mul,Nat.mul_comm] using hh
    exact square_normal_form_int (a^(2*q)) (a*b) (4*q-1) 2 hsq hpow x hx
  · intro x
    obtain ⟨i,_,hi|hi⟩ := normal_form a b _ _ (by positivity) ha
      (by rw [← hb]; exact pow_orderOf_eq_one b) hconj hgen x
    · exact ⟨i,Or.inl (by simpa only [zpow_natCast] using hi)⟩
    · refine ⟨(i:ℤ)-1,Or.inr ?_⟩
      rw [hi,← zpow_natCast]
      have he : a^((i:ℤ)-1)*(a*b)=a^(i:ℤ)*b := by
        rw [zpow_sub,zpow_one]
        group
      exact he.symm

end ABG.QuasiDihedral
