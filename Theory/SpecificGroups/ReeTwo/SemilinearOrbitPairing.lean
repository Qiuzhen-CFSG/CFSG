module

public import Theory.SpecificGroups.ReeTwo.SemilinearExtensionData
public import Theory.GroupTheory.Commutator.ThirdHom
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The intrinsic central pairing on the semilinear orbit frame

The root displacement gives a central bilinear pairing, via the class-three
commutator homomorphism. It vanishes on the derived subgroup and on the root.
After normalizing the native symmetry at the seed, simultaneous shifts and
doubling of five-orbit indices make all off-diagonal entries equal. The
involutory seed gives zero diagonal entries. If the common off-diagonal entry
were trivial, orbit generation and `[R, ⟨t⟩] = D` would put the order-32 derived
subgroup in the order-two center. Thus every off-diagonal entry is the given
central involution. Expanding the four prescribed orbit words yields the exact
antidiagonal pairing, preserving both the root and the central involution.

Sources: Thompson VI, pp.629–630; Parrott (1972), pp.672–674;
Shinoda (1975), pp.81–82. This is intrinsic commutator calculus and uses no
quotient-coordinate calculation or model recognition.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace ReeTwo
variable {K : Type*} [Group K]
private theorem rightComm_eq_comm_of_central (x y : K)
    (hc : ⁅x,y⁆ ∈ center K) : rightComm x y = ⁅x,y⁆ := by
  calc
    rightComm x y = (x*y)⁻¹ * ⁅x,y⁆ * (x*y) := by
      simp only [rightComm, commutatorElement_def]
      group
    _ = ⁅x,y⁆ := by
      rw [Subgroup.mem_center_iff.mp hc]
      group

private theorem exists_rootDisplacementPairing
    (hc : ⁅commutator K, (⊤ : Subgroup K)⁆ ≤ center K) (t : K) :
    ∃ P : K →* (K →* center K),
      ∀ x y, (P x y : K) = rightComm x (rightComm y t) := by
  obtain ⟨f, hf⟩ := Subgroup.exists_third_commutator_hom hc
  let P : K →* (K →* center K) := {
    toFun x := {
      toFun y := (f y t x)⁻¹
      map_one' := by
        simp only [map_one, MonoidHom.one_apply, inv_one]
      map_mul' y z := by
        simp only [map_mul, MonoidHom.mul_apply, mul_inv_rev]
        exact mul_comm _ _ }
    map_one' := by
      apply MonoidHom.ext
      intro y
      change (f y t 1)⁻¹ = 1
      rw [map_one, inv_one]
    map_mul' x y := by
      apply MonoidHom.ext
      intro z
      change (f z t (x*y))⁻¹ = (f z t x)⁻¹ * (f z t y)⁻¹
      rw [map_mul, mul_inv_rev, mul_comm] }
  refine ⟨P, fun x y => ?_⟩
  have he : f y⁻¹ t⁻¹ x = f y t x := by
    simp only [map_inv, MonoidHom.inv_apply, inv_inv]
  have hmem : ⁅rightComm y t, x⁆ ∈ center K := by
    rw [← show ⁅y⁻¹,t⁻¹⁆ = rightComm y t from by simp [rightComm, commutatorElement_def]]
    rw [← hf]
    exact (f y⁻¹ t⁻¹ x).property
  have hswap : ⁅x,rightComm y t⁆ = ⁅rightComm y t,x⁆⁻¹ := by
    simp [commutatorElement_def, mul_assoc]
  rw [rightComm_eq_comm_of_central x (rightComm y t) (hswap ▸ (center K).inv_mem hmem), hswap]
  change (f y t x : K)⁻¹ = _
  rw [← he, hf]
  congr 2
  simp [rightComm, commutatorElement_def]

variable {A : Type*} [Group A]
variable {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}

/-- The central bilinear pairing obtained by taking displacement by the root. -/
noncomputable def SemilinearExtensionData.rootPairing
    (h : SemilinearExtensionData ρ R t z b σ) : K →* (K →* center K) :=
  (exists_rootDisplacementPairing (by
    rw [← h.derived_eq, h.derived_commutator, h.center_eq]) t).choose

theorem SemilinearExtensionData.rootPairing_apply
    (h : SemilinearExtensionData ρ R t z b σ) (x y : K) :
    (h.rootPairing x y : K) = rightComm x (rightComm y t) :=
  (exists_rootDisplacementPairing (by
    rw [← h.derived_eq, h.derived_commutator, h.center_eq]) t).choose_spec x y

private theorem rightComm_mem_derived (x y : K) : rightComm x y ∈ commutator K := by
  simpa [rightComm, commutatorElement_def, commutator_def] using
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x⁻¹) (Subgroup.mem_top y⁻¹))

private theorem derived_inv (h : SemilinearExtensionData ρ R t z b σ)
    {d : K} (hd : d ∈ commutator K) : d⁻¹ = d := by
  have := h.derived_elementary
  have hd2 : d ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) d
    (h.derived_eq.symm ▸ hd)
  exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hd2)

theorem SemilinearExtensionData.rootPairing_root_left
    (h : SemilinearExtensionData ρ R t z b σ) (y : K) : h.rootPairing t y = 1 := by
  apply Subtype.ext
  rw [h.rootPairing_apply]
  have hc := Subgroup.mem_centralizer_iff.mp h.root_centralizes (rightComm y t)
    (h.derived_eq.symm ▸ rightComm_mem_derived y t)
  change rightComm t (rightComm y t) = 1
  simpa [rightComm, commutatorElement_def] using (show Commute t (rightComm y t) from hc.symm).inv_inv.commutator_eq

theorem SemilinearExtensionData.rootPairing_root_right
    (h : SemilinearExtensionData ρ R t z b σ) (x : K) : h.rootPairing x t = 1 := by
  apply Subtype.ext
  rw [h.rootPairing_apply]
  simp [rightComm]

theorem SemilinearExtensionData.rootPairing_derived_left
    (h : SemilinearExtensionData ρ R t z b σ) {d : K} (hd : d ∈ commutator K)
    (y : K) : h.rootPairing d y = 1 := by
  have he := Abelianization.commutator_subset_ker h.rootPairing hd
  exact congrArg (fun f : K →* center K => f y) he

theorem SemilinearExtensionData.rootPairing_derived_right
    (h : SemilinearExtensionData ρ R t z b σ) (x : K) {d : K}
    (hd : d ∈ commutator K) : h.rootPairing x d = 1 :=
  Abelianization.commutator_subset_ker (h.rootPairing x) hd

theorem SemilinearExtensionData.rootPairing_congr
    (h : SemilinearExtensionData ρ R t z b σ) {x x' y y' : K}
    (hx : x / x' ∈ commutator K) (hy : y / y' ∈ commutator K) :
    h.rootPairing x y = h.rootPairing x' y' := by
  have hleft := h.rootPairing_derived_left hx y
  have hright := h.rootPairing_derived_right x' hy
  simp only [map_div, MonoidHom.div_apply, div_eq_one] at hleft hright
  exact hleft.trans hright

theorem SemilinearExtensionData.rootPairing_self_of_square
    (h : SemilinearExtensionData ρ R t z b σ) {x : K} (hx : x ^ 2 = 1) :
    h.rootPairing x x = 1 := by
  apply Subtype.ext
  rw [h.rootPairing_apply]
  have hd := derived_inv h (rightComm_mem_derived x t)
  change rightComm x (rightComm x t) = 1
  rw [rightComm, hd]
  calc
    _ = rightComm (x ^ 2) t := by simp only [rightComm, pow_two]; group
    _ = 1 := by rw [hx]; simp [rightComm]


variable [Finite K]

theorem SemilinearExtensionData.map_center
    (h : SemilinearExtensionData ρ R t z b σ) (φ : MulAut K) (c : center K) :
    φ (c : K) = c := by
  have hZ : Nat.card (center K) = 2 := by rw [h.center_eq, h.center_card]
  let : IsCyclic (center K) := isCyclic_of_prime_card hZ
  have hAut : Nat.card (MulAut (center K)) = 1 := by
    rw [IsCyclic.card_mulAut, hZ]
    decide
  let : Subsingleton (MulAut (center K)) := (Nat.card_eq_one_iff_unique.mp hAut).1
  exact congrArg (fun f : MulAut (center K) => (f c : K))
    (show Subgroup.centerCongr φ = 1 from Subsingleton.elim _ _)

theorem SemilinearExtensionData.rootPairing_natural
    (h : SemilinearExtensionData ρ R t z b σ) (φ : MulAut K)
    (hφ : φ t = t ∨ φ t = t⁻¹) (x y : K) :
    h.rootPairing (φ x) (φ y) = h.rootPairing x y := by
  apply Subtype.ext
  rw [h.rootPairing_apply, h.rootPairing_apply]
  have ht : t ^ 2 ∈ center K := by rw [h.root_square, h.center_eq]; exact h.central_mem
  calc
    rightComm (φ x) (rightComm (φ y) t) = φ (rightComm x (rightComm y t)) := by
      rw [← map_root_rightComm φ t ht hφ y]
      simp only [rightComm, map_mul, map_inv]
    _ = rightComm x (rightComm y t) := by
      rw [← h.rootPairing_apply]
      exact h.map_center φ _

theorem SemilinearExtensionData.rootPairing_shift
    (h : SemilinearExtensionData ρ R t z b σ) (c a d : A) :
    h.rootPairing (ρ (c*a) b) (ρ (c*d) b) = h.rootPairing (ρ a b) (ρ d b) := by
  simpa only [map_mul, MulAut.mul_apply] using
    h.rootPairing_natural (ρ c) (Or.inl (h.root_fixed c)) (ρ a b) (ρ d b)

theorem SemilinearExtensionData.rootPairing_double
    (h : SemilinearExtensionData ρ R t z b σ)
    (hseed : σ b / (b : K) ∈ (commutator R).map R.subtype) (a d : A) :
    h.rootPairing (ρ (a^2) b) (ρ (d^2) b) = h.rootPairing (ρ a b) (ρ d b) := by
  rw [← h.rootPairing_natural σ h.symmetry_root (ρ a b) (ρ d b)]
  apply Eq.symm
  apply h.rootPairing_congr
  · rw [← h.derived_eq]; exact h.symmetry_orbit_coset hseed a
  · rw [← h.derived_eq]; exact h.symmetry_orbit_coset hseed d


omit [Finite K] in
theorem SemilinearExtensionData.frameTail_eq_displacement
    (h : SemilinearExtensionData ρ R t z b σ) (a : Fin 4 → K) (i : Fin 4) :
    frameTail a t i = rightComm (a i) t := by
  have he (x : K) : rightComm t x = rightComm x t := by
    rw [← derived_inv h (rightComm_mem_derived x t)]
    simp [rightComm, mul_assoc]
  fin_cases i <;> simp [frameTail, he]

omit [Finite K] in
theorem SemilinearExtensionData.orbitFrame_pairing_of_orbit
    (h : SemilinearExtensionData ρ R t z b σ) (g : A)
    (hpair : ∀ i j : Fin 4,
      rightComm (ρ (g ^ i.val) b) (rightComm (ρ (g ^ j.val) b) t) =
        if i = j then 1 else z) :
    ∀ i j : Fin 4,
      rightComm (orbitFrame ρ b g t i) (frameTail (orbitFrame ρ b g t) t j) =
        if i.val + j.val = 3 then z else 1 := by
  let v (i : Fin 4) : K := ρ (g ^ i.val) b
  have hp (i j : Fin 4) : (h.rootPairing (v i) (v j) : K) =
      if i = j then 1 else z := by
    rw [h.rootPairing_apply]
    exact hpair i j
  have ha : orbitFrame ρ b g t =
      ![v 0, v 2 * v 3 * t, v 1 * v 2 * t, v 0 * v 1 * v 2 * v 3] := by
    ext i
    fin_cases i <;> simp [orbitFrame, v]
  have hz : z*z = 1 := by
    have he := pow_orderOf_eq_one z
    simpa only [h.central_order, pow_two] using he
  intro i j
  rw [h.frameTail_eq_displacement, ← h.rootPairing_apply, ha]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.ext_iff, map_mul, MonoidHom.mul_apply, hp,
      h.rootPairing_root_left, h.rootPairing_root_right, ← mul_assoc, hz]


private theorem five_square_invariant [Finite A] {C : Type*} (F : A → C)
    (hA : Nat.card A = 5) (g : A) (hg : g ≠ 1)
    (hs : ∀ a, F (a ^ 2) = F a) (a : A) (ha : a ≠ 1) : F a = F g := by
  classical
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf g = 5 :=
    (orderOf_eq_card_of_zpowers_eq_top (zpowers_eq_top_of_prime_card hA hg)).trans hA
  have hm := (mem_zpowers_iff_mem_range_orderOf (x := g) (y := a)).mp
    (mem_zpowers_of_prime_card hA hg)
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  have hn5 : n < 5 := by simpa only [Finset.mem_range, hord] using hn
  have h2 : F (g ^ 2) = F g := hs g
  have h4 : F (g ^ 4) = F g := by
    simpa only [← pow_mul] using (hs (g ^ 2)).trans h2
  have h8 : F (g ^ 8) = F g := by
    simpa only [← pow_mul] using (hs (g ^ 4)).trans h4
  have hp8 : g ^ 8 = g ^ 3 := by
    simpa only [hord] using (pow_mod_orderOf g 8).symm
  have h3 : F (g ^ 3) = F g := hp8 ▸ h8
  interval_cases n
  · exact (ha (pow_zero g)).elim
  · simp only [pow_one]
  · exact h2
  · exact h3
  · exact h4

/-- Shifting and doubling indices makes all distinct orbit pairs equal. -/
theorem SemilinearExtensionData.rootPairing_off_diagonal [Finite A]
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (hg : g ≠ 1)
    (a d : A) (had : a ≠ d) :
    h.rootPairing (ρ a b) (ρ d b) = h.rootPairing b (ρ g b) := by
  obtain ⟨c, hc, hseed⟩ := exists_seed_normalized_symmetry ρ R t z b σ h
  have hdouble (a d : A) :
      h.rootPairing (ρ (a^2) b) (ρ (d^2) b) = h.rootPairing (ρ a b) (ρ d b) := by
    apply Subtype.ext
    rw [h.rootPairing_apply, h.rootPairing_apply, ← hc.rootPairing_apply, ← hc.rootPairing_apply]
    exact congrArg Subtype.val (hc.rootPairing_double hseed a d)
  have hs (a : A) : h.rootPairing b (ρ (a^2) b) = h.rootPairing b (ρ a b) := by
    simpa only [one_pow, map_one, MulAut.one_apply] using hdouble 1 a
  calc
    h.rootPairing (ρ a b) (ρ d b) = h.rootPairing b (ρ (a⁻¹*d) b) := by
      simpa only [inv_mul_cancel, map_one, MulAut.one_apply] using
        (h.rootPairing_shift a⁻¹ a d).symm
    _ = h.rootPairing b (ρ g b) := five_square_invariant
      (fun a => h.rootPairing b (ρ a b)) h.actor_card g hg hs _
      (fun he => had (inv_mul_eq_one.mp he))


omit [Finite K] in
private theorem commute_of_rightComm_eq_one {x y : K} (h : rightComm x y = 1) :
    Commute x y := by
  have hc : Commute x⁻¹ y⁻¹ := commutatorElement_eq_one_iff_mul_comm.mp (by
    simpa only [rightComm, commutatorElement_def, inv_inv] using h)
  simpa only [inv_inv] using hc.inv_inv

/-- Trivial orbit pairing would force the order-32 derived subgroup into the
order-two center, since the orbit generates the residual. -/
theorem SemilinearExtensionData.rootPairing_off_diagonal_ne_one [Finite A]
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (hg : g ≠ 1) :
    h.rootPairing b (ρ g b) ≠ 1 := by
  intro hzero
  have horbit (a d : A) : h.rootPairing (ρ a b) (ρ d b) = 1 := by
    by_cases had : a = d
    · subst d
      apply h.rootPairing_self_of_square
      have hb : (b : K) ^ 2 = 1 := congrArg Subtype.val h.seed_square
      rw [← map_pow, hb, map_one]
    · rw [h.rootPairing_off_diagonal g hg a d had, hzero]
  have hR (a : A) : R ≤ (h.rootPairing (ρ a b)).ker := by
    conv_lhs => rw [← h.seed_generates]
    apply (closure_le _).mpr
    rintro _ ⟨d, rfl⟩
    exact horbit a d
  have hK (a : A) : (⊤ : Subgroup K) ≤ (h.rootPairing (ρ a b)).ker := by
    rw [← h.root_generates]
    exact sup_le (hR a) (zpowers_le.mpr (h.rootPairing_root_right _))
  have hleftR : R ≤ h.rootPairing.ker := by
    conv_lhs => rw [← h.seed_generates]
    apply (closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    apply MonoidHom.ext
    intro y
    exact hK a (mem_top y)
  have ht : t ∈ h.rootPairing.ker := by
    apply MonoidHom.ext
    intro y
    exact h.rootPairing_root_left y
  have htop : (⊤ : Subgroup K) ≤ h.rootPairing.ker := by
    rw [← h.root_generates]
    exact sup_le hleftR (zpowers_le.mpr ht)
  have hall (x y : K) : h.rootPairing x y = 1 :=
    congrArg (fun f : K →* center K => f y) (htop (mem_top x))
  have hdisplacement (y : K) : rightComm y t ∈ center K := by
    apply mem_center_iff.mpr
    intro x
    apply (commute_of_rightComm_eq_one _).eq
    have he := congrArg Subtype.val (hall x y)
    rwa [h.rootPairing_apply] at he
  let q := QuotientGroup.mk' (center K)
  have htq : q t ∈ center (K ⧸ center K) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) y
    apply (commute_of_rightComm_eq_one _).eq
    have he : q (rightComm x t) = 1 :=
      (QuotientGroup.eq_one_iff (N := center K) _).mpr (hdisplacement x)
    simpa only [rightComm, map_mul, map_inv] using he
  have hD : (commutator R).map R.subtype ≤ center K := by
    rw [← QuotientGroup.ker_mk' (center K), ← h.root_commutator]
    apply commutator_le.mpr
    intro r hr v hv
    change q ⁅r,v⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    have hv' : q v ∈ center (K ⧸ center K) :=
      (zpowers_le.mpr (show t ∈ (center (K ⧸ center K)).comap q from htq)) hv
    exact mem_center_iff.mp hv' (q r)
  have hcard := Subgroup.card_le_of_le hD
  rw [h.derived_card, h.center_eq, h.center_card] at hcard
  omega

/-- Distinct five-orbit vectors pair to the prescribed central involution. -/
theorem SemilinearExtensionData.rootPairing_orbit [Finite A] [DecidableEq A]
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (hg : g ≠ 1)
    (a d : A) :
    (h.rootPairing (ρ a b) (ρ d b) : K) = if a = d then 1 else z := by
  classical
  by_cases had : a = d
  · subst d
    have hb : (b : K) ^ 2 = 1 := congrArg Subtype.val h.seed_square
    have ha : (ρ a (b : K)) ^ 2 = 1 := by rw [← map_pow, hb, map_one]
    rw [if_pos rfl, h.rootPairing_self_of_square ha]
    rfl
  · rw [if_neg had, h.rootPairing_off_diagonal g hg a d had]
    have hZ : Nat.card (center K) = 2 := by rw [h.center_eq, h.center_card]
    obtain ⟨c, _, hu⟩ := (Nat.card_eq_two_iff' (1 : center K)).mp hZ
    have hzmem : z ∈ center K := h.center_eq.symm ▸ h.central_mem
    have hz : (⟨z, hzmem⟩ : center K) ≠ 1 := by
      intro he
      have he' : z = 1 := congrArg Subtype.val he
      have ho := h.central_order
      rw [he', orderOf_one] at ho
      omega
    exact congrArg Subtype.val
      ((hu _ (h.rootPairing_off_diagonal_ne_one g hg)).trans (hu _ hz).symm)

/-- The native symmetry forces the antidiagonal central pairing on the four
prescribed orbit words, with the original root and central involution. -/
theorem SemilinearExtensionData.orbitFrame_pairing [Finite A]
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (hg : g ≠ 1) :
    ∀ i j : Fin 4,
      rightComm (orbitFrame ρ b g t i) (frameTail (orbitFrame ρ b g t) t j) =
        if i.val + j.val = 3 then z else 1 := by
  classical
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf g = 5 :=
    (orderOf_eq_card_of_zpowers_eq_top (zpowers_eq_top_of_prime_card h.actor_card hg)).trans
      h.actor_card
  apply h.orbitFrame_pairing_of_orbit g
  intro i j
  rw [← h.rootPairing_apply, h.rootPairing_orbit g hg]
  have he : g ^ i.val = g ^ j.val ↔ i = j := by
    constructor
    · intro hp
      apply Fin.ext
      exact pow_injOn_Iio_orderOf (by change i.val < orderOf g; rw [hord]; omega)
        (by change j.val < orderOf g; rw [hord]; omega) hp
    · rintro rfl
      rfl
  simp only [he]

end ReeTwo
