module

public import ABG.ChapterII.Section2.LinearWreathedSylow
public import ABG.ChapterII.Section2.UnitaryWreathedSylow
public import ABG.ChapterII.Section2.UnitarySemidihedralSylow
public import Theory.SpecificGroups.GL2.SemidihedralSylow

/-!
# Sylow presentations in full GL₂ and GU₂

Every Sylow two-subgroup of GL₂ over an odd finite field, or of the actual
GU₂(q) over GF(q²) with q-Frobenius conjugation, is semidihedral or wreathed.
The predicates in the conclusions are the exact generator presentations,
including cardinality and generation, rather than recognition assumptions.

For GL₂ with q congruent to three modulo four, use the explicit quadratic
torus construction. In the remaining cases, every two-subgroup lies in the
appropriate determinant level: its determinant has two-power order dividing
q−1 (linear) or q+1 (unitary). Restricting an arbitrary ambient Sylow subgroup
to that level and applying Sylow conjugacy transports the already constructed
matrix presentations. The level constructions discharge their order formulas;
no additional full-group order formula is needed for this restriction argument.

Source: Alperin–Brauer–Gorenstein II.2 Lemma 1, article p. 17; these full-group
extensions are used for Aschbacher–Smith A.3.21(b), printed p. 55.
-/

namespace ABG

private theorem two_power_order_dvd {G : Type*} [Group G] {H : Type*} [Group H]
    (T : Subgroup G) (hT : IsPGroup 2 T) (f : G →* H)
    (a : T) (r m : ℕ) (hm : Odd m)
    (hd : orderOf (f a.val) ∣ 2 ^ r * m) : orderOf (f a.val) ∣ 2 ^ r := by
  obtain ⟨k, hk⟩ := hT.exists_orderOf_dvd_pow a
  have hd2 : orderOf (f a.val) ∣ 2 ^ k :=
    (orderOf_map_dvd f a.val).trans (by simpa only [Subgroup.orderOf_coe] using hk)
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  rw [hj] at hd ⊢
  exact (hm.coprime_two_left.pow_left j).dvd_mul_right.mp hd

private theorem exact_two_part_ge_two (m : ℕ) (hm : m ≠ 0) (hfour : 4 ∣ m) :
    ∃ r d : ℕ, 2 ≤ r ∧ Odd d ∧ m = 2 ^ r * d := by
  obtain ⟨r, d, hd, he⟩ := Nat.exists_eq_two_pow_mul_odd hm
  refine ⟨r, d, ?_, hd, he⟩
  by_contra hr
  have : r = 0 ∨ r = 1 := by omega
  obtain ⟨k, hk⟩ := hd
  rcases this with rfl | rfl <;> simp only [pow_zero, pow_one, one_mul] at he <;> omega

/-- Every Sylow two-subgroup of the full GL₂ over an odd finite field has
an actual semidihedral or wreathed presentation. -/
public theorem full_GL2_sylow_shape (F : Type*) [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (T : Sylow 2 (GL (Fin 2) F)) :
    Stellmacher.IsSemidihedralGroup T ∨ IsWreathedGroup T := by
  have hmod : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    have := Nat.odd_iff.mp hF
    omega
  rcases hmod with hmod | hmod
  · obtain ⟨r, d, hr, hd, he⟩ := exact_two_part_ge_two (Nat.card F - 1)
      (by have := Finite.one_lt_card (α := F); omega) (by omega)
    have hdiv : 2 ^ r ∣ Nat.card F - 1 := ⟨d, he⟩
    have hodd : Odd ((Nat.card F - 1) / 2 ^ r) := by
      rw [he, Nat.mul_div_cancel_left _ (by positivity)]
      exact hd
    obtain ⟨P, hP, _⟩ := determinantTwoPower_wreathed_sylow F r hr hdiv hodd
    have hT : (T : Subgroup (GL (Fin 2) F)) ≤
        Matrix.GeneralLinearGroup.determinantTwoPower F r := by
      intro a ha
      rw [Matrix.GeneralLinearGroup.mem_determinantTwoPower_iff_orderOf_dvd]
      apply two_power_order_dvd _ T.isPGroup' Matrix.GeneralLinearGroup.det ⟨a, ha⟩ r d hd
      rw [← he, ← Nat.card_units F]
      exact orderOf_dvd_natCard _
    let e : T ≃* P := (Subgroup.subgroupOfEquivOfLe hT).symm.trans ((T.subtype hT).equiv P)
    exact Or.inr ⟨r, wreathed_equiv e.symm hP⟩
  · obtain ⟨P, n, hn, hc, a, b, ha, hb, hab, hgen, _⟩ :=
      Matrix.GeneralLinearGroup.exists_semidihedral_sylow F hmod
    exact Or.inl (semidihedral_equiv (P.equiv T) ⟨n, hn, hc, a, b, ha, hb, hab, hgen⟩)

/-- Every Sylow two-subgroup of the actual GU₂(q), over GF(q²) with
q-Frobenius conjugation, has the required concrete presentation. -/
public theorem full_GU2_sylow_shape (p f : ℕ) [Fact p.Prime] (hp : Odd p) (hf : f ≠ 0)
    (T : Sylow 2 (GU2 p f hf)) :
    Stellmacher.IsSemidihedralGroup T ∨ IsWreathedGroup T := by
  let q := p ^ f
  have hq : Odd q := hp.pow
  have hqpos : 0 < q := pow_pos (Fact.out : p.Prime).pos _
  have hqbig : 1 < q := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
    have := Nat.odd_iff.mp hq
    omega
  let detU := (Matrix.GeneralLinearGroup.det (n := Fin 2)
    (R := GaloisField p (2 * f))).comp (unitaryForm 2 p f hf).unitarySubgroup.subtype
  rcases hmod with hmod | hmod
  · obtain ⟨r, d, hr, hd, he⟩ := exact_two_part_ge_two (q - 1) (by omega) (by omega)
    have hdiv : 2 ^ r ∣ q - 1 := ⟨d, he⟩
    have hodd : Odd ((q - 1) / 2 ^ r) := by
      rw [he, Nat.mul_div_cancel_left _ (by positivity)]
      exact hd
    obtain ⟨P, _, hP, _⟩ := SU2Level_semidihedral_sylow p f hp hf r hr hdiv hodd
    have hT : (T : Subgroup (GU2 p f hf)) ≤ SU2Level p f hf 1 := by
      intro a ha
      rw [mem_SU2Level_iff_orderOf_dvd]
      apply two_power_order_dvd _ T.isPGroup' detU ⟨a, ha⟩ 1 ((q + 1) / 2)
        (by rw [Nat.odd_iff]; omega)
      have heq : 2 ^ 1 * ((q + 1) / 2) = q + 1 := by omega
      rw [heq]
      exact GU2_det_orderOf_dvd p f hf a
    let e : T ≃* P := (Subgroup.subgroupOfEquivOfLe hT).symm.trans ((T.subtype hT).equiv P)
    exact Or.inl (semidihedral_equiv e.symm hP)
  · obtain ⟨r, d, hr, hd, he⟩ := exact_two_part_ge_two (q + 1) (by omega) (by omega)
    have hdiv : 2 ^ r ∣ q + 1 := ⟨d, he⟩
    have hodd : Odd ((q + 1) / 2 ^ r) := by
      rw [he, Nat.mul_div_cancel_left _ (by positivity)]
      exact hd
    obtain ⟨P, hP, _⟩ := SU2Level_wreathed_sylow p f hp hf r hr hdiv hodd
    have hT : (T : Subgroup (GU2 p f hf)) ≤ SU2Level p f hf r := by
      intro a ha
      rw [mem_SU2Level_iff_orderOf_dvd]
      apply two_power_order_dvd _ T.isPGroup' detU ⟨a, ha⟩ r d hd
      rw [← he]
      exact GU2_det_orderOf_dvd p f hf a
    let e : T ≃* P := (Subgroup.subgroupOfEquivOfLe hT).symm.trans ((T.subtype hT).equiv P)
    exact Or.inr ⟨r, wreathed_equiv e.symm hP⟩
end ABG
