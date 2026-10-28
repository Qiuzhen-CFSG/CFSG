module

public import Theory.SpecificGroups.Classical.DefiningLocalRank.UnitaryCentralizer.Geometry
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.PrimeRankElementary
public import ABG.ChapterII.Section2.UnitaryCard

/-!
# Defining-prime rank of arbitrary PSU₃ involution centralizers

Lift the original projective involution through the central scalar kernel of
exponent three. Its full SU₃ centralizer maps onto the original projective
centralizer. Hermitian form transport and the two-plus-one eigenbasis identify
this covering centralizer with the actual GU₂(p^e). The known order formula has
p-part exactly p^e, so every elementary abelian p-subgroup of the projective
centralizer has order at most p^e.

All nondegenerate ternary forms and all positive exponents are covered, including
characteristic three. No recognition or simplicity hypothesis is required.
Source: Aschbacher–Smith A.2.17, printed p.39, and the involution centralizer
calculation in A.3.21(a), printed p.55; Huppert II.10.4 for form transport.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.Classical.DefiningLocalRank.UnitaryCentralizer
variable {F : Type*} [Field F] [Finite F]

/-- The order of the original projective centralizer divides the actual GU₂ order. -/
theorem projective_centralizer_card_dvd (J : HermitianForm 3 F)
    {p e : ℕ} [Fact p.Prime] (hp : Odd p) (he : 0 < e)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∣
      p ^ e * ((p ^ e) ^ 2 - 1) * (p ^ e + 1) := by
  let E := GaloisField p (2 * e)
  let J3 := ABG.unitaryForm 3 p e (by omega)
  let J2 := ABG.unitaryForm 2 p e (by omega)
  have hE : Nat.card E = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, Nat.mul_comm e 2]
  have hJ3 : Nat.card {x : E // J3.conj x = x} = p ^ e :=
    FiniteField.card_fixed_of_quadratic_frobenius J3.conj p e he hE
      (by intro x; exact iterateFrobeniusEquiv_def _ _ _ _)
  have hJ : Nat.card {x : F // J.conj x = x} = p ^ e :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj p e he hcard hconj
  obtain ⟨s⟩ := J.nonempty_specialEquiv_of_card J3 (p ^ e) hcard hJ hE hJ3
  let q := J.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := SU3.InnerThreeRank.exists_involution_lift_of_cube_kernel q
    J.specialToProjective_surjective hcube t ht
  let C := centralizer ({z} : Set J.specialSubgroup)
  have hmap : C.map q = centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    SU3.InnerThreeRank.map_centralizer_of_central_cube_kernel q J.specialToProjective_surjective
      J.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let f := ep.toMonoidHom.comp (q.subgroupMap C)
  have hf : Function.Surjective f := ep.surjective.comp (q.subgroupMap_surjective C)
  let c := Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv s z
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hp
  have h2 : (2 : E) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime E Nat.prime_two hp2
  let d := involutionCentralizerEquiv J3 J2 rfl rfl rfl (p ^ e) hE hJ3 h2
    (s z) ((s.orderOf_eq z).trans hz)
  have hc : Nat.card C = Nat.card (ABG.GU2 p e (by omega)) :=
    Nat.card_congr (c.trans d.symm).toEquiv
  have hd := Subgroup.card_dvd_of_surjective f hf
  rw [hc, ABG.GU2_card p e hp (by omega)] at hd
  exact hd

private theorem rank_le_of_card_dvd_prime_power_mul {G : Type*} [Group G] [Finite G]
    {p e n : ℕ} [Fact p.Prime] (hc : Nat.card G ∣ p ^ e * n)
    (hn : Nat.Coprime p n) : primeRank p G ≤ e := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro A hA
  let := hA
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
  have hd : p ^ k ∣ p ^ e * n := hk ▸ A.card_subgroup_dvd_card.trans hc
  have hke : p ^ k ∣ p ^ e := (hn.pow_left k).dvd_of_dvd_mul_right hd
  rw [hk]
  exact Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos e) hke

/-- An arbitrary involution in the original PSU₃ model has defining-prime
centralizer rank at most the exponent of its fixed field. -/
theorem projective_involution_centralizer_rank (J : HermitianForm 3 F)
    {p e : ℕ} [Fact p.Prime] (hp : Odd p) (he : 0 < e)
    (hcard : Nat.card F = (p ^ e) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    primeRank p (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ≤ e := by
  let : Finite (GL (Fin 3) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hc := projective_centralizer_card_dvd J hp he hcard hconj t ht
  rw [mul_assoc] at hc
  apply rank_le_of_card_dvd_prime_power_mul hc
  have hq : p ∣ p ^ e := dvd_pow_self p (by omega)
  have hq2 : p ∣ (p ^ e) ^ 2 := hq.trans (dvd_pow_self (p ^ e) (by decide))
  have hpos : 1 ≤ (p ^ e) ^ 2 := Nat.one_le_pow _ _ (pow_pos (Fact.out : p.Prime).pos e)
  have hleft : Nat.Coprime p ((p ^ e) ^ 2 - 1) :=
    Nat.Coprime.of_dvd_left hq2 ((Nat.coprime_self_sub_right hpos).mpr (by simp))
  have hright : Nat.Coprime p (p ^ e + 1) :=
    Nat.Coprime.of_dvd_left hq (Nat.coprime_self_add_right.mpr (by simp))
  exact hleft.mul_right hright

end Theory.SpecificGroups.Classical.DefiningLocalRank.UnitaryCentralizer
