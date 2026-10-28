module
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Unitary.Reduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary

/-!
# The two small unitary Cartan cases

At fixed-field order two the full SU₃ torus has order three and its
projective image has order dividing three. Their automorphism groups have
order dividing two. Hence every odd actor fixes either torus, without a
simplicity or semilinearity assumption. Hall and Sylow conjugacy then handle
all Cartan complements, and a genuine Hermitian basis change handles every
form. Source: Aschbacher–Smith F.1.3(5), printed p.260; Huppert II.10.12.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace CFSG.Quasithin.ChapterF.Source.Unitary
variable {G : Type*} [Group G] [Finite G]

/-- An odd automorphism preserving a subgroup of order dividing three fixes it. -/
theorem odd_aut_fixes_of_card_dvd_three (D : Subgroup G) (hD : Nat.card D ∣ 3)
    (a : MulAut G) (hao : Odd (orderOf a)) (haD : D.map a.toMonoidHom = D) :
    ∀ x ∈ D, a x = x := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic D := isCyclic_of_card_dvd_prime hD
  let b : MulAut D := (a.subgroupMap D).trans (MulEquiv.subgroupCongr haD)
  have hb (k : ℕ) (x : D) : ((b ^ k) x : G) = (a ^ k) (x : G) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply]
      change a (((b ^ k) x : D) : G) = a ((a ^ k) (x : G))
      rw [ih]
  have hpow : b ^ orderOf a = 1 := by
    ext x
    rw [hb, pow_orderOf_eq_one]
    rfl
  have hc : Nat.card (MulAut D) ∣ 2 := by
    rw [IsCyclic.card_mulAut]
    rcases (Nat.dvd_prime Nat.prime_three).mp hD with h | h <;> rw [h] <;> decide
  have htwo : orderOf b ∣ 2 := (orderOf_dvd_natCard b).trans hc
  have hone : orderOf b = 1 := Nat.dvd_one.mp (by
    have hd := Nat.dvd_gcd htwo (orderOf_dvd_of_pow_eq_one hpow)
    rwa [(Nat.coprime_two_left.mpr hao).gcd_eq_one] at hd)
  have hb1 : b = 1 := orderOf_eq_one_iff.mp hone
  intro x hx
  have he := congrArg (fun c : MulAut D => (c ⟨x,hx⟩ : G)) hb1
  exact he

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The fixed standard SU₃ pair reduces to the intrinsic Cartan statement. -/
theorem special_cartanRigidity_of_pair {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hr : PairRigidity (suRoot J hJ) (suTorus J hJ)) :
    CartanQuadraticRigidity J.specialSubgroup := by
  obtain ⟨_, _, S, hSR, _, _, _, hN, _, _, hsolv, _, _, _, hodd⟩ :=
    standard_su_borel_data J n hn hcard hconj hJ
  apply cartanRigidity_of_standard_pair S (suTorus J hJ)
  · change suTorus J hJ ≤ normalizer ((S : Subgroup J.specialSubgroup) : Set _)
    rw [hSR, hN]
    exact le_sup_right
  · exact Nat.coprime_two_left.mpr hodd
  · change (S : Subgroup J.specialSubgroup) ⊔ suTorus J hJ = normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup)
    rw [hSR, hN]
  · change Group.IsSolvable (normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup))
    rwa [hSR]
  · rwa [hSR]

/-- The fixed standard PSU₃ pair reduces to the intrinsic Cartan statement,
using the actual projection of the root and torus. -/
theorem projective_cartanRigidity_of_pair {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hr : PairRigidity (hermitianUnipotentPSU J hJ).range (hermitianTorusPSU J hJ).range) :
    CartanQuadraticRigidity (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨_, _, S, hSR, _, _, _, _, _, _, _, _, _, _, hodd⟩ :=
    standard_su_borel_data J n hn hcard hconj hJ
  let P := S.mapSurjective (suProjection_surjective J)
  have hP : (P : Subgroup _) = (hermitianUnipotentPSU J hJ).range := by
    change (S : Subgroup _).map (suProjection J) = _
    rw [hSR, suRoot_map_projection]
  obtain ⟨_, _, _, _, _, _, hsup, hN, _⟩ :=
    standard_projective_matrix_borel J n hn hcard hconj hJ
  have hNP : normalizer (P : Set _) =
      (hermitianUnipotentPSU J hJ).range ⊔ (hermitianTorusPSU J hJ).range := by
    change normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
    rw [hP, hN, hsup]
  apply cartanRigidity_of_standard_pair P (hermitianTorusPSU J hJ).range
  · rw [hNP]
    exact le_sup_right
  · have hd := (suTorus J hJ).card_map_dvd (suProjection J)
    rw [suTorus_map_projection] at hd
    exact (Nat.coprime_two_left.mpr hodd).of_dvd_right hd
  · rw [hNP, hP]
  · exact (standard_psu_facts J n hn hcard hconj hJ P).solvable
  · rwa [hP]

/-- SU₃(2) needs only its actual order-three torus. -/
theorem special_cartanRigidity_two
    (hcard : Nat.card F = 2 ^ 2) (hconj : ∀ x, J.conj x = x ^ 2) :
    CartanQuadraticRigidity J.specialSubgroup := by
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J 1 (by decide)
    (by simpa using hcard) (by simpa using hconj)
  apply CartanQuadraticRigidity.of_equiv (FormTransport.specialEquiv J C hC)
  apply special_cartanRigidity_of_pair (FormTransport.standardForm J)
    (n := 1) (by decide) (by simpa using hcard) (by simpa using hconj) rfl
  intro a hao _haU haD _hq
  apply odd_aut_fixes_of_card_dvd_three _ _ a hao haD
  have hc := suTorus_card (FormTransport.standardForm J) rfl
  simpa [hcard] using hc.dvd

/-- PSU₃(2) uses the image of that torus, with its scalar kernel retained. -/
theorem projective_cartanRigidity_two
    (hcard : Nat.card F = 2 ^ 2) (hconj : ∀ x, J.conj x = x ^ 2) :
    CartanQuadraticRigidity (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J 1 (by decide)
    (by simpa using hcard) (by simpa using hconj)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) :=
    Finite.of_surjective _ (suProjection_surjective (FormTransport.standardForm J))
  apply CartanQuadraticRigidity.of_equiv (FormTransport.projectiveEquiv J C hC)
  apply projective_cartanRigidity_of_pair (FormTransport.standardForm J)
    (n := 1) (by decide) (by simpa using hcard) (by simpa using hconj) rfl
  intro a hao _haU haD _hq
  apply odd_aut_fixes_of_card_dvd_three _ _ a hao haD
  have hd := (suTorus (FormTransport.standardForm J) rfl).card_map_dvd
    (suProjection (FormTransport.standardForm J))
  rw [suTorus_map_projection (FormTransport.standardForm J) rfl,
    suTorus_card (FormTransport.standardForm J) rfl, hcard] at hd
  simpa using hd

end CFSG.Quasithin.ChapterF.Source.Unitary
