module

public import Theory.GroupTheory.AbelianBySymmetricThree
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Frames
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Odd unitary subgroups and their torus normalizers

The source is GLS, Volume 4, Chapter 4, Lemma 3.11 and Chapter 2,
Lemma 17.4 (`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603 and
`refs/KGroup/GLS4/Chapter2.tex`, lines 3136–3147).

For an odd subgroup H normalized by an involution t and contained in no
isotropic-line stabilizer, the geometric placement theorem constructs an
orthonormal frame preserved by H⟨t⟩. Its full diagonal special-unitary
subgroup, or its literal projective image, is the required torus F.
The structure theorem computes both cyclic factors, the actual quotient
N(F)/(F.subgroupOf N(F)) ≃ S₃, the fixed-subgroup order (q+1)/d,
and the commutator [F,t] ≃ C_(q+1). Here d=1 for SU₃ and
d=gcd(3,q+1) for PSU₃. Thus `special_odd_subgroup_torus` and
`projective_odd_subgroup_torus` establish all clauses of Lemma 3.11.

Under N(H) ≤ H⟨t⟩, the finite-group argument then gives C_H(t) ≤ F,
[H : C_H(t)] dividing 3(q+1), and [H : C_H(t)] ≠ q+1.
These conclusions have no additional torus-data or ambient ZD premises.
The Sylow-three obstruction is proved in `AbelianBySymmetricThree`;
the Section 17 consumer's arithmetic implication c=q+1 finishes its
contradiction. The earlier conditional interfaces are retained, while
the final special and projective applications discharge their premises.
-/

public section

open Subgroup
namespace UnitaryThree.OddTorusNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- The group-theoretic conclusion of Lemma 17.4 from the explicit torus data. -/
theorem constraints_of_torus_data
    (F H : Subgroup G) [IsMulCommutative F]
    (q d : ℕ) (hq : Even q) (hd : d ∣ q + 1)
    (eF : F ≃* Multiplicative (ZMod (q + 1)) × Multiplicative (ZMod ((q + 1) / d)))
    (eN : normalizer F ⧸ F.subgroupOf (normalizer F) ≃* Equiv.Perm (Fin 3))
    (hHodd : Odd (Nat.card H)) (t : G) (ht : orderOf t = 2)
    (htN : t ∈ normalizer H) (hN : normalizer H ≤ H ⊔ zpowers t)
    (hinside : H ⊔ zpowers t ≤ normalizer F)
    (hfixed : Nat.card (F ⊓ centralizer ({t} : Set G) : Subgroup G) = (q + 1) / d) :
    H ⊓ centralizer ({t} : Set G) ≤ F ∧
      (centralizer ({t} : Set G)).relIndex H ∣ 3 * (q + 1) ∧
      (centralizer ({t} : Set G)).relIndex H ≠ q + 1 := by
  have hFcard : Nat.card F = (q + 1) * ((q + 1) / d) := by
    rw [Nat.card_congr eF.toEquiv, Nat.card_prod,
      Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, Nat.card_zmod]
  have hodd : Odd (q + 1) := hq.add_odd odd_one
  have hFodd : Odd (Nat.card F) := by
    rw [hFcard]
    exact hodd.mul (Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd hd))
  have hindex : (centralizer ({t} : Set G)).relIndex F = q + 1 := by
    have hc' := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G)
      (F ⊓ centralizer ({t} : Set G)) F bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, hfixed, hFcard] at hc'
    have hpos : 0 < (q + 1) / d := hfixed ▸ Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (hc'.trans (Nat.mul_comm _ _))
  simpa only [hindex] using
    AbelianBySymmetricThree.constraints_in_normalizer F H hFodd eN hHodd t ht htN hN hinside

end UnitaryThree.OddTorusNormalizer

namespace UnitaryThree.OddTorusNormalizer
open BenderSuzuki.MatrixGroups
variable {E : Type*} [Field E] [Finite E]

/-- Application to the actual SU₃ frame torus; its structural data remain explicit. -/
theorem special_constraints_of_frame_data
    (J : HermitianForm 3 E) (P : OrthogonalFrame J)
    (H : Subgroup J.specialSubgroup) (q : ℕ) (hq : Even q)
    (eF : specialFrameTorus J P ≃*
      Multiplicative (ZMod (q + 1)) × Multiplicative (ZMod (q + 1)))
    (eN : normalizer (specialFrameTorus J P) ⧸
      (specialFrameTorus J P).subgroupOf (normalizer (specialFrameTorus J P)) ≃*
        Equiv.Perm (Fin 3))
    (hHodd : Odd (Nat.card H)) (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htN : t ∈ normalizer H) (hN : normalizer H ≤ H ⊔ zpowers t)
    (hinside : H ⊔ zpowers t ≤ normalizer (specialFrameTorus J P))
    (hfixed : Nat.card (specialFrameTorus J P ⊓ centralizer ({t} : Set J.specialSubgroup) :
      Subgroup J.specialSubgroup) = q + 1) :
    H ⊓ centralizer ({t} : Set J.specialSubgroup) ≤ specialFrameTorus J P ∧
      (centralizer ({t} : Set J.specialSubgroup)).relIndex H ∣ 3 * (q + 1) ∧
      (centralizer ({t} : Set J.specialSubgroup)).relIndex H ≠ q + 1 := by
  exact constraints_of_torus_data (specialFrameTorus J P) H q 1 hq (one_dvd _)
    (by rw [Nat.div_one]; exact eF) eN hHodd t ht htN hN hinside
    (by simpa only [Nat.div_one] using hfixed)

/-- Application to the actual PSU₃ image, with the exact gcd(3,q+1) divisor. -/
theorem projective_constraints_of_frame_data
    (J : HermitianForm 3 E) (P : OrthogonalFrame J)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (q : ℕ) (hq : Even q)
    (eF : projectiveFrameTorus J P ≃*
      Multiplicative (ZMod (q + 1)) × Multiplicative (ZMod ((q + 1) / Nat.gcd 3 (q + 1))))
    (eN : normalizer (projectiveFrameTorus J P) ⧸
      (projectiveFrameTorus J P).subgroupOf (normalizer (projectiveFrameTorus J P)) ≃*
        Equiv.Perm (Fin 3))
    (hHodd : Odd (Nat.card H)) (t : ProjectiveSpecialUnitaryMatrixGroup J)
    (ht : orderOf t = 2) (htN : t ∈ normalizer H)
    (hN : normalizer H ≤ H ⊔ zpowers t)
    (hinside : H ⊔ zpowers t ≤ normalizer (projectiveFrameTorus J P))
    (hfixed : Nat.card (projectiveFrameTorus J P ⊓
      centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = (q + 1) / Nat.gcd 3 (q + 1)) :
    H ⊓ centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      projectiveFrameTorus J P ∧
      (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))).relIndex H ∣
        3 * (q + 1) ∧
      (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))).relIndex H ≠ q + 1 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  exact constraints_of_torus_data (projectiveFrameTorus J P) H q (Nat.gcd 3 (q + 1))
    hq (Nat.gcd_dvd_right _ _) eF eN hHodd t ht htN hN hinside hfixed

end UnitaryThree.OddTorusNormalizer

open Subgroup BenderSuzuki.MatrixGroups
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E] [Finite E]

/-- GLS4, Chapter 4, Lemma 3.11 for the actual SU₃ group. The torus is the
full diagonal special-unitary subgroup in the constructed orthonormal frame.
The fixed-subgroup order also supplies the calculation used in Lemma 17.4. -/
theorem special_odd_subgroup_torus
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : SpecialNoBorel J H) :
    ∃ P : OrthogonalFrame J,
      H ⊔ zpowers t ≤ normalizer (specialFrameTorus J P) ∧
      Nonempty (specialFrameTorus J P ≃*
        Multiplicative (ZMod (2 ^ n + 1)) × Multiplicative (ZMod (2 ^ n + 1))) ∧
      Nonempty ((normalizer (specialFrameTorus J P) ⧸
        (specialFrameTorus J P).subgroupOf (normalizer (specialFrameTorus J P))) ≃*
          Equiv.Perm (Fin 3)) ∧
      Nat.card ↥(specialFrameTorus J P ⊓ centralizer {t}) = 2 ^ n + 1 ∧
      Nonempty (↥⁅specialFrameTorus J P, zpowers t⁆ ≃*
        Multiplicative (ZMod (2 ^ n + 1))) := by
  obtain ⟨P, hP⟩ := special_placement J hn hcard hfixed H hodd t ht htH hB
  obtain ⟨_, hF, hN, hcalc⟩ := specialFrameTorus_structure J P n hn hcard hfixed
  exact ⟨P, hP, hF, hN, hcalc t ht
    (hP ((le_sup_right : zpowers t ≤ H ⊔ zpowers t) (mem_zpowers t)))⟩

/-- GLS4, Chapter 4, Lemma 3.11 for the actual PSU₃ group. The torus is the
literal projective image of the full special-unitary frame torus, so its
second cyclic factor and fixed subgroup retain the divisor `gcd(3,q+1)`. -/
theorem projective_odd_subgroup_torus
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hodd : Odd (Nat.card H))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : ProjectiveNoBorel J H) :
    ∃ P : OrthogonalFrame J,
      H ⊔ zpowers t ≤ normalizer (projectiveFrameTorus J P) ∧
      Nonempty (projectiveFrameTorus J P ≃*
        Multiplicative (ZMod (2 ^ n + 1)) ×
          Multiplicative (ZMod ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)))) ∧
      Nonempty ((normalizer (projectiveFrameTorus J P) ⧸
        (projectiveFrameTorus J P).subgroupOf (normalizer (projectiveFrameTorus J P))) ≃*
          Equiv.Perm (Fin 3)) ∧
      Nat.card ↥(projectiveFrameTorus J P ⊓ centralizer {t}) =
        (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) ∧
      Nonempty (↥⁅projectiveFrameTorus J P, zpowers t⁆ ≃*
        Multiplicative (ZMod (2 ^ n + 1))) := by
  obtain ⟨P, hP⟩ := projective_placement J hn hcard hfixed H hodd t ht htH hB
  obtain ⟨_, hF, hN, hcalc⟩ := projectiveFrameTorus_structure J P n hn hcard hfixed
  exact ⟨P, hP, hF, hN, hcalc t ht
    (hP ((le_sup_right : zpowers t ≤ H ⊔ zpowers t) (mem_zpowers t)))⟩

/-- The SU₃ application in GLS4, Chapter 2, Lemma 17.4, with every geometric
and torus-structure premise discharged. Normalizer control forces the odd
subgroup's fixed elements into the constructed torus; the Sylow-three
argument excludes fixed-point index `q+1`. -/
theorem special_odd_subgroup_constraints
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : SpecialNoBorel J H)
    (hN : normalizer H ≤ H ⊔ zpowers t) :
    ∃ P : OrthogonalFrame J,
      H ⊔ zpowers t ≤ normalizer (specialFrameTorus J P) ∧
      H ⊓ centralizer {t} ≤ specialFrameTorus J P ∧
      (centralizer {t}).relIndex H ∣ 3 * (2 ^ n + 1) ∧
      (centralizer {t}).relIndex H ≠ 2 ^ n + 1 := by
  obtain ⟨P, hP, ⟨eF⟩, ⟨eN⟩, hC, _⟩ :=
    special_odd_subgroup_torus J hn hcard hfixed H hodd t ht htH hB
  exact ⟨P, hP, special_constraints_of_frame_data J P H (2 ^ n)
    (even_two.pow_of_ne_zero (by omega : n ≠ 0)) eF eN hodd t ht htH hN hP hC⟩

/-- The corresponding PSU₃ conclusion, using the actual projective quotient
and its smaller fixed subgroup. No ambient ZD hypothesis is required. -/
theorem projective_odd_subgroup_constraints
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hodd : Odd (Nat.card H))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : ProjectiveNoBorel J H)
    (hN : normalizer H ≤ H ⊔ zpowers t) :
    ∃ P : OrthogonalFrame J,
      H ⊔ zpowers t ≤ normalizer (projectiveFrameTorus J P) ∧
      H ⊓ centralizer {t} ≤ projectiveFrameTorus J P ∧
      (centralizer {t}).relIndex H ∣ 3 * (2 ^ n + 1) ∧
      (centralizer {t}).relIndex H ≠ 2 ^ n + 1 := by
  obtain ⟨P, hP, ⟨eF⟩, ⟨eN⟩, hC, _⟩ :=
    projective_odd_subgroup_torus J hn hcard hfixed H hodd t ht htH hB
  exact ⟨P, hP, projective_constraints_of_frame_data J P H (2 ^ n)
    (even_two.pow_of_ne_zero (by omega : n ≠ 0)) eF eN hodd t ht htH hN hP hC⟩

/-- The terminal SU₃ obstruction for Lemma 17.4. The Section 17 consumer's
arithmetic theorem supplies the incompatible equality `c=q+1`. -/
theorem special_index_ne_succ
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : SpecialNoBorel J H)
    (hN : normalizer H ≤ H ⊔ zpowers t) :
    (centralizer {t}).relIndex H ≠ 2 ^ n + 1 := by
  obtain ⟨_, _, _, _, hne⟩ :=
    special_odd_subgroup_constraints J hn hcard hfixed H hodd t ht htH hB hN
  exact hne

/-- The terminal PSU₃ obstruction, retaining the actual projective model. -/
theorem projective_index_ne_succ
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hodd : Odd (Nat.card H))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : ProjectiveNoBorel J H)
    (hN : normalizer H ≤ H ⊔ zpowers t) :
    (centralizer {t}).relIndex H ≠ 2 ^ n + 1 := by
  obtain ⟨_, _, _, _, hne⟩ :=
    projective_odd_subgroup_constraints J hn hcard hfixed H hodd t ht htH hB hN
  exact hne

end UnitaryThree.OddTorusNormalizer
