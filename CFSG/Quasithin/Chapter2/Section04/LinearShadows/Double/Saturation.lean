module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Theory.GroupTheory.PrimeRankZero
/-!
# Saturation of the odd torus in the two-block shadow

Prime rank alone cannot identify the abelian product B = DDˣ with D.
The source torus has order m² and exponent dividing the odd integer m=q−1.
Abelianness makes the conjugate-generated product have the same exponent.
Each Sylow subgroup of B has generator rank at most two, so its order divides
m² by Schreier's bound; prime factorization gives |B| | m². Hence D=B=Dˣ.

The source application takes an actual marking D ≃ Fˣ × Fˣ, retains the
literal conjugation map, and obtains the rank bound in N_G(Q) from the
original quasithin group. No exponent or rank table is assumed.
Source: Aschbacher–Smith, §2.4, printed p.540.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {B : Type*} [CommGroup B] [Finite B]
private theorem card_dvd_square_of_rank_bound {m : ℕ} (hm : 0 < m) (hpow : ∀ b : B, b ^ m = 1)
    (hr : ∀ p : ℕ, p.Prime → primeRank p B ≤ 2) : Nat.card B ∣ m ^ 2 := by
  apply (Nat.factorization_prime_le_iff_dvd (Nat.card_pos (α := B)).ne'
    (pow_pos hm 2).ne').mp
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p B := Classical.choice inferInstance
  have hP : Group.rank P ≤ 2 := by
    have h := (⊤ : Subgroup P).rank_le_primeRank p
      (P.isPGroup'.to_subgroup (⊤ : Subgroup P))
    rw [Group.rank_congr (Subgroup.topEquiv : (⊤ : Subgroup P) ≃* P)] at h
    exact h.trans ((Theory.GroupTheory.primeRank_le_of_injective p
      (P : Subgroup B).subtype Subtype.val_injective).trans (hr p hp))
  have hc : Nat.card P ∣ m ^ 2 :=
    (card_dvd_exponent_pow_rank' P (fun x => Subtype.ext (hpow x))).trans
      (pow_dvd_pow m hP)
  rw [P.card_eq_multiplicity] at hc
  exact (hp.pow_dvd_iff_le_factorization (pow_pos hm 2).ne').mp hc
end CFSG.Quasithin.Chapter2.LinearDouble
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {B : Type*} [CommGroup B] [Finite B]
private theorem card_dvd_square_of_odd_exponent {m : ℕ} (hm : Odd m)
    (hpow : ∀ b : B, b ^ m = 1) (hr : IsStronglyQuasithin B) : Nat.card B ∣ m ^ 2 := by
  apply card_dvd_square_of_rank_bound hm.pos hpow
  intro p hp
  by_cases hp2 : p = 2
  · rcases hp2 with rfl
    have hz : primeRank 2 B = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr (by
      intro hd
      obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 hd
      exact hm.not_two_dvd_nat (hx ▸ orderOf_dvd_of_pow_eq_one (hpow x)))
    omega
  · exact hr p hp (hp.odd_of_ne_two hp2)

variable {G : Type*} [Group G] [Finite G]
/-- An abelian strongly quasithin overgroup of the same bounded odd exponent
cannot properly contain a subgroup of the full square order. -/
theorem subgroup_eq_of_full_odd_square (D B : Subgroup G) (hDB : D ≤ B) (hcomm : IsMulCommutative B)
    {m : ℕ} (hm : Odd m) (hpow : ∀ b : B, b ^ m = 1)
    (hcard : Nat.card D = m ^ 2) (hr : IsStronglyQuasithin B) : D = B := by
  let := hcomm
  let : CommGroup B := IsMulCommutative.instCommGroup
  have hc := card_dvd_square_of_odd_exponent hm hpow hr
  apply eq_of_le_of_card_ge hDB
  rw [hcard]
  exact Nat.le_of_dvd (pow_pos hm.pos 2) hc
end CFSG.Quasithin.Chapter2.LinearDouble
namespace CFSG.Quasithin.Chapter2.LinearDouble
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
/-- The abelian conjugate product has the original torus exponent; saturation
then identifies both conjugates with their product. -/
theorem eq_conjugate_of_square_torus (D : Subgroup G) (x : G)
    {m : ℕ} (hm : Odd m) (hpow : ∀ d : D, d ^ m = 1)
    (hcard : Nat.card D = m ^ 2)
    (hcomm : IsMulCommutative (D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G))
    (hr : IsStronglyQuasithin (D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G)) :
    D = D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom ∧
      D = D.map (MulAut.conj x⁻¹).toMonoidHom := by
  let B := D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom
  have hDB : D ≤ B := le_sup_left
  have hpowB : ∀ b : B, b ^ m = 1 := by
    intro b
    apply Subtype.ext
    change (b : G) ^ m = 1
    have hb : (b : G) ∈ D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom := b.property
    rw [sup_eq_closure] at hb
    refine closure_induction (p := fun z _ => z ^ m = 1) ?_ ?_ ?_ ?_ hb
    · intro d hd
      rcases hd with hd | hd
      · exact congrArg Subtype.val (hpow ⟨d,hd⟩)
      · obtain ⟨d',hd',rfl⟩ := hd
        rw [← map_pow]
        have ht : d' ^ m = 1 := congrArg Subtype.val (hpow ⟨d',hd'⟩)
        rw [ht,map_one]
    · exact one_pow m
    · intro a b ha hb hpa hpb
      have haB : a ∈ B := by simpa only [B,sup_eq_closure] using ha
      have hbB : b ∈ B := by simpa only [B,sup_eq_closure] using hb
      have hab : Commute a b := congrArg Subtype.val
        (hcomm.is_comm.comm (⟨a,haB⟩ : B) (⟨b,hbB⟩ : B))
      rw [hab.mul_pow,hpa,hpb,mul_one]
    · intro a _ hpa
      rw [inv_pow,hpa,inv_one]
  have he := subgroup_eq_of_full_odd_square D B hDB hcomm hm hpowB hcard hr
  refine ⟨he, ?_⟩
  apply (eq_of_le_of_card_ge (show D.map (MulAut.conj x⁻¹).toMonoidHom ≤ D from
    (le_sup_right : D.map (MulAut.conj x⁻¹).toMonoidHom ≤ B).trans he.ge) ?_).symm
  rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
end CFSG.Quasithin.Chapter2.LinearDouble
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
/-- Source p.540: B=D=Dˣ for an actual pair of finite-field tori in the
normalizer of the original nontrivial two-subgroup Q. -/
theorem eq_conjugate_of_field_torus (D Q : Subgroup G) (x : G) (eD : D ≃* (Fˣ × Fˣ))
    (hG : IsQuasithin G) (hQ : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hDQ : D ≤ normalizer (Q : Set G))
    (hDxQ : D.map (MulAut.conj x⁻¹).toMonoidHom ≤ normalizer (Q : Set G))
    (hcomm : IsMulCommutative (D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G)) :
    D = D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom ∧
      D = D.map (MulAut.conj x⁻¹).toMonoidHom := by
  let : Fintype F := Fintype.ofFinite F
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    exact FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  have hodd : Odd (Nat.card F - 1) := by
    obtain ⟨k,hk⟩ := heven
    have hpos := Nat.card_pos (α := F)
    refine ⟨k-1, ?_⟩
    omega
  have hpow : ∀ d : D, d ^ (Nat.card F - 1) = 1 := by
    intro d
    apply eD.injective
    rw [map_pow,map_one]
    apply Prod.ext
    · change (eD d).1 ^ (Nat.card F - 1) = 1
      simpa only [Nat.card_units] using
        (pow_card_eq_one' (x := (eD d).1))
    · change (eD d).2 ^ (Nat.card F - 1) = 1
      simpa only [Nat.card_units] using
        (pow_card_eq_one' (x := (eD d).2))
  have hcard : Nat.card D = (Nat.card F - 1) ^ 2 := by
    rw [Nat.card_congr eD.toEquiv,Nat.card_prod,Nat.card_units,pow_two]
  have hsq := CFSG.Quasithin.isQuasithin_iff_twoLocal.mp hG
    (normalizer (Q : Set G)) ⟨Q,hQne,hQ,rfl⟩
  exact eq_conjugate_of_square_torus D x hodd hpow hcard hcomm
    (hsq.of_injective (inclusion (sup_le hDQ hDxQ))
      (inclusion_injective (sup_le hDQ hDxQ)))
end CFSG.Quasithin.Chapter2.LinearDouble
