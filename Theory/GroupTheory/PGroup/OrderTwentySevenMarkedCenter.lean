module
public import Theory.GroupTheory.PGroup.OrderTwentySeven
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Mathlib.GroupTheory.IndexNormal

/-!
# Centers in nonabelian groups of order twenty-seven

Such a group is extraspecial, its center is its derived subgroup, and every
subgroup of order nine contains that center. The center and central quotient
orders give extraspeciality. The nontrivial derived subgroup fills the center;
an index-three subgroup is normal with cyclic quotient and contains the derived
subgroup. These facts mark the original Cartan cubic in the Sylow-three
argument of Aschbacher--Smith, 11.1.2, printed p.763.
-/

open Subgroup
open scoped IsMulCommutative
public noncomputable section
namespace OrderTwentySeven
variable {P : Type*} [Group P] [Finite P]
theorem extraspecial (hc : Nat.card P = 27) (hn : ¬ IsMulCommutative P) :
    IsExtraspecial 3 P := by
  have hQ := quotient_center_card hc hn
  refine ⟨center_card hc hn, ?_, Finite.one_lt_card_iff_nontrivial.mp (by omega)⟩
  refine { toIsMulCommutative :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by simpa using hQ)
           exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro q
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) q
  rw [←map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (cube_mem_center hc hn x)

theorem center_eq_commutator (hc : Nat.card P = 27) (hn : ¬ IsMulCommutative P) :
    center P = commutator P := by
  have hle : commutator P ≤ center P := by
    rw [commutator_def]
    exact Subgroup.commutator_le.mpr (fun a _ b _ => commutator_mem_center hc hn a b)
  have hne : commutator P ≠ ⊥ := by
    intro he
    exact hn ((commutator_eq_bot_iff P).mp he)
  have hd := card_dvd_of_le hle
  rw [center_card hc hn] at hd
  have hh : Nat.card (commutator P) = 3 :=
    (Nat.prime_three.eq_one_or_self_of_dvd _ hd).resolve_left
      (fun he => hne (card_eq_one.mp he))
  exact (eq_of_le_of_card_ge hle (by rw [hh,center_card hc hn])).symm

theorem center_le_of_card_nine (hc : Nat.card P = 27) (hn : ¬ IsMulCommutative P)
    (A : Subgroup P) (hA : Nat.card A = 9) : center P ≤ A := by
  have hi : A.index = 3 := by
    have hh := A.card_mul_index
    rw [hA,hc] at hh
    omega
  let : A.Normal := A.normal_of_index_eq_minFac_card (by rw [hi,hc]; decide +kernel)
  let : IsCyclic (P ⧸ A) := isCyclic_of_card_dvd_prime (p := 3) (by
    rw [←index_eq_card,hi])
  rw [center_eq_commutator hc hn]
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
end OrderTwentySeven

