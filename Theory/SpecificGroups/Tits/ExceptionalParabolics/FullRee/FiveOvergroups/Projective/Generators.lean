module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Interpretation
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Generation

/-! The literal projective generator images have orders4 and13 and therefore generate PSL₂(F25), by the proved Dickson classification. -/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Tits.Max4Projective
instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem field_card : Nat.card F=25 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (3:ZMod 5) 1),Nat.card_prod]
  norm_num

theorem projective_card : Nat.card PSL=7800 := psl25_card field_card
instance : IsSimpleGroup PSL := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [field_card];decide)

def a : SL := (raw0Gen 0).sl (raw0Gen_det 0)
def b : SL := (raw0Gen 1).sl (raw0Gen_det 1)
theorem b_four : b^4 = -1 := by apply Subtype.ext;decide +kernel
theorem ab_thirteen : (a*b)^13 = 1 ∨ (a*b)^13 = -1 := by decide +kernel

theorem pi_ne_one_of_entry {x:SL} (h : (x:Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0) : pi x ≠ 1 := by
  intro he
  obtain ⟨r,_,hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff _).mp he)
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
  exact h (by simpa [Matrix.scalar_apply,Matrix.diagonal] using hh.symm)

theorem b_order : orderOf (pi b)=4 := by
  have hsq : (pi b)^2 ≠ 1 := by
    rw [← map_pow]
    exact pi_ne_one_of_entry (by decide +kernel)
  have hp : (pi b)^4=1 := by rw [← map_pow,b_four,pi_neg_one]
  exact orderOf_eq_prime_pow (p:=2) (n:=1) hsq hp

theorem ab_order : orderOf (pi (a*b))=13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    rcases ab_thirteen with h|h
    · rw [h,map_one]
    · rw [h,pi_neg_one]
  · exact pi_ne_one_of_entry (by decide +kernel)

theorem target_range_top : closure (Set.range target0Gen)=⊤ := by
  let H := closure (Set.range target0Gen)
  have hb : pi b∈H := subset_closure ⟨1,rfl⟩
  have hab : pi (a*b)∈H := by
    rw [map_mul]
    exact H.mul_mem (subset_closure ⟨0,rfl⟩) hb
  apply psl25_eq_top_of_divisors field_card
  · have hh := orderOf_dvd_natCard (⟨pi b,hb⟩:H)
    rwa [← orderOf_submonoid,b_order] at hh
  · have hh := orderOf_dvd_natCard (⟨pi (a*b),hab⟩:H)
    rwa [← orderOf_submonoid,ab_order] at hh
end Tits.Max4Projective
