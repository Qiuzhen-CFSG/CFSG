module
public import Theory.GroupTheory.PResidual.ConjugateSpan

/-!
# The residual of a moving prime conjugate orbit

Let P be a normal odd prime subgroup and R lie in a two-subgroup S.
If R moves P, then [P,R]=P lies in the orbit span of R under PS.
The quotient PS/P is a two-group, so the span's two-residual lies in P;
P's odd order supplies the opposite inclusion. The conjugating group
remains the specified PS throughout.

Source application: Aschbacher--Smith15.2.3(1), printed pp.1104--1105.
-/

public section
open Subgroup
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

/-- A moving prime normal subgroup is exactly the residual of the prescribed two-orbit. -/
theorem prime_conjugateSpan_residual (P S R : Subgroup D) [P.Normal]
    (hP : Nat.Prime (Nat.card P)) (hodd : Odd (Nat.card P))
    (hS : IsPGroup 2 S) (hRS : R ≤ S)
    (hmove : ¬ R ≤ centralizer (P : Set D)) :
    (pResidual 2 (conjugateSpanBy R (P ⊔ S))).map
      (conjugateSpanBy R (P ⊔ S)).subtype = P := by
  let N := conjugateSpanBy R (P ⊔ S)
  let E := (pResidual 2 N).map N.subtype
  have hNE : N ≤ P ⊔ S := conjugateSpanBy_le (hRS.trans le_sup_right) (P ⊔ S).le_normalizer
  have hEP : E ≤ P := le_normal_of_isPPerfect_of_le_sup_pGroup E P S
    (isPPerfect_embedded_pResidual 2 N) hS ((map_subtype_le _).trans hNE)
  have hcommP : ⁅P,R⁆ ≤ P := commutator_le_left P R
  have hcommN : ⁅P,R⁆ ≤ N := (commutator_mono le_rfl (le_conjugateSpanBy R (P ⊔ S))).trans
    (le_normalizer_iff_commutator_le_right.mp
      (le_sup_left.trans (le_normalizer_conjugateSpanBy R (P ⊔ S))))
  have hcommNe : ⁅P,R⁆ ≠ ⊥ := by
    intro hh
    exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
  have heq : ⁅P,R⁆ = P := by
    let : Fact (Nat.card P).Prime := ⟨hP⟩
    rcases (⁅P,R⁆.subgroupOf P).eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hh := congrArg (map P.subtype) hb
      rw [map_subgroupOf_eq_of_le hcommP,map_bot] at hh
      exact (hcommNe hh).elim
    · have hh := congrArg (map P.subtype) ht
      simpa only [map_subgroupOf_eq_of_le hcommP,←MonoidHom.range_eq_map,range_subtype] using hh
  have hPN : P ≤ N := heq ▸ hcommN
  apply le_antisymm hEP
  intro x hx
  refine ⟨⟨x,hPN hx⟩,?_,rfl⟩
  apply mem_pResidual_of_orderOf_coprime
  have hc := hodd.coprime_two_left.of_dvd_right (P.orderOf_dvd_natCard hx)
  exact (N.orderOf_coe ⟨x,hPN hx⟩) ▸ hc

end Subgroup
