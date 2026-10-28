module

public import Stellmacher.Recognition.Parrott.Recognition
public import Theory.SpecificGroups.ReeTwo.TitsParrottCore

/-!
# Recognizing a concrete Tits involution centralizer

A multiplicative equivalence with the actual first Tits parabolic transports
its two-core, faithful five-by-four quotient and Sylow-five fixed subgroup.
Thus the local model supplies Parrott's original centralizer hypotheses.
The subsequent ambient recognition retains the independent N₂ hypothesis.

Source: Parrott (1972), original hypotheses, p.672, and recognition, pp.683--684.
-/

public section
namespace Stellmacher.Recognition

open Subgroup ReeTwo.ParabolicConcrete
variable {G : Type*} [Group G] [Finite G]

/-- An actual Tits first-parabolic marking supplies all of Parrott's
original involution-centralizer hypotheses. -/
theorem parrott_hypotheses_of_tits_centralizer (z : G) (hz : orderOf z = 2)
    (e : Tits.ExceptionalParabolics.first ≃* centralizer ({z} : Set G)) :
    ParrottCentralizerHypotheses z := by
  let C := centralizer ({z} : Set G)
  let Q := pCore 2 C
  let q : titsQ ≃* Q := (titsQ.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hq (x : titsQ) : (q x : C) = e x := rfl
  let : Group.IsNilpotent Q := (pCore_isPGroup (p := 2) (G := C)).isNilpotent
  have hclass : 3 ≤ Group.nilpotencyClass Q :=
    tits_core_class_lower.trans (Group.nilpotencyClass_le_of_surjective q.symm.toMonoidHom q.symm.surjective)
  refine ⟨hz, (Nat.card_congr q.toEquiv).symm.trans titsQ_card, hclass,
    ⟨FiveFour.action,FiveFour.action_injective,?_⟩,?_⟩
  · exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans titsQuotientEquiv⟩
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨P,hP⟩ := tits_sylow_five_fixed_center
    let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
    refine ⟨S,?_⟩
    intro x hx
    have hx' : q.symm x ∈ (centralizer (P : Set Tits.ExceptionalParabolics.first)).subgroupOf titsQ := by
      intro p hp
      apply e.injective
      rw [map_mul,map_mul]
      have he : e (q.symm x : Tits.ExceptionalParabolics.first) = (x : C) := by
        rw [← hq,q.apply_symm_apply]
      change e p * e (q.symm x : Tits.ExceptionalParabolics.first) = e (q.symm x : Tits.ExceptionalParabolics.first) * e p
      rw [he]
      exact hx (e p) (show e p ∈ S from mem_map_of_mem e.toMonoidHom hp)
    have hc := hP hx'
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := q.surjective y
    have hh := congrArg q (mem_center_iff.mp hc y)
    simpa only [map_mul,q.apply_symm_apply] using hh


/-- The concrete centralizer marking recognizes a nonsolvable simple N₂-group. -/
theorem nonempty_equiv_tits_of_concrete_centralizer [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (z : G) (hz : orderOf z = 2)
    (e : Tits.ExceptionalParabolics.first ≃* centralizer ({z} : Set G)) :
    Nonempty (G ≃* Tits.ParrottGroup) :=
  nonempty_equiv_tits_of_parrott hns hN (parrott_hypotheses_of_tits_centralizer z hz e)

end Stellmacher.Recognition
