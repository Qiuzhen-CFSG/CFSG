module
public import Theory.GroupAction.CentralKernelFixedComponents
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import CFSG.Quasithin.ChapterA.Section02.OddPrimeRank

/-! The second invariant pumpup cannot have a proper involution-fixed
component whose central quotient has cubic rank two.  Only the actual
central quotient and its involution-fixed components enter this argument. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {E : Type*} [Group E] [Finite E]

omit [Finite E] in
private theorem component_not_le_center {B C : Subgroup E}
    (hB : IsComponentIn B C) : ¬ B ≤ center E := by
  intro hc
  let : IsQuasisimple B := hB.quasisimple
  have he : ⁅B,B⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono hc le_top).trans (commutator_center_left (⊤ : Subgroup E)).le)
  rw [commutator_eq_self] at he
  exact hB.ne_bot he

/-- A component with cubic central quotient of rank two cannot be fixed by
a nontrivial involution when all fixed components downstairs have rank one. -/
theorem fixed_component_actor_eq_one_of_central_quotient_rank_two
    [Group.IsPerfect E] (a : MulAut E) (ha : a ^ 2 = 1)
    (B : Subgroup E) (hB : IsComponentIn B a.fixedSubgroup)
    (hr : 2 ≤ primeRank 3 (B ⧸ center B))
    (hfixed : ∀ b : MulAut (E ⧸ center E), orderOf b = 2 →
      ∀ C : Subgroup b.fixedSubgroup, IsComponent b.fixedSubgroup C → primeRank 3 C ≤ 1) :
    a = 1 := by
  by_contra hn
  let : IsQuasisimple B := hB.quasisimple
  let b := quotientAut (center E) a
  let q := QuotientGroup.mk' (center E)
  have ha2 : orderOf a = 2 := orderOf_eq_prime_iff.mpr ⟨ha,hn⟩
  have hb2 : orderOf b = 2 :=
    (orderOf_injective (quotientAut (center E)) MulAut.quotient_center_injective a).trans ha2
  have heq : ∀ x, q (a x) = b (q x) := fun x =>
    (quotientAut_apply_mk (center E) a x).symm
  have hne : B.map q ≠ ⊥ := by
    intro he
    apply component_not_le_center hB
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
  have hC := hB.map_fixed_of_central_ker a b q (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) heq hne
  let C := B.map q
  let : IsQuasisimple C := hC.quasisimple
  let : Nontrivial C := (nontrivial_iff_ne_bot _).mpr hne
  have hrC : primeRank 3 C ≤ 1 := by
    rw [← primeRank_equiv 3 (subgroupOfEquivOfLe hC.1)]
    exact hfixed b hb2 (C.subgroupOf b.fixedSubgroup) hC.2
  let e : (B ⧸ center B) ≃* (C ⧸ center C) :=
    IsQuasisimple.centralQuotientEquiv (q.subgroupMap B) (q.subgroupMap_surjective B)
  have hh := PrimeRank.le_of_surjective_of_source_le_one (by decide : (3 : ℕ) ≠ 2)
    (QuotientGroup.mk' (center C)) (QuotientGroup.mk'_surjective _) hrC
  rw [primeRank_equiv 3 e] at hr
  omega

end CFSG.Quasithin.Chapter2.Section05.Overcomponents
