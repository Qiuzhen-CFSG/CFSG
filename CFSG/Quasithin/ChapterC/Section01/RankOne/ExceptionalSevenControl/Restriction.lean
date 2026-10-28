module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.OmegaCenter

/-!
# Restricting an exceptional A₇ block to its Sylow product

A group equivalence transports the two-core, its commutator U and the
vanishing fixed subgroup. Thus the exceptional A₇ definition passes to
the same block viewed inside an overgroup containing it. Only the elementary
group-equivalence facts from the solvable transport module are reused.

Source: the application of C.1.23(2) inside LT, printed pp.129–130.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
open Subgroup
open CFSG.Quasithin.ChapterC
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

noncomputable def exceptionalUEquiv (e : A ≃* B) : blockU A ≃* blockU B :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (RankOne.Solvable.blockU_map_equiv e))

theorem exceptional_of_equiv (e : A ≃* B) (h : IsExceptionalA7Block A) : IsExceptionalA7Block B := by
  have hB := RankOne.Solvable.isShort_of_equiv e h.1
  let u := exceptionalUEquiv e
  have hu (b : blockU B) : e ((u.symm b : blockU A) : A) = b :=
    congrArg Subtype.val (u.apply_symm_apply b)
  have hf : blockFixed B = ⊥ := by
    apply bot_unique
    intro b hb
    have ha : u.symm b ∈ blockFixed A := by
      change (u.symm b : A) ∈ center A
      apply mem_center_iff.mpr
      intro a
      apply e.injective
      simp only [map_mul, hu]
      exact mem_center_iff.mp hb (e a)
    rw [h.fixed_eq_bot] at ha
    exact u.symm.injective (ha.trans u.symm.map_one.symm)
  refine ⟨hB, ?_, ?_⟩
  · obtain ⟨a⟩ := h.2.1
    exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans a⟩
  · let j : BlockModule B ≃* blockU B :=
      (QuotientGroup.quotientMulEquivOfEq hf).trans QuotientGroup.quotientBot
    exact (Nat.card_congr j.toEquiv).trans ((Nat.card_congr u.toEquiv).symm.trans h.u_card)


variable {G : Type*} [Group G] [Finite G]

theorem exceptional_subgroupOf (L H : Subgroup G) (hLH : L ≤ H)
    (hm : IsExceptionalA7Block L) : IsExceptionalA7Block (L.subgroupOf H) :=
  exceptional_of_equiv (subgroupOfEquivOfLe hLH).symm hm

theorem block_subgroupOf (L H : Subgroup G) (hLH : L ≤ H)
    (hL : IsBlock L) : IsBlock (L.subgroupOf H) :=
  ⟨inferInstance, RankOne.Solvable.isShort_of_equiv (subgroupOfEquivOfLe hLH).symm hL.short,
    hL.subnormal.subgroupOf⟩

end CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
