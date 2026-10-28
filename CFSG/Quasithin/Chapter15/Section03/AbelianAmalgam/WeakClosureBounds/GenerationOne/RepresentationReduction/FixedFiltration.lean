module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.FixedSpace
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Odd-index fixation through invariant extensions

A vector fixed by a subgroup B has a well-defined trace over the cosets of B.
If B has odd index, this trace lifts the same globally fixed quotient vector
in characteristic two. Consequently equality of B-fixed and group-fixed spaces
passes through extensions. Iteration handles the natural/central layers in the
SL₂ exception on printed p.1152 of Aschbacher--Smith, 15.3.65, without splitting
the extension or changing its actual quotient representation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
open Representation.BinaryOffender
open scoped BigOperators

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

private theorem action_out_eq (B : Subgroup D) (v : V) (hv : v ∈ fixedSpace ρ B)
    (q : D ⧸ B) (g : D) (hq : (QuotientGroup.mk g : D ⧸ B) = q) :
    ρ q.out v = ρ g v := by
  obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul B g
  have hout : q.out = g * (b : D) := by rw [← hq]; exact hb
  rw [hout, map_mul, Module.End.mul_apply]
  exact congrArg (ρ g) (hv b)

/-- A B-fixed vector with a globally fixed image has a globally fixed lift
of the same image when B has odd index. -/
theorem exists_fixed_lift_of_odd_index [Finite D]
    (C : Subrepresentation ρ) (B : Subgroup D) (hindex : Odd B.index)
    (v : V) (hv : v ∈ fixedSpace ρ B)
    (hq : C.toSubmodule.mkQ v ∈ fixedSpace C.quotientRepresentation ⊤) :
    ∃ w ∈ fixedSpace ρ ⊤, C.toSubmodule.mkQ w = C.toSubmodule.mkQ v := by
  classical
  let : Fintype (D ⧸ B) := Fintype.ofFinite _
  let w : V := ∑ q : D ⧸ B, ρ q.out v
  refine ⟨w, ?_, ?_⟩
  · intro g
    change ρ g.val w = w
    dsimp only [w]
    rw [map_sum]
    calc
      (∑ q : D ⧸ B, ρ g.val (ρ q.out v)) =
          ∑ q : D ⧸ B, ρ (g.val • q).out v := by
        apply Finset.sum_congr rfl
        intro q _
        rw [← Module.End.mul_apply, ← map_mul]
        exact (action_out_eq ρ B v hv (g.val • q) (g.val * q.out)
          (MulAction.Quotient.mk_smul_out B g.val q)).symm
      _ = ∑ q : D ⧸ B, ρ q.out v :=
        Equiv.sum_comp (MulAction.toPerm g.val) (fun q : D ⧸ B => ρ q.out v)
  · have he (q : D ⧸ B) : C.toSubmodule.mkQ (ρ q.out v) = C.toSubmodule.mkQ v :=
      hq ⟨q.out, Subgroup.mem_top _⟩
    have hodd : Odd (Fintype.card (D ⧸ B)) := by
      simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hindex
    dsimp only [w]
    rw [map_sum]
    simp only [he, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hodd.natCast_zmod_two, one_smul]

/-- Equality of Borel-fixed and global fixed vectors is closed under invariant
extensions at odd index. Both the kernel and the quotient retain their actions. -/
theorem fixedSpace_le_of_extension [Finite D]
    (C : Subrepresentation ρ) (B : Subgroup D) (hindex : Odd B.index)
    (hC : C.toSubmodule ⊓ fixedSpace ρ B ≤ fixedSpace ρ ⊤)
    (hquot : fixedSpace C.quotientRepresentation B ≤
      fixedSpace C.quotientRepresentation ⊤) :
    fixedSpace ρ B ≤ fixedSpace ρ ⊤ := by
  intro v hv
  have hq : C.toSubmodule.mkQ v ∈ fixedSpace C.quotientRepresentation B := by
    intro b
    exact congrArg C.toSubmodule.mkQ (hv b)
  obtain ⟨w, hw, he⟩ := exists_fixed_lift_of_odd_index ρ C B hindex v hv (hquot hq)
  have hvw : v - w ∈ C.toSubmodule := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change C.toSubmodule.mkQ (v - w) = 0
    rw [map_sub, he, sub_self]
  have hbw : w ∈ fixedSpace ρ B := fun b => hw ⟨b, Subgroup.mem_top _⟩
  have hdiff := hC ⟨hvw, (fixedSpace ρ B).sub_mem hv hbw⟩
  simpa only [sub_add_cancel] using (fixedSpace ρ ⊤).add_mem hdiff hw

/-- A subgroup containing a Sylow two-subgroup has odd index, as required
for the extension argument. This applies to the genuine Borel models. -/
theorem odd_index_of_sylow_le [Finite D] (S : Sylow 2 D) (B : Subgroup D)
    (hSB : (S : Subgroup D) ≤ B) : Odd B.index := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  exact S.not_dvd_index (heven.two_dvd.trans (Subgroup.index_dvd_of_le hSB))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
