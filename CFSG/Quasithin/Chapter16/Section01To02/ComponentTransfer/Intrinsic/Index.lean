module

public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Action

/-!
# Sylow fixed-point indices from intrinsic centralizer indices

If 4 divides |K:C|, it divides |R:R ∩ C| for every Sylow two-subgroup R
of K: compute the index of R ∩ C through R and cancel the odd index |K:R|.
Fixed points upstairs map into fixed points downstairs under an equivariant
surjection, so the same numerical bound in a quotient implies the bound in K.
No invariance of R under t is used, and fixed points need not lift.

These are numerical transfer lemmas for 16.1.8. The actual centralizer tables
must still establish the divisibility hypotheses in the surviving source
cases. This module does not assume or assert the nine-case classification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4–16.1.5 and 16.1.8, pp.1171–1173.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic

open Subgroup Theory.GroupTheory

variable {G M : Type*} [Group G] [Group M] [Finite G]

/-- The factor four in an index survives restriction to every Sylow two-subgroup. -/
theorem four_dvd_relIndex_sylow (C : Subgroup G) (R : Sylow 2 G)
    (hC : 4 ∣ C.index) : 4 ∣ C.relIndex R := by
  have hd : 4 ∣ (C ⊓ (R : Subgroup G)).index :=
    hC.trans (index_dvd_of_le (show C ⊓ (R : Subgroup G) ≤ C from inf_le_left))
  have he : C.relIndex R * R.index = (C ⊓ (R : Subgroup G)).index := by
    rw [← relIndex_mul_index (show C ⊓ (R : Subgroup G) ≤ R from inf_le_right)]
    rw [inf_relIndex_right]
  rw [← he] at hd
  exact (Nat.prime_two.coprime_pow_of_not_dvd (m := 2) R.not_dvd_index).symm
    |>.dvd_of_dvd_mul_right hd

/-- The resulting relative index is strictly greater than two. -/
theorem strict_relIndex_sylow (C : Subgroup G) (R : Sylow 2 G)
    (hC : 4 ∣ C.index) : 2 < C.relIndex R := by
  have hp : 0 < C.relIndex R := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have := Nat.le_of_dvd hp (four_dvd_relIndex_sylow C R hC)
  omega

omit [Finite G] in
/-- An equivariant surjection transfers the factor four in a fixed-subgroup index. -/
theorem four_dvd_fixedIndex_of_quotient (a : MulAut G) (b : MulAut M)
    (f : G →* M) (hf : Function.Surjective f) (heq : ∀ x, f (a x) = b (f x))
    (hi : 4 ∣ b.fixedSubgroup.index) : 4 ∣ a.fixedSubgroup.index := by
  have hc : a.fixedSubgroup ≤ b.fixedSubgroup.comap f := by
    intro x hx
    rw [mem_comap, MulAut.mem_fixedSubgroup, ← heq, (MulAut.mem_fixedSubgroup a x).mp hx]
  have hd := index_dvd_of_le hc
  rw [index_comap_of_surjective _ hf] at hd
  exact hi.trans hd

/-- A numerical intrinsic model calculation bounds the actual ambient centralizer index. -/
theorem strict_index_of_model_fixedIndex {K : Subgroup G} {t : G}
    (hn : t ∈ normalizer K) (b : MulAut M) (f : K →* M)
    (hf : Function.Surjective f) (heq : ∀ x, f (action hn x) = b (f x))
    (hi : 4 ∣ b.fixedSubgroup.index) (R : Sylow 2 K) :
    2 < (involutionCentralizer t).relIndex ((R : Subgroup K).map K.subtype) := by
  have hc : (involutionCentralizer t).comap K.subtype = (action hn).fixedSubgroup := by
    ext x
    exact (mem_fixed_action hn x).symm
  rw [← relIndex_comap, hc]
  exact strict_relIndex_sylow _ R (four_dvd_fixedIndex_of_quotient _ b f hf heq hi)

/-- The bound transfers from K/O₂(K) without assuming that fixed points lift. -/
theorem strict_index_of_quotient_fixedIndex {K : Subgroup G} {t : G}
    (hn : t ∈ normalizer K) (hi : 4 ∣ (quotientAction hn).fixedSubgroup.index)
    (R : Sylow 2 K) :
    2 < (involutionCentralizer t).relIndex ((R : Subgroup K).map K.subtype) :=
  strict_index_of_model_fixedIndex hn (quotientAction hn) (QuotientGroup.mk' (pCore 2 K))
    (QuotientGroup.mk'_surjective _) (fun x => (quotientAction_apply hn x).symm) hi R

end CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic

