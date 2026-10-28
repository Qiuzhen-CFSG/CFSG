module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSevenCheck
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The partition and quotient in the A₇ branch

The partition is literally the three pairs `{01,23,45}` and singleton `{6}`.
Its stabilizer consists exactly of permutations commuting with `(01)(23)(45)`;
intersecting with A₇ defines the subgroup to be identified in 2.3.9(7)(c).

The quotient map uses an actual equivalence `K/Z(K) ≃ A₇`, and its kernel is
proved to be `Z(K)`. `ActsAsTripleSwap` records the literal induced action,
not a group-family label. The threefold cover must retain this kernel: the
intersection will embed into the quotient stabilizer, and cannot be identified
with its full inverse image.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation A.3.5 (p.43), Lemma 1.1.5(3)(d) (p.501), and 2.3.9(7)(c) (pp.525–526).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven

open Equiv Subgroup

abbrev A7 := alternatingGroup (Fin 7)
abbrev S7 := Perm (Fin 7)

abbrev tripleSwap : S7 := AlternatingSevenCheck.tripleSwap

/-- The literal stabilizer of `{01,23,45,6}`. -/
def partitionStabilizer : Subgroup S7 where
  carrier := {g | ∀ i j : Fin 7, (g i).val / 2 = (g j).val / 2 ↔ i.val / 2 = j.val / 2}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' {g h} hg hh i j := (hg (h i) (h j)).trans (hh i j)
  inv_mem' {g} hg i j := by
    simpa using (hg (g⁻¹ i) (g⁻¹ j)).symm

/-- Its subgroup of even permutations, inside the actual alternating group. -/
def alternatingStabilizer : Subgroup A7 :=
  partitionStabilizer.comap (alternatingGroup (Fin 7)).subtype

private theorem same_pair (i j : Fin 7) :
    i.val / 2 = j.val / 2 ↔ i = j ∨ tripleSwap i = j := by
  fin_cases i <;> fin_cases j <;> decide

/-- Preserving the three pairs and singleton is equivalent to commuting
with the involution interchanging each pair. -/
theorem partitionStabilizer_eq_centralizer :
    partitionStabilizer = centralizer ({tripleSwap} : Set S7) := by
  ext g
  change (∀ i j : Fin 7, (g i).val / 2 = (g j).val / 2 ↔ i.val / 2 = j.val / 2) ↔ _
  constructor
  · intro hg
    apply mem_centralizer_singleton_iff.mpr
    apply Equiv.ext
    intro i
    change g (tripleSwap i) = tripleSwap (g i)
    by_cases hi : tripleSwap i = i
    · have hrel : (g i).val / 2 = (g (g⁻¹ (tripleSwap (g i)))).val / 2 := by
        simp only [Perm.inv_def, Equiv.apply_symm_apply]
        exact (same_pair _ _).mpr (Or.inr rfl)
      have hr := (same_pair _ _).mp ((hg _ _).mp hrel)
      have he : i = g⁻¹ (tripleSwap (g i)) := by simpa only [hi, or_self] using hr
      simpa only [hi, Perm.inv_def, Equiv.apply_symm_apply] using congrArg g he
    · have hrel := (hg i (tripleSwap i)).mpr ((same_pair _ _).mpr (Or.inr rfl))
      rcases (same_pair _ _).mp hrel with he | he
      · exact (hi (g.injective he).symm).elim
      · exact he.symm
  · intro hg i j
    have hc : ∀ k, g (tripleSwap k) = tripleSwap (g k) :=
      fun k => congrArg (fun f : S7 => f k) (mem_centralizer_singleton_iff.mp hg)
    rw [same_pair, same_pair, ← hc, g.injective.eq_iff, g.injective.eq_iff]

@[simp] theorem mem_alternatingStabilizer (g : A7) :
    g ∈ alternatingStabilizer ↔ (g : S7) * tripleSwap = tripleSwap * (g : S7) := by
  change (g : S7) ∈ partitionStabilizer ↔ _
  rw [partitionStabilizer_eq_centralizer, mem_centralizer_singleton_iff]

variable {K : Type*} [Group K]

/-- The actual central quotient map, followed by the supplied A₇ equivalence. -/
def quotientMap (e : (K ⧸ center K) ≃* A7) : K →* A7 :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center K))

/-- Compatibility with the specified cycle type, in the coordinates of `e`. -/
def ActsAsTripleSwap (e : (K ⧸ center K) ≃* A7) (α : MulAut K) : Prop :=
  ∀ x : K, (quotientMap e (α x) : S7) =
    tripleSwap * (quotientMap e x : S7) * tripleSwap⁻¹

@[simp] theorem quotientMap_ker (e : (K ⧸ center K) ≃* A7) :
    (quotientMap e).ker = center K := by
  ext x
  change e ((QuotientGroup.mk' (center K)) x) = 1 ↔ x ∈ center K
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

theorem quotientMap_surjective (e : (K ⧸ center K) ≃* A7) :
    Function.Surjective (quotientMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective (center K))

end CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSeven

end
