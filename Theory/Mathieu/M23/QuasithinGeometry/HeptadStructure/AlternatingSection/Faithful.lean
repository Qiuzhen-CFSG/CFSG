module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Basic

/-!
# Faithfulness of the heptad action after fixing a complementary point

For each point outside the heptad other than 0, three certified blocks
intersect in precisely that point and 0. Each block contains three points of
the heptad together with 0, so is determined by these four fixed points. Their intersections establish faithfulness.

Source: Aschbacher, *Sporadic Groups*, Chapter 6, Lemma 19.1(3), in the M23
specialization. The intersection certificates use this project's Witt design.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.AlternatingSection
open scoped Pointwise
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def anchor0 : Fin 23 → Fin 253 :=
  ![0, 0, 0, 0, 0, 0, 9, 9, 9, 8, 4, 0, 19, 19, 19, 8, 4, 0, 20, 20, 20, 8, 4]

private def anchor1 : Fin 23 → Fin 253 :=
  ![0, 0, 0, 0, 0, 0, 30, 32, 22, 32, 44, 0, 28, 30, 22, 30, 40, 0, 32, 28, 22, 28, 42]

private def anchor2 : Fin 23 → Fin 253 :=
  ![0, 0, 0, 0, 0, 0, 86, 78, 88, 88, 100, 0, 88, 78, 84, 84, 98, 0, 84, 78, 86, 86, 96]

private def anchor (q : Fin 23) : Fin 3 → Fin 253 :=
  ![anchor0 q, anchor1 q, anchor2 q]

private theorem anchor_card : ∀ q : Fin 23, q ∉ omega → q ≠ 0 →
    ∀ j : Fin 3, (insert 0 (omega ∩ m23BlockAt (anchor q j))).card = 4 := by
  decide +kernel

private theorem anchor_subset : ∀ q : Fin 23, q ∉ omega → q ≠ 0 →
    ∀ j : Fin 3, insert 0 (omega ∩ m23BlockAt (anchor q j)) ⊆
      m23BlockAt (anchor q j) := by
  decide +kernel

private theorem anchor_inter : ∀ q : Fin 23, q ∉ omega → q ≠ 0 →
    m23BlockAt (anchor q 0) ∩ m23BlockAt (anchor q 1) ∩
      m23BlockAt (anchor q 2) = {0, q} := by
  decide +kernel

/-- An automorphism fixing the heptad pointwise and point 0 is the identity. -/
theorem eq_one_of_fixes (g : M23) (h0 : g • (0 : Fin 23) = 0)
    (h : ∀ q ∈ omega, g • q = q) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro q
  change g • q = q
  by_cases hq : q ∈ omega
  · exact h q hq
  by_cases hq0 : q = 0
  · subst q; exact h0
  have hB (j : Fin 3) : g • m23BlockAt (anchor q j) = m23BlockAt (anchor q j) := by
    apply MulAction.mem_stabilizer_iff.mp
    apply four_stabilizer_le_heptad_stabilizer (anchor_card q hq hq0 j)
      (Finset.mem_image.mpr ⟨anchor q j, Finset.mem_univ _, rfl⟩)
      (anchor_subset q hq hq0 j)
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    have hf : g • a = a := by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact h0
      · exact h a (Finset.mem_inter.mp ha).1
    rwa [hf]
  have hp : g • ({0, q} : Finset (Fin 23)) = {0, q} := by
    rw [← anchor_inter q hq hq0, Finset.smul_finset_inter,
      Finset.smul_finset_inter, hB, hB, hB]
  have hm : g • q ∈ ({0, q} : Finset (Fin 23)) := by
    rw [← hp]
    exact Finset.smul_mem_smul_finset (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact False.elim (hq0 (g.val.injective (hm.trans h0.symm)))
  · exact hm

/-- The subgroup fixing the chosen point 0 outside the heptad. -/
noncomputable abbrev pointComplement := MulAction.stabilizer heptadStabilizer (0 : Fin 23)

/-- Its actual action on the source labels. -/
noncomputable def pointAction : pointComplement →* Equiv.Perm (Fin 7) :=
  heptadAction.comp pointComplement.subtype

/-- Fixing point 0 makes the labelled heptad action faithful. -/
theorem pointAction_injective : Function.Injective pointAction := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  apply Subtype.ext
  apply Subtype.ext
  apply eq_one_of_fixes
  · exact MulAction.mem_stabilizer_iff.mp g.property
  · exact (mem_heptadKernel g.val).mp hg

end Sporadic.Mathieu.M23Geometry.AlternatingSection
