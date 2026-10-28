module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeSylow

/-!
# Stabilizers of Sylow-fixed vectors in the natural eight-point module

A nonzero vector in the natural binary module for S₈ fixed by a Sylow
2-subgroup has stabilizer conjugate to the stabilizer of the unordered
partition `{0,1,2,3}|{4,5,6,7}`.

For the binary-tree Sylow subgroup, the first six generators have fixed
coordinates, so fixing a class modulo constants forces them to fix every
representative. Their coordinate equalities make each representative constant
on the two four-point blocks. A nonzero class has distinct values on those
blocks. Over F₂, fixing the class is exactly preserving its coordinate equality
relation, hence exactly preserving the unordered partition. Sylow conjugacy
transports this calculation with conjugation oriented as `r * g * r⁻¹`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.3.1–2, printed pp.83–84; the concrete stabilizer
calculation used in 15.3.32(1),(4), printed pp.1132–1133.
-/

public section

namespace BinaryPermutation.EightSylowFixed

open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

private theorem first_six_fixed_point :
    ∀ j : Fin 6, ∃ i : Fin 8, treeGenerator j.castSucc i = i := by decide

private theorem binary_relation (a b c d : ZMod 2) :
    (a = b ↔ c = d) ↔ a - c = b - d := by
  revert a b c d
  decide

private theorem first_six_coordinates (w : Full (Fin 8))
    (h : ∀ j : Fin 6, representation (Fin 8) (treeGenerator j.castSucc) w = w) :
    ∀ i : Fin 8, w i = if i.val < 4 then w 0 else w 4 := by
  have h01 := congrFun (h 0) 0
  have h23 := congrFun (h 1) 2
  have h45 := congrFun (h 2) 4
  have h67 := congrFun (h 3) 6
  have h02 := congrFun (h 4) 0
  have h46 := congrFun (h 5) 4
  change w 1 = w 0 at h01
  change w 3 = w 2 at h23
  change w 5 = w 4 at h45
  change w 7 = w 6 at h67
  change w 2 = w 0 at h02
  change w 6 = w 4 at h46
  intro i
  fin_cases i <;> simp_all

private theorem deleted_fixed_iff_relation (g : S8) (w : Full (Fin 8)) :
    deletedRepresentation (Fin 8) g ((constants (Fin 8)).mkQ w) =
      (constants (Fin 8)).mkQ w ↔
      ∀ i j, w (g i) = w (g j) ↔ w i = w j := by
  rw [deleted_fixed_iff]
  constructor
  · rintro ⟨c, hc⟩ i j
    apply (binary_relation _ _ _ _).mpr
    have hi := hc (g i)
    have hj := hc (g j)
    simp only [Equiv.symm_apply_apply] at hi hj
    simpa only [neg_sub] using congrArg Neg.neg (hi.trans hj.symm)
  · intro h
    refine ⟨w (g.symm 0) - w 0, fun i => ?_⟩
    apply (binary_relation _ _ _ _).mp
    simpa only [Equiv.apply_symm_apply] using (h (g.symm i) (g.symm 0)).symm

/-- The stabilizer of a nonzero natural vector fixed by the binary-tree
Sylow subgroup is the unordered four-block stabilizer. -/
theorem tree_fixed_stabilizer (v : natural (Fin 8)) (hv : v ≠ 0)
    (hfixed : ∀ g ∈ treeGroup, naturalRepresentation (Fin 8) g v = v) :
    ∀ g : S8, naturalRepresentation (Fin 8) g v = v ↔ g ∈ fourStabilizer := by
  obtain ⟨w, _, hrep⟩ := v.property
  have hdel (g : S8) (hg : g ∈ treeGroup) :
      deletedRepresentation (Fin 8) g ((constants (Fin 8)).mkQ w) =
        (constants (Fin 8)).mkQ w := by
    rw [hrep]
    exact congrArg Subtype.val (hfixed g hg)
  have hcoords := first_six_coordinates w (fun j => by
    obtain ⟨i, hi⟩ := first_six_fixed_point j
    exact (deleted_fixed_iff_of_fixed_point _ w i hi).mp
      (hdel _ (treeGenerator_mem j.castSucc)))
  have hne : w 0 ≠ w 4 := by
    intro hh
    apply hv
    apply Subtype.ext
    change v.val = 0
    rw [← hrep]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (mem_constants_iff w).mpr
    refine ⟨w 0, fun i => ?_⟩
    rw [hcoords i, hh]
    simp
  have hrel (i j : Fin 8) : w i = w j ↔ i.val / 4 = j.val / 4 := by
    rw [hcoords i, hcoords j]
    fin_cases i <;> fin_cases j <;> simp [hne, Ne.symm hne]
  intro g
  rw [Subtype.ext_iff, naturalRepresentation_apply, ← hrep, deleted_fixed_iff_relation,
    mem_fourStabilizer]
  simp only [hrel]

private noncomputable def treeSylow : Sylow 2 S8 :=
  (IsPGroup.of_card (show Nat.card treeGroup = 2 ^ 7 from card_treeGroup)).toSylow (by
    have hi := treeGroup.card_mul_index
    have hc : Nat.card S8 = 40320 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [card_treeGroup, hc] at hi
    have hindex : treeGroup.index = 315 := by omega
    rw [hindex]
    decide)

private theorem apply_inv_apply (r : S8) (v : natural (Fin 8)) :
    naturalRepresentation (Fin 8) r⁻¹ (naturalRepresentation (Fin 8) r v) = v := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem action_injective (r : S8) :
    Function.Injective (naturalRepresentation (Fin 8) r) := by
  intro x y h
  have := congrArg (naturalRepresentation (Fin 8) r⁻¹) h
  simpa only [apply_inv_apply] using this

private theorem conjugate_apply (r g : S8) (v : natural (Fin 8)) :
    naturalRepresentation (Fin 8) (r * g * r⁻¹)
      (naturalRepresentation (Fin 8) r v) =
      naturalRepresentation (Fin 8) r (naturalRepresentation (Fin 8) g v) := by
  simp only [map_mul, Module.End.mul_apply, apply_inv_apply]

/-- Every nonzero Sylow-fixed natural vector has a conjugate four-block
stabilizer, with the conjugation orientation used to transport a marking. -/
theorem exists_conjugate_stabilizer (Q : Sylow 2 S8) (v : natural (Fin 8))
    (hv : v ≠ 0)
    (hfixed : ∀ g ∈ (Q : Subgroup S8), naturalRepresentation (Fin 8) g v = v) :
    ∃ r : S8, ∀ g : S8, naturalRepresentation (Fin 8) g v = v ↔
      r * g * r⁻¹ ∈ fourStabilizer := by
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq S8 Q treeSylow
  have hmap : (Q : Subgroup S8).map (MulAut.conj r).toMonoidHom = treeGroup := by
    change ((r • Q : Sylow 2 S8) : Subgroup S8) = (treeSylow : Subgroup S8)
    rw [hr]
  have hn : naturalRepresentation (Fin 8) r v ≠ 0 := by
    intro hz
    apply hv
    apply action_injective r
    simpa only [map_zero] using hz
  have ht : ∀ g ∈ treeGroup, naturalRepresentation (Fin 8) g
      (naturalRepresentation (Fin 8) r v) = naturalRepresentation (Fin 8) r v := by
    intro g hg
    rw [← hmap] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    change naturalRepresentation (Fin 8) (r * a * r⁻¹)
      (naturalRepresentation (Fin 8) r v) = naturalRepresentation (Fin 8) r v
    rw [conjugate_apply, hfixed a ha]
  refine ⟨r, fun g => ?_⟩
  rw [← tree_fixed_stabilizer _ hn ht, conjugate_apply]
  exact (action_injective r).eq_iff.symm

end BinaryPermutation.EightSylowFixed
