module
public import Theory.Representation.BinaryPermutation.SixCoreOrbits
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry

/-!
# Point radicals on the five-dimensional six-letter core

The weight-two and weight-four orbits give the same full duad stabilizers.
For any permutation subgroup containing A₆, its vector stabilizer is normal
in the corresponding S₆ stabilizer, since all commutators are even. Relative
normality therefore puts its two-core inside the full duad two-core, an even
conjugate of C₂ times the complementary Klein four. The original core is
used throughout; no natural-quotient subgroup is substituted for it.

Source: Aschbacher–Smith B.3.4 and 13.2.2(6), printed pp.84–85,877.
-/

public noncomputable section
namespace BinaryPermutation.SixCorePoint
open Subgroup BinaryNaturalDual.VectorStabilizers
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement
abbrev S := Equiv.Perm (Fin 6)
abbrev W := core (Fin 6)
abbrev rho := coreRepresentation (Fin 6)
abbrev stabilizer (w : W) := representationStabilizer rho w
private def pairWord : W := ⟨![0,0,0,0,1,1],by rw [mem_core];decide⟩
private theorem pairWord_ne_zero : pairWord ≠ 0 := by decide
private theorem pairWord_ne_constant : pairWord ≠ sixCoreConstant := by decide
private theorem pair_stabilizer : stabilizer pairWord = H1 := by
  ext a
  change rho a pairWord = pairWord ↔ a ∈ H1
  revert a
  decide +kernel
private theorem stabilizer_complement (w : W) :
    stabilizer (w + sixCoreConstant) = stabilizer w := by
  have hc (a : S) : rho a sixCoreConstant = sixCoreConstant := by
    apply Subtype.ext
    funext i
    rfl
  ext a
  change rho a (w + sixCoreConstant) = w + sixCoreConstant ↔ rho a w = w
  rw [map_add,hc,add_left_inj]
private theorem stabilizer_conjugate (a : S) (w : W) :
    (stabilizer w).map (MulAut.conj a).toMonoidHom = stabilizer (rho a w) := by
  ext b
  constructor
  · rintro ⟨g,hg,rfl⟩
    change rho (a*g*a⁻¹) (rho a w) = rho a w
    rw [← Module.End.mul_apply,← map_mul]
    simp only [mul_assoc,inv_mul_cancel,mul_one,map_mul,Module.End.mul_apply]
    rw [hg]
  · intro hb
    refine ⟨a⁻¹*b*a,?_,by simp [MulAut.conj_apply,mul_assoc]⟩
    change rho (a⁻¹*b*a) w = w
    rw [map_mul,Module.End.mul_apply,map_mul,Module.End.mul_apply]
    change rho b (rho a w) = rho a w at hb
    rw [hb,← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one]
    rfl

/-- Both weights have the same literal duad stabilizer up to an even conjugate. -/
theorem exists_point_stabilizer (w : W)
    (hw : ¬ ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a w = w) :
    ∃ a : alternatingGroup (Fin 6), stabilizer w = H1.map (MulAut.conj a.val).toMonoidHom := by
  have hw := not_or.mp ((not_congr (sixCore_fixed_iff w)).mp hw)
  rcases sixCore_paired_orbits pairWord w pairWord_ne_zero pairWord_ne_constant hw.1 hw.2 with
    ⟨a,ha⟩ | ⟨a,ha⟩
  · refine ⟨a,?_⟩
    rw [←pair_stabilizer,stabilizer_conjugate]
    exact congrArg stabilizer ha.symm
  · refine ⟨a,?_⟩
    rw [←pair_stabilizer,←stabilizer_complement pairWord,stabilizer_conjugate]
    exact congrArg stabilizer ha.symm

/-- A subgroup containing A6 has a point radical contained in the full S6
point radical. This uses relative normality, not ambient normality. -/
theorem point_core_le (Y : Subgroup S) (hY : alternatingGroup (Fin 6) ≤ Y) (w : W) :
    (stabilizer w ⊓ Y).pCoreIn 2 ≤ (stabilizer w).pCoreIn 2 := by
  apply pCoreIn_mono_of_normalizes inf_le_left
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
  constructor
  intro n hn g
  change (g : S) * (n : S) * (g : S)⁻¹ ∈ stabilizer w ⊓ Y
  refine ⟨(stabilizer w).mul_mem ((stabilizer w).mul_mem g.property n.property)
    ((stabilizer w).inv_mem g.property),?_⟩
  change (g : S) * (n : S) * (g : S)⁻¹ ∈ Y
  change (n : S) ∈ stabilizer w ⊓ Y at hn
  have hc : ⁅(g : S),(n : S)⁆ ∈ Y := hY (by
    change Equiv.Perm.sign ⁅(g : S),(n : S)⁆ = 1
    simp [commutatorElement_def,mul_assoc,mul_left_comm,mul_comm])
  simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using Y.mul_mem hc hn.2

/-- The actual point radical for either A6 or S6 lies in the conjugate of
C2 times the complementary Klein four, for either nonconstant weight. -/
theorem exists_point_core_bound (Y : Subgroup S) (hY : alternatingGroup (Fin 6) ≤ Y)
    (w : W)
    (hw : ¬ ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a w = w) :
    ∃ a : alternatingGroup (Fin 6),
      (stabilizer w ⊓ Y).pCoreIn 2 ≤ pointCore.map (MulAut.conj a.val).toMonoidHom := by
  obtain ⟨a,ha⟩ := exists_point_stabilizer w hw
  refine ⟨a,(point_core_le Y hY w).trans_eq ?_⟩
  rw [ha,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj a.val).injective,H1_core_eq_pointCore]
end BinaryPermutation.SixCorePoint
