module

public import Theory.Representation.BinaryPermutation.SixCoreOrbits
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad

/-!
# Stabilizers of nonfixed vectors in the six-letter augmentation core

Every nonfixed vector is an even-permutation conjugate of the word of
weight two supported on {0,1}, or of its complement. The two words have
the same stabilizer. The literal duad stabilizer in A₆ is S₄, whose quotient
by its two-core is S₃. Conjugation transports this quotient without
replacing the five-dimensional core by its four-dimensional natural quotient.

The source application identifies C_L(z)/O₂(C_L(z)) in the ordinary row
of Aschbacher–Smith 13.4.8, printed pp.904–905.
-/

@[expose] public noncomputable section
open Subgroup BinaryNaturalDual.VectorStabilizers
namespace BinaryPermutation.SixCoreStabilizer
abbrev A := alternatingGroup (Fin 6)
abbrev W := core (Fin 6)
abbrev rho := alternatingCoreRepresentation (Fin 6)
abbrev stabilizer (w : W) := representationStabilizer rho w
private def pairWord : W := ⟨![1,1,0,0,0,0],by rw [mem_core];decide⟩
private theorem pairWord_ne_zero : pairWord ≠ 0 := by decide
private theorem pairWord_ne_constant : pairWord ≠ sixCoreConstant := by decide
private theorem pair_stabilizer : stabilizer pairWord =
    Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer := by
  ext a
  change rho a pairWord = pairWord ↔
    a.val ∈ Theory.SpecificGroups.SymmetricSix.duadStabilizer
  revert a
  decide +kernel

private theorem stabilizer_complement (w : W) :
    stabilizer (w + sixCoreConstant) = stabilizer w := by
  ext a
  change rho a (w + sixCoreConstant) = w + sixCoreConstant ↔ rho a w = w
  rw [map_add,sixCoreConstant_fixed,add_left_inj]

private theorem stabilizer_conjugate (a : A) (w : W) :
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

/-- Every nonfixed vector in the original five-space has an S3 quotient stabilizer. -/
theorem quotient_equiv (w : W) (hfix : ¬ ∀ a : A, rho a w = w) :
    Nonempty ((stabilizer w ⧸ pCore 2 (stabilizer w)) ≃* Equiv.Perm (Fin 3)) := by
  have hw := not_or.mp ((not_congr (sixCore_fixed_iff w)).mp hfix)
  have model : ∀ u : W, stabilizer u = stabilizer pairWord →
      (∃ a : A, rho a u = w) →
      Nonempty ((stabilizer w ⧸ pCore 2 (stabilizer w)) ≃* Equiv.Perm (Fin 3)) := by
    intro u hu ⟨a,ha⟩
    have he := stabilizer_conjugate a u
    rw [ha] at he
    let e : stabilizer w ≃* Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer :=
      (MulEquiv.subgroupCongr he.symm).trans
        (((stabilizer u).equivMapOfInjective (MulAut.conj a).toMonoidHom
          (MulAut.conj a).injective).symm.trans (MulEquiv.subgroupCongr (hu.trans pair_stabilizer)))
    exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      Theory.SpecificGroups.SymmetricSix.a6DuadCoreQuotientEquiv⟩
  rcases sixCore_paired_orbits pairWord w pairWord_ne_zero pairWord_ne_constant hw.1 hw.2 with h | h
  · exact model pairWord rfl h
  · exact model (pairWord + sixCoreConstant) (stabilizer_complement pairWord) h
end BinaryPermutation.SixCoreStabilizer
