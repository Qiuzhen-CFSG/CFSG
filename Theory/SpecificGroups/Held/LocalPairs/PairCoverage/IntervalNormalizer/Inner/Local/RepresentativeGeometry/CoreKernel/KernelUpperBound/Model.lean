module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.Words
/-!
# Generators for the native Held kernel certificate

The two generators are exactly those of the literal ATLAS local subgroup.
A six-cycle in the native action supplies five conjugate involutions. These
will give a stabilizer chain after quotienting by the kernel envelope.
No quotient order or abstract group identification is assumed.

Sources: GLS3 Table 5.3p; unchanged ATLAS max3/max4 and degree-2058 data.
-/

public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound
open Held.TwoLocalCandidates Subgroup
@[expose] def generator (i : Bool) (k : Fin 2) : localOvergroup i :=
  match i with
  | false => Cores.localGenerator 0 k
  | true => Cores.localGenerator 1 k

theorem generator_closure (i : Bool) : closure (Set.range (generator i)) = ⊤ := by
  cases i
  · exact Cores.localGenerator_closure 0
  · exact Cores.localGenerator_closure 1

@[expose] def generatorPerm (i : Bool) (k : Fin 2) : Equiv.Perm (Fin 2058) :=
  if i then ![Cores.Tables1.p0, Cores.Tables1.p1] k
  else ![Cores.Tables0.p0, Cores.Tables0.p1] k

theorem representation_generator (i : Bool) (k : Fin 2) :
    representation (generator i k).val = generatorPerm i k := by
  cases i <;> fin_cases k
  · exact Cores.Tables0.p0_eq.symm
  · exact Cores.Tables0.p1_eq.symm
  · exact Cores.Tables1.p0_eq.symm
  · exact Cores.Tables1.p1_eq.symm

@[expose] def cycle (i : Bool) : localOvergroup i :=
  if i then generator i 0 * generator i 1 else generator i 1
@[expose] def adjacent (i : Bool) (k : Fin 5) : localOvergroup i :=
  cycle i ^ k.val * generator i 0 * (cycle i ^ k.val)⁻¹
@[expose] def cyclePerm (i : Bool) : Equiv.Perm (Fin 2058) :=
  if i then generatorPerm i 0 * generatorPerm i 1 else generatorPerm i 1

theorem representation_cycle (i : Bool) : representation (cycle i).val = cyclePerm i := by
  cases i <;> simp only [cycle, cyclePerm, Bool.false_eq_true, ↓reduceIte,
    coe_mul, map_mul, representation_generator]

theorem representation_adjacent (i : Bool) (k : Fin 5) :
    representation (adjacent i k).val =
      cyclePerm i ^ k.val * generatorPerm i 0 * (cyclePerm i ^ k.val)⁻¹ := by
  simp only [adjacent, coe_mul, coe_inv, coe_pow, map_mul, map_inv, map_pow,
    representation_cycle, representation_generator]

theorem generator_zero_square (i : Bool) : generator i 0 * generator i 0 = 1 := by
  apply Subtype.val_injective
  cases i <;> exact (pow_two Held.a).symm.trans Held.a_sq

theorem adjacent_square (i : Bool) (k : Fin 5) : adjacent i k * adjacent i k = 1 := by
  simp only [adjacent, mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc (generator i 0), generator_zero_square, one_mul, mul_inv_cancel]

@[expose] def correction (i : Bool) (w : List (Fin 7)) (e : Nat) : localOvergroup i :=
  (w.map (coreGenerator i)).prod * kernelThird i ^ e

theorem correction_mem (i : Bool) (w : List (Fin 7)) (e : Nat) :
    correction i w e ∈ kernelEnvelope i := by
  apply (kernelEnvelope i).mul_mem
  · apply (show wordCore i ≤ kernelEnvelope i from le_sup_left)
    exact (wordCore i).list_prod_mem (fun x hx => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      exact coreGenerator_mem i k)
  · exact (show zpowers (kernelThird i) ≤ kernelEnvelope i from le_sup_right)
      (pow_mem (mem_zpowers _) _)
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound
