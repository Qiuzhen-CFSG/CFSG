module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneChart

/-!
# The 77 native hexads under a fixed hexad stabilizer

Two words in the original degree-22 Mathieu generators give three orbits.
A 77-entry forest certifies the transporters. The checks use the existing
hexad table and literal point permutations; no group enumeration is used.
Source: Aschbacher–Segev (1991), (5.3)(1), p.600.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeHexads
open Sporadic.Mathieu
open scoped Pointwise

noncomputable def generator : Fin 2 → M22 :=
  ![m22GeneratorBInM22⁻¹ * m22GeneratorAInM22 * m22GeneratorBInM22⁻¹ * m22GeneratorAInM22 * m22GeneratorBInM22⁻¹ * m22GeneratorAInM22 * m22GeneratorBInM22 * m22GeneratorAInM22 * m22GeneratorBInM22 * m22GeneratorAInM22 * m22GeneratorBInM22,m22GeneratorBInM22⁻¹ * m22GeneratorBInM22⁻¹ * m22GeneratorAInM22 * m22GeneratorBInM22⁻¹ * m22GeneratorAInM22 * m22GeneratorBInM22 * m22GeneratorAInM22 * m22GeneratorBInM22⁻¹ * m22GeneratorAInM22 * m22GeneratorBInM22 * m22GeneratorAInM22 * m22GeneratorBInM22⁻¹]
def table : Fin 2 → Fin 22 → Fin 22 :=
  ![![0,1,2,20,21,19,14,15,8,9,18,13,16,11,6,7,12,17,10,5,3,4],![8,2,18,20,13,12,9,19,14,11,3,16,5,0,21,17,7,15,1,6,10,4]]
theorem generator_apply (i : Fin 2) (x : Fin 22) : (generator i).val x = table i x := by
  revert i x; decide +kernel
theorem generator_fixes (i : Fin 2) : generator i • m22Hexad123 = m22Hexad123 := by
  change m22Hexad123.image (generator i).val = m22Hexad123
  have hg : (generator i).val = table i := funext (generator_apply i)
  rw [hg]
  revert i; decide +kernel
def parent : Fin 77 → Fin 77 := ![0,1,16,15,9,14,63,19,12,18,20,6,39,16,47,27,28,15,51,40,34,18,10,32,17,24,14,1,35,27,34,2,8,22,3,12,21,70,42,29,35,43,51,37,48,56,59,30,56,49,74,24,60,75,49,36,38,49,71,43,66,54,58,25,37,71,61,52,63,32,39,53,21,40,53,54,22]
def letter : Fin 77 → Fin 2 := ![0,0,1,1,1,0,1,0,0,0,0,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,1,0,0,0,1,1,0,1,1,0,1,1,1,1,0,0,1,1,0,1,1,1,0,1,1,0,1,1,1,1,0,0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,0,0,0,1]
def depth : Fin 77 → Nat := ![0,0,8,3,8,8,7,8,5,7,6,8,4,8,7,2,7,3,6,7,5,7,7,7,4,5,8,1,6,2,5,9,6,8,4,5,8,5,7,3,6,7,6,6,10,9,8,6,9,0,5,5,5,3,1,9,8,1,5,7,4,2,6,6,6,5,3,6,7,7,4,4,8,7,4,2,8]
def root : Fin 77 → Fin 77 := ![0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,49,49,1,49,49,49,1,1,49,49,1,49,49,49,1,1,49,49,49,1,1,1,49,1,1,49,49,1]
theorem forest : ∀ i : Fin 77,
    (depth i = 0 → i = root i) ∧
    (depth i ≠ 0 → depth (parent i) < depth i ∧ root (parent i) = root i ∧
      ∀ x : Fin 22, (m22BlockMask (parent i)).testBit x.val =
        (m22BlockMask i).testBit (table (letter i) x).val) := by
  decide +kernel
theorem root_card : ∀ i : Fin 77,
    root i = (if (m22BlockAt i ∩ m22Hexad123).card = 6 then 0
      else if (m22BlockAt i ∩ m22Hexad123).card = 2 then 1 else 49) := by
  decide +kernel
theorem root_sizes :
    (Finset.univ.filter (fun i : Fin 77 => root i = 1)).card = 60 ∧
    (Finset.univ.filter (fun i : Fin 77 => root i = 49)).card = 16 := by
  decide +kernel

theorem intersection_cases : ∀ i : Fin 77,
    (m22BlockAt i ∩ m22Hexad123).card = 0 ∨
    (m22BlockAt i ∩ m22Hexad123).card = 2 ∨ m22BlockAt i = m22Hexad123 := by
  decide +kernel
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeHexads
