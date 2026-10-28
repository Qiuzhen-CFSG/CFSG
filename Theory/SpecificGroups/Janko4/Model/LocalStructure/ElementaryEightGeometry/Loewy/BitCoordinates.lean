module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.IsotropicCode
public import Batteries.Data.Fin.OfBits

public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open GeneratorCertificates

/-- All eight binary coefficients have an actual eight-bit mask. -/
theorem exists_mask_bits (c : Fin 8 → ZMod 2) :
    ∃ m : Fin 256, ∀ i : Fin 8, bit m.val i.val = c i := by
  let f : Fin 8 → Bool := fun i => decide (c i = 1)
  refine ⟨⟨Nat.ofBits f, Nat.ofBits_lt_two_pow f⟩,?_⟩
  intro i
  change (if (Nat.ofBits f).testBit i.val then (1 : ZMod 2) else 0) = c i
  rw [Nat.testBit_ofBits_lt f i.val i.isLt]
  change (if decide (c i = 1) then (1 : ZMod 2) else 0) = c i
  by_cases hi : c i = 1
  · simp only [hi, decide_true, if_pos]
  · have hz : c i = 0 := by
      have hc : c i = 0 ∨ c i = 1 := by
        have hh : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
        exact hh _
      exact hc.resolve_right hi
    rw [if_neg (by simpa only [decide_eq_true_eq] using hi)]
    exact hz.symm

theorem exists_mask_coordinates (a b : Fin 4 → ZMod 2) :
    ∃ m : Fin 256, (fun i : Fin 4 => bit m.val i.val) = a ∧
      (fun i : Fin 4 => bit m.val (4+i.val)) = b := by
  obtain ⟨m,hm⟩ := exists_mask_bits
    (Fin.addCases (m := 4) (n := 4) (motive := fun _ => ZMod 2) a b)
  refine ⟨m,?_,?_⟩
  · funext i
    simpa only [Fin.addCases_left, Fin.val_castAdd] using hm (Fin.castAdd 4 i)
  · funext i
    simpa only [Fin.addCases_right, Fin.val_natAdd] using hm (Fin.natAdd 4 i)

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
