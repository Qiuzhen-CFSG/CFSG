module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.OrbitBaseChecks
/-!
# Kernel-checked generator transitions for the J₂ involution orbit

Seven-bit lookup tables for the three generator letters are proved equal
to the published permutations. Exhaustive Boolean checking then verifies
every point of every conjugation transition on the 315 candidate rows.
All reductions run in the kernel; the generated data supply no axioms.

Source: ATLAS `J2G1-p100B0`; candidate rows are in `OrbitData`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
open OrbitData
set_option maxRecDepth 100000
set_option Elab.async false

def letterPacked : Fin 3 → Nat :=
  ![470534163730062869911363024468043625726304620038018037366950930285973911676205782046213865496771569892128340730334015622028359153083123020292251731884913318734969411873230468091871540321808628302024410068142547, 3234967701574023288017704270913789399548845676982065206373928870228913752386975839948414443758577378205229365791802719998856417312117905715024748407215049785228781853510609863692219811450715825262485969147626773, 3377862216939204608209019933455681426219024363596881756892669536352030827785925351345362563460844105849526589246761354822075856259740605599629990671129056314103711580268098197814694108667979975332570640941909071]

def letterValue (s : Fin 3) (p : Fin 100) : Fin 100 :=
  ⟨(letterPacked s >>> (7 * p.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

theorem letterValue_eq : ∀ (s : Fin 3) (p : Fin 100),
    letterValue s p = permLetter s p := by
  decide +kernel

theorem letterValue_inv_eq : ∀ (s : Fin 3) (p : Fin 100),
    letterValue (invLetter s) p = (permLetter s)⁻¹ p := by
  decide +kernel

def checkSteps (lo count : Nat) : Bool :=
  (List.range count).all fun j =>
    if h : lo + j < 315 then
      checkFin (fun s : Fin 3 => checkFin (fun p : Fin 100 => decide
        (value (next ⟨lo + j, h⟩ s) p =
          letterValue (invLetter s) (value ⟨lo + j, h⟩ (letterValue s p)))))
    else true

theorem all_steps : checkSteps 0 315 = true := by
  decide +kernel

theorem value_step (i : Fin 315) (s : Fin 3) (p : Fin 100) :
    value (next i s) p = (permLetter s)⁻¹ (value i (permLetter s p)) := by
  have hi := List.all_eq_true.mp all_steps i.val (List.mem_range.mpr i.isLt)
  simp only [Nat.zero_add, dif_pos i.isLt] at hi
  have hs := allFin (fun s : Fin 3 => checkFin (fun p : Fin 100 => decide
    (value (next i s) p = letterValue (invLetter s) (value i (letterValue s p)))) = true)
    (by simpa only [Bool.decide_eq_true] using hi) s
  have hp := allFin (fun p : Fin 100 =>
    value (next i s) p = letterValue (invLetter s) (value i (letterValue s p))) hs p
  rw [letterValue_inv_eq, letterValue_eq] at hp
  exact hp

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
