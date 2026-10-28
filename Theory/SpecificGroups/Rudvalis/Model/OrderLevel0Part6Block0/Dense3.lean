module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps
import Mathlib.Tactic.FinCases

/-!
# Dense transitions in Rudvalis part-6 block 0, rows 75--99

The cached factor maps from `FactorMaps` reduce each transition to its 203
twenty-point slices. The representative words are taken directly from the
published `FactorWords` rows, so the finite checks certify every point of each
transition without re-evaluating the long factor words.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense3
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

private theorem row75 :
    stepCheck (FactorWords.row ⟨75, by decide⟩).1
      (FactorWords.row ⟨75, by decide⟩).2 := by
  let n : Fin 100 := ⟨75, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row76 :
    stepCheck (FactorWords.row ⟨76, by decide⟩).1
      (FactorWords.row ⟨76, by decide⟩).2 := by
  let n : Fin 100 := ⟨76, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row77 :
    stepCheck (FactorWords.row ⟨77, by decide⟩).1
      (FactorWords.row ⟨77, by decide⟩).2 := by
  let n : Fin 100 := ⟨77, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row78 :
    stepCheck (FactorWords.row ⟨78, by decide⟩).1
      (FactorWords.row ⟨78, by decide⟩).2 := by
  let n : Fin 100 := ⟨78, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row79 :
    stepCheck (FactorWords.row ⟨79, by decide⟩).1
      (FactorWords.row ⟨79, by decide⟩).2 := by
  let n : Fin 100 := ⟨79, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row80 :
    stepCheck (FactorWords.row ⟨80, by decide⟩).1
      (FactorWords.row ⟨80, by decide⟩).2 := by
  let n : Fin 100 := ⟨80, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row81 :
    stepCheck (FactorWords.row ⟨81, by decide⟩).1
      (FactorWords.row ⟨81, by decide⟩).2 := by
  let n : Fin 100 := ⟨81, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row82 :
    stepCheck (FactorWords.row ⟨82, by decide⟩).1
      (FactorWords.row ⟨82, by decide⟩).2 := by
  let n : Fin 100 := ⟨82, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row83 :
    stepCheck (FactorWords.row ⟨83, by decide⟩).1
      (FactorWords.row ⟨83, by decide⟩).2 := by
  let n : Fin 100 := ⟨83, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row84 :
    stepCheck (FactorWords.row ⟨84, by decide⟩).1
      (FactorWords.row ⟨84, by decide⟩).2 := by
  let n : Fin 100 := ⟨84, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row85 :
    stepCheck (FactorWords.row ⟨85, by decide⟩).1
      (FactorWords.row ⟨85, by decide⟩).2 := by
  let n : Fin 100 := ⟨85, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row86 :
    stepCheck (FactorWords.row ⟨86, by decide⟩).1
      (FactorWords.row ⟨86, by decide⟩).2 := by
  let n : Fin 100 := ⟨86, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row87 :
    stepCheck (FactorWords.row ⟨87, by decide⟩).1
      (FactorWords.row ⟨87, by decide⟩).2 := by
  let n : Fin 100 := ⟨87, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row88 :
    stepCheck (FactorWords.row ⟨88, by decide⟩).1
      (FactorWords.row ⟨88, by decide⟩).2 := by
  let n : Fin 100 := ⟨88, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row89 :
    stepCheck (FactorWords.row ⟨89, by decide⟩).1
      (FactorWords.row ⟨89, by decide⟩).2 := by
  let n : Fin 100 := ⟨89, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row90 :
    stepCheck (FactorWords.row ⟨90, by decide⟩).1
      (FactorWords.row ⟨90, by decide⟩).2 := by
  let n : Fin 100 := ⟨90, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row91 :
    stepCheck (FactorWords.row ⟨91, by decide⟩).1
      (FactorWords.row ⟨91, by decide⟩).2 := by
  let n : Fin 100 := ⟨91, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row92 :
    stepCheck (FactorWords.row ⟨92, by decide⟩).1
      (FactorWords.row ⟨92, by decide⟩).2 := by
  let n : Fin 100 := ⟨92, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row93 :
    stepCheck (FactorWords.row ⟨93, by decide⟩).1
      (FactorWords.row ⟨93, by decide⟩).2 := by
  let n : Fin 100 := ⟨93, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row94 :
    stepCheck (FactorWords.row ⟨94, by decide⟩).1
      (FactorWords.row ⟨94, by decide⟩).2 := by
  let n : Fin 100 := ⟨94, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row95 :
    stepCheck (FactorWords.row ⟨95, by decide⟩).1
      (FactorWords.row ⟨95, by decide⟩).2 := by
  let n : Fin 100 := ⟨95, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row96 :
    stepCheck (FactorWords.row ⟨96, by decide⟩).1
      (FactorWords.row ⟨96, by decide⟩).2 := by
  let n : Fin 100 := ⟨96, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row97 :
    stepCheck (FactorWords.row ⟨97, by decide⟩).1
      (FactorWords.row ⟨97, by decide⟩).2 := by
  let n : Fin 100 := ⟨97, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row98 :
    stepCheck (FactorWords.row ⟨98, by decide⟩).1
      (FactorWords.row ⟨98, by decide⟩).2 := by
  let n : Fin 100 := ⟨98, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

private theorem row99 :
    stepCheck (FactorWords.row ⟨99, by decide⟩).1
      (FactorWords.row ⟨99, by decide⟩).2 := by
  let n : Fin 100 := ⟨99, by decide⟩
  let w := L0RepWord (FactorWords.row n).2
  let v := L0RepWord (L0Act ((FactorWords.row n).1.castLE (by decide))
    (FactorWords.row n).2)
  apply FactorMaps.ofSlices n w v
  · rfl
  · rfl
  · intro b
    fin_cases b <;> decide +kernel

public theorem checked (k : Fin 25) :
    stepCheck (FactorWords.row ⟨k.val + 75, by omega⟩).1
      (FactorWords.row ⟨k.val + 75, by omega⟩).2 := by
  fin_cases k
  · exact row75
  · exact row76
  · exact row77
  · exact row78
  · exact row79
  · exact row80
  · exact row81
  · exact row82
  · exact row83
  · exact row84
  · exact row85
  · exact row86
  · exact row87
  · exact row88
  · exact row89
  · exact row90
  · exact row91
  · exact row92
  · exact row93
  · exact row94
  · exact row95
  · exact row96
  · exact row97
  · exact row98
  · exact row99

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense3

