module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.Check00
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.Check01
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.Check02
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.Check03

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/Thompson/Model/Simplicity/NormalGenerationHigh/source/generate.py`.
Source word: ATLAS Th conjugacy table, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/. -/

public section
namespace Thompson.Simplicity.Word31Certificate
open Subgroup.CosetWordCertificate

/-- All 16040 deductions follow from the actual model of the certificate. -/
theorem all_hold {G : Type*} [Group G] {H : Subgroup G}
    {g : (Fin 2) → G} {ρ : Nat → G}
    (valid : Valid context H g ρ) :
    ∀ n, n < 16040 → Holds H g ρ (facts n) := by
  have hall_0 := checkChunk_sound valid facts instructions 0 4096
    (fun n h => (Nat.not_lt_zero n h).elim) checked_0
  have hall_4096 := checkChunk_sound valid facts instructions 4096 4096
    hall_0 checked_4096
  have hall_8192 := checkChunk_sound valid facts instructions 8192 4096
    hall_4096 checked_8192
  have hall_12288 := checkChunk_sound valid facts instructions 12288 3752
    hall_8192 checked_12288
  exact hall_12288

end Thompson.Simplicity.Word31Certificate
