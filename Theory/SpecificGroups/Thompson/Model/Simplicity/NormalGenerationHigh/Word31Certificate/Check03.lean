module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.Context
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.factsTable
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/Thompson/Model/Simplicity/NormalGenerationHigh/source/generate.py`.
Source word: ATLAS Th conjugacy table, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/. -/

public section
namespace Thompson.Simplicity.Word31Certificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_12288 : checkChunk context facts instructions 12288 3752 = true := by decide +kernel

end Thompson.Simplicity.Word31Certificate
