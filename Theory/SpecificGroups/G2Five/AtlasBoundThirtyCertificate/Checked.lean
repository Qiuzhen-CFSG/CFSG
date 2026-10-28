module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Check00
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Check01
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Check02
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Check03
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Check04
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Check05
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Check06
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Check07

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

/-- All 8000 deductions follow from the actual model of the certificate. -/
theorem all_hold {G : Type*} [Group G] {H : Subgroup G}
    {g : (Fin 3) → G} {ρ : Nat → G}
    (valid : Valid context H g ρ) :
    ∀ n, n < 8000 → Holds H g ρ (facts n) := by
  have hall_0 := checkChunk_sound valid facts instructions 0 1024
    (fun n h => (Nat.not_lt_zero n h).elim) checked_0
  have hall_1024 := checkChunk_sound valid facts instructions 1024 1024
    hall_0 checked_1024
  have hall_2048 := checkChunk_sound valid facts instructions 2048 1024
    hall_1024 checked_2048
  have hall_3072 := checkChunk_sound valid facts instructions 3072 1024
    hall_2048 checked_3072
  have hall_4096 := checkChunk_sound valid facts instructions 4096 1024
    hall_3072 checked_4096
  have hall_5120 := checkChunk_sound valid facts instructions 5120 1024
    hall_4096 checked_5120
  have hall_6144 := checkChunk_sound valid facts instructions 6144 1024
    hall_5120 checked_6144
  have hall_7168 := checkChunk_sound valid facts instructions 7168 832
    hall_6144 checked_7168
  exact hall_7168

end G2Five.AtlasPresentation.ThirtyCertificate
