module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Checks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Soundness
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.SeedChecks.Pilot

/-!
# Assembly of the initial full-degree cross checks

Four intervals of length 65536 and three shorter terminal intervals cover every
ambient letter. The finite range certificates are independent; `SeedChecks`
remains unproved until every range for both original tests has been supplied.
The first 1024 letters of each test are already certified in `Pilot`.

The final theorem in this module applies the range reduction to the genuine
word5 and word8 permutation interpretations. No intermediate numerical witness
is assumed to be a permutation, and no restriction to the smaller orbit is used.

Source: the literal `FirstFour.Words`, `source/faithfulness/nodes.json`,
ATLAS F24G1-p306936B0 and GLS3 Table 5.3v.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions.Staged
open Certificate

namespace SeedCertificate

/-- The three terminal intervals used by the existing full-domain cover. -/
def Tail (test : Nat → Bool) : Prop :=
  checkPow test 262144 15 = true ∧
  checkPow test 294912 13 = true ∧
  checkPow test 303104 12 = true

/-- Assemble independently checked intervals on the original ambient domain. -/
theorem checks_of_ranges (test : Nat → Bool)
    (h0 : checkPow test 0 16 = true)
    (h1 : checkPow test 65536 16 = true)
    (h2 : checkPow test 131072 16 = true)
    (h3 : checkPow test 196608 16 = true)
    (ht : Tail test) : Checks test :=
  FirstFourModel.covered_checks test
    (checkPow_join test 17 0
      (checkPow_join test 16 0 h0 h1)
      (checkPow_join test 16 131072 h2 h3))
    ht.1 ht.2.1 ht.2.2

end SeedCertificate

/-- Conditional finite assembly; every range remains a genuine proof obligation. -/
theorem seedChecks_of_ranges
    (h50 : checkPow check5 0 16 = true)
    (h51 : checkPow check5 65536 16 = true)
    (h52 : checkPow check5 131072 16 = true)
    (h53 : checkPow check5 196608 16 = true)
    (h5t : SeedCertificate.Tail check5)
    (h80 : checkPow check8 0 16 = true)
    (h81 : checkPow check8 65536 16 = true)
    (h82 : checkPow check8 131072 16 = true)
    (h83 : checkPow check8 196608 16 = true)
    (h8t : SeedCertificate.Tail check8) : SeedChecks :=
  ⟨SeedCertificate.checks_of_ranges check5 h50 h51 h52 h53 h5t,
    SeedCertificate.checks_of_ranges check8 h80 h81 h82 h83 h8t⟩

/-- The actual literal-word consumers of the range certificates. -/
theorem seedWordAgreements_of_ranges
    (h50 : checkPow check5 0 16 = true)
    (h51 : checkPow check5 65536 16 = true)
    (h52 : checkPow check5 131072 16 = true)
    (h53 : checkPow check5 196608 16 = true)
    (h5t : SeedCertificate.Tail check5)
    (h80 : checkPow check8 0 16 = true)
    (h81 : checkPow check8 65536 16 = true)
    (h82 : checkPow check8 131072 16 = true)
    (h83 : checkPow check8 196608 16 = true)
    (h8t : SeedCertificate.Tail check8) :
    Agrees (FirstFourModel.Word.word5 FirstFourModel.aPerm FirstFourModel.bPerm) raw5 ∧
    Agrees (FirstFourModel.Word.word8 FirstFourModel.aPerm FirstFourModel.bPerm) raw8 := by
  have hs := seedChecks_of_ranges h50 h51 h52 h53 h5t h80 h81 h82 h83 h8t
  exact ⟨agrees5 hs.1, agrees8 hs.2⟩

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions.Staged
