module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Base

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

@[expose] public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

def survivorNode0 : Nat → Nat :=
  (lookupBranch 24 (lookupBranch 12 (lookupBranch 6 (lookupBranch 3 (lookupBranch 1 (fun _ => 0) (lookupBranch 2 (fun _ => 1) (fun _ => 2))) (lookupBranch 4 (fun _ => 3) (lookupBranch 5 (fun _ => 4) (fun _ => 5)))) (lookupBranch 9 (lookupBranch 7 (fun _ => 6) (lookupBranch 8 (fun _ => 7) (fun _ => 8))) (lookupBranch 10 (fun _ => 9) (lookupBranch 11 (fun _ => 13) (fun _ => 14))))) (lookupBranch 18 (lookupBranch 15 (lookupBranch 13 (fun _ => 15) (lookupBranch 14 (fun _ => 16) (fun _ => 17))) (lookupBranch 16 (fun _ => 24) (lookupBranch 17 (fun _ => 25) (fun _ => 28)))) (lookupBranch 21 (lookupBranch 19 (fun _ => 29) (lookupBranch 20 (fun _ => 30) (fun _ => 31))) (lookupBranch 22 (fun _ => 32) (lookupBranch 23 (fun _ => 33) (fun _ => 36)))))) (lookupBranch 36 (lookupBranch 30 (lookupBranch 27 (lookupBranch 25 (fun _ => 40) (lookupBranch 26 (fun _ => 41) (fun _ => 42))) (lookupBranch 28 (fun _ => 43) (lookupBranch 29 (fun _ => 44) (fun _ => 45)))) (lookupBranch 33 (lookupBranch 31 (fun _ => 46) (lookupBranch 32 (fun _ => 52) (fun _ => 53))) (lookupBranch 34 (fun _ => 54) (lookupBranch 35 (fun _ => 55) (fun _ => 56))))) (lookupBranch 42 (lookupBranch 39 (lookupBranch 37 (fun _ => 57) (lookupBranch 38 (fun _ => 60) (fun _ => 73))) (lookupBranch 40 (fun _ => 75) (lookupBranch 41 (fun _ => 77) (fun _ => 94)))) (lookupBranch 45 (lookupBranch 43 (fun _ => 108) (lookupBranch 44 (fun _ => 111) (fun _ => 167))) (lookupBranch 46 (fun _ => 191) (lookupBranch 47 (fun _ => 210) (fun _ => 421)))))))

end G2Five.AtlasPresentation.ThirtyCertificate
