module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Checks

/-!
# Initial bounded seed certificates

These checks establish the original word5 and word8 cross identities on
`[0, 1024)`. Each leaf uses ordinary kernel reduction on 128 ambient letters;
joining the leaves does not repeat their reductions. These are prefixes only,
not full-degree seed checks. Range certificates reuse them in the first range.

Source: `FirstFour.Words`, `Fi23InFi24Prime/source/faithfulness/nodes.json`,
ATLAS F24G1-p306936B0 and GLS3 Table 5.3v. Measurements and reproduction are
in `SeedChecks/source/README.md`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions.Staged.SeedCertificate
open Certificate

-- A completed leaf releases its reduction cache before the next leaf starts.
set_option Elab.async false

private theorem leaf5_0 : checkPow check5 0 7 = true := by
  decide +kernel

private theorem leaf5_128 : checkPow check5 128 7 = true := by
  decide +kernel

private theorem leaf5_256 : checkPow check5 256 7 = true := by
  decide +kernel

private theorem leaf5_384 : checkPow check5 384 7 = true := by
  decide +kernel

private theorem leaf5_512 : checkPow check5 512 7 = true := by
  decide +kernel

private theorem leaf5_640 : checkPow check5 640 7 = true := by
  decide +kernel

private theorem leaf5_768 : checkPow check5 768 7 = true := by
  decide +kernel

private theorem leaf5_896 : checkPow check5 896 7 = true := by
  decide +kernel

private theorem joined5_0_8 : checkPow check5 0 8 = true :=
  checkPow_join check5 7 0 leaf5_0 leaf5_128

private theorem joined5_256_8 : checkPow check5 256 8 = true :=
  checkPow_join check5 7 256 leaf5_256 leaf5_384

private theorem joined5_0_9 : checkPow check5 0 9 = true :=
  checkPow_join check5 8 0 joined5_0_8 joined5_256_8

private theorem joined5_512_8 : checkPow check5 512 8 = true :=
  checkPow_join check5 7 512 leaf5_512 leaf5_640

private theorem joined5_768_8 : checkPow check5 768 8 = true :=
  checkPow_join check5 7 768 leaf5_768 leaf5_896

private theorem joined5_512_9 : checkPow check5 512 9 = true :=
  checkPow_join check5 8 512 joined5_512_8 joined5_768_8

theorem prefix5 : checkPow check5 0 10 = true :=
  checkPow_join check5 9 0 joined5_0_9 joined5_512_9

private theorem leaf8_0 : checkPow check8 0 7 = true := by
  decide +kernel

private theorem leaf8_128 : checkPow check8 128 7 = true := by
  decide +kernel

private theorem leaf8_256 : checkPow check8 256 7 = true := by
  decide +kernel

private theorem leaf8_384 : checkPow check8 384 7 = true := by
  decide +kernel

private theorem leaf8_512 : checkPow check8 512 7 = true := by
  decide +kernel

private theorem leaf8_640 : checkPow check8 640 7 = true := by
  decide +kernel

private theorem leaf8_768 : checkPow check8 768 7 = true := by
  decide +kernel

private theorem leaf8_896 : checkPow check8 896 7 = true := by
  decide +kernel

private theorem joined8_0_8 : checkPow check8 0 8 = true :=
  checkPow_join check8 7 0 leaf8_0 leaf8_128

private theorem joined8_256_8 : checkPow check8 256 8 = true :=
  checkPow_join check8 7 256 leaf8_256 leaf8_384

private theorem joined8_0_9 : checkPow check8 0 9 = true :=
  checkPow_join check8 8 0 joined8_0_8 joined8_256_8

private theorem joined8_512_8 : checkPow check8 512 8 = true :=
  checkPow_join check8 7 512 leaf8_512 leaf8_640

private theorem joined8_768_8 : checkPow check8 768 8 = true :=
  checkPow_join check8 7 768 leaf8_768 leaf8_896

private theorem joined8_512_9 : checkPow check8 512 9 = true :=
  checkPow_join check8 8 512 joined8_512_8 joined8_768_8

theorem prefix8 : checkPow check8 0 10 = true :=
  checkPow_join check8 9 0 joined8_0_9 joined8_512_9

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions.Staged.SeedCertificate
