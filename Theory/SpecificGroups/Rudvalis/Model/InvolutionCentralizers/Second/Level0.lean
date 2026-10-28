module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Basic
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Orbit0

/-!
# Exact point-image bound with 0 fixed points

Untrusted finite witnesses for the literal ATLAS generator a and its two-point
centralizer stabilizer chain. Every equation used below is checked by Lean's
kernel. No centralizer order or product structure is assumed.
Source: RuG1-p4060B0, attributed in Model.PermutationData; GLS3 Table 5.3r.
Reproduction data and procedure are in Second/source/.
-/

set_option Elab.async false
namespace Rudvalis.InvolutionCentralizers.SecondCertificate
open OuterNormalizer OuterNormalizer.InvarianceCertificate OuterNormalizer.RigidityCertificate

private def decode0Facts (x : Fin 4060) : Prop :=
  (seed 0) x = (seed 0) 0 → point0 (pointInv0 x) = x

private instance (x : Fin 4060) : Decidable (decode0Facts x) := inferInstanceAs (Decidable ((seed 0) x = (seed 0) 0 → point0 (pointInv0 x) = x))

private theorem decode0Facts_b0 : checkBlock decode0Facts 0 = true := by decide +kernel

private theorem decode0Facts_b1 : checkBlock decode0Facts 1 = true := by decide +kernel

private theorem decode0Facts_b2 : checkBlock decode0Facts 2 = true := by decide +kernel

private theorem decode0Facts_b3 : checkBlock decode0Facts 3 = true := by decide +kernel

private theorem decode0Facts_b4 : checkBlock decode0Facts 4 = true := by decide +kernel

private theorem decode0Facts_b5 : checkBlock decode0Facts 5 = true := by decide +kernel

private theorem decode0Facts_b6 : checkBlock decode0Facts 6 = true := by decide +kernel

private theorem decode0Facts_b7 : checkBlock decode0Facts 7 = true := by decide +kernel

private theorem decode0Facts_b8 : checkBlock decode0Facts 8 = true := by decide +kernel

private theorem decode0Facts_b9 : checkBlock decode0Facts 9 = true := by decide +kernel

private theorem decode0Facts_b10 : checkBlock decode0Facts 10 = true := by decide +kernel

private theorem decode0Facts_b11 : checkBlock decode0Facts 11 = true := by decide +kernel

private theorem decode0Facts_b12 : checkBlock decode0Facts 12 = true := by decide +kernel

private theorem decode0Facts_b13 : checkBlock decode0Facts 13 = true := by decide +kernel

private theorem decode0Facts_b14 : checkBlock decode0Facts 14 = true := by decide +kernel

private theorem decode0Facts_b15 : checkBlock decode0Facts 15 = true := by decide +kernel

private theorem decode0Facts_b16 : checkBlock decode0Facts 16 = true := by decide +kernel

private theorem decode0Facts_b17 : checkBlock decode0Facts 17 = true := by decide +kernel

private theorem decode0Facts_b18 : checkBlock decode0Facts 18 = true := by decide +kernel

private theorem decode0Facts_b19 : checkBlock decode0Facts 19 = true := by decide +kernel

private theorem decode0Facts_b20 : checkBlock decode0Facts 20 = true := by decide +kernel

private theorem decode0Facts_b21 : checkBlock decode0Facts 21 = true := by decide +kernel

private theorem decode0Facts_b22 : checkBlock decode0Facts 22 = true := by decide +kernel

private theorem decode0Facts_b23 : checkBlock decode0Facts 23 = true := by decide +kernel

private theorem decode0Facts_b24 : checkBlock decode0Facts 24 = true := by decide +kernel

private theorem decode0Facts_b25 : checkBlock decode0Facts 25 = true := by decide +kernel

private theorem decode0Facts_b26 : checkBlock decode0Facts 26 = true := by decide +kernel

private theorem decode0Facts_b27 : checkBlock decode0Facts 27 = true := by decide +kernel

private theorem decode0Facts_b28 : checkBlock decode0Facts 28 = true := by decide +kernel

private theorem decode0Facts_b29 : checkBlock decode0Facts 29 = true := by decide +kernel

private theorem decode0Facts_b30 : checkBlock decode0Facts 30 = true := by decide +kernel

private theorem decode0Facts_b31 : checkBlock decode0Facts 31 = true := by decide +kernel

private theorem decode0Facts_b32 : checkBlock decode0Facts 32 = true := by decide +kernel

private theorem decode0Facts_b33 : checkBlock decode0Facts 33 = true := by decide +kernel

private theorem decode0Facts_b34 : checkBlock decode0Facts 34 = true := by decide +kernel

private theorem decode0Facts_b35 : checkBlock decode0Facts 35 = true := by decide +kernel

private theorem decode0Facts_b36 : checkBlock decode0Facts 36 = true := by decide +kernel

private theorem decode0Facts_b37 : checkBlock decode0Facts 37 = true := by decide +kernel

private theorem decode0Facts_b38 : checkBlock decode0Facts 38 = true := by decide +kernel

private theorem decode0Facts_b39 : checkBlock decode0Facts 39 = true := by decide +kernel

private theorem decode0Facts_b40 : checkBlock decode0Facts 40 = true := by decide +kernel

private theorem decode0Facts_b41 : checkBlock decode0Facts 41 = true := by decide +kernel

private theorem decode0Facts_b42 : checkBlock decode0Facts 42 = true := by decide +kernel

private theorem decode0Facts_b43 : checkBlock decode0Facts 43 = true := by decide +kernel

private theorem decode0Facts_b44 : checkBlock decode0Facts 44 = true := by decide +kernel

private theorem decode0Facts_b45 : checkBlock decode0Facts 45 = true := by decide +kernel

private theorem decode0Facts_b46 : checkBlock decode0Facts 46 = true := by decide +kernel

private theorem decode0Facts_b47 : checkBlock decode0Facts 47 = true := by decide +kernel

private theorem decode0Facts_b48 : checkBlock decode0Facts 48 = true := by decide +kernel

private theorem decode0Facts_b49 : checkBlock decode0Facts 49 = true := by decide +kernel

private theorem decode0Facts_b50 : checkBlock decode0Facts 50 = true := by decide +kernel

private theorem decode0Facts_b51 : checkBlock decode0Facts 51 = true := by decide +kernel

private theorem decode0Facts_b52 : checkBlock decode0Facts 52 = true := by decide +kernel

private theorem decode0Facts_b53 : checkBlock decode0Facts 53 = true := by decide +kernel

private theorem decode0Facts_b54 : checkBlock decode0Facts 54 = true := by decide +kernel

private theorem decode0Facts_b55 : checkBlock decode0Facts 55 = true := by decide +kernel

private theorem decode0Facts_b56 : checkBlock decode0Facts 56 = true := by decide +kernel

private theorem decode0Facts_b57 : checkBlock decode0Facts 57 = true := by decide +kernel

private theorem decode0Facts_b58 : checkBlock decode0Facts 58 = true := by decide +kernel

private theorem decode0Facts_b59 : checkBlock decode0Facts 59 = true := by decide +kernel

private theorem decode0Facts_b60 : checkBlock decode0Facts 60 = true := by decide +kernel

private theorem decode0Facts_b61 : checkBlock decode0Facts 61 = true := by decide +kernel

private theorem decode0Facts_b62 : checkBlock decode0Facts 62 = true := by decide +kernel

private theorem decode0Facts_b63 : checkBlock decode0Facts 63 = true := by decide +kernel

private theorem decode0Facts_all : ∀ x, decode0Facts x := by
  apply allFinBlocks
  intro b
  fin_cases b
  · exact decode0Facts_b0
  · exact decode0Facts_b1
  · exact decode0Facts_b2
  · exact decode0Facts_b3
  · exact decode0Facts_b4
  · exact decode0Facts_b5
  · exact decode0Facts_b6
  · exact decode0Facts_b7
  · exact decode0Facts_b8
  · exact decode0Facts_b9
  · exact decode0Facts_b10
  · exact decode0Facts_b11
  · exact decode0Facts_b12
  · exact decode0Facts_b13
  · exact decode0Facts_b14
  · exact decode0Facts_b15
  · exact decode0Facts_b16
  · exact decode0Facts_b17
  · exact decode0Facts_b18
  · exact decode0Facts_b19
  · exact decode0Facts_b20
  · exact decode0Facts_b21
  · exact decode0Facts_b22
  · exact decode0Facts_b23
  · exact decode0Facts_b24
  · exact decode0Facts_b25
  · exact decode0Facts_b26
  · exact decode0Facts_b27
  · exact decode0Facts_b28
  · exact decode0Facts_b29
  · exact decode0Facts_b30
  · exact decode0Facts_b31
  · exact decode0Facts_b32
  · exact decode0Facts_b33
  · exact decode0Facts_b34
  · exact decode0Facts_b35
  · exact decode0Facts_b36
  · exact decode0Facts_b37
  · exact decode0Facts_b38
  · exact decode0Facts_b39
  · exact decode0Facts_b40
  · exact decode0Facts_b41
  · exact decode0Facts_b42
  · exact decode0Facts_b43
  · exact decode0Facts_b44
  · exact decode0Facts_b45
  · exact decode0Facts_b46
  · exact decode0Facts_b47
  · exact decode0Facts_b48
  · exact decode0Facts_b49
  · exact decode0Facts_b50
  · exact decode0Facts_b51
  · exact decode0Facts_b52
  · exact decode0Facts_b53
  · exact decode0Facts_b54
  · exact decode0Facts_b55
  · exact decode0Facts_b56
  · exact decode0Facts_b57
  · exact decode0Facts_b58
  · exact decode0Facts_b59
  · exact decode0Facts_b60
  · exact decode0Facts_b61
  · exact decode0Facts_b62
  · exact decode0Facts_b63

public theorem image0_mem_range (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut) (ha : ∀ x, p (aPerm x) = aPerm (p x))
    (hf : ∀ x : Fin 4060, x.val < 0 → p x = x) :
    p 0 ∈ Set.range point0 :=
  ⟨pointInv0 (p 0),decode0Facts_all (p 0)
    (seed_preserved 0 p hp ha hf 0)⟩

end Rudvalis.InvolutionCentralizers.SecondCertificate
