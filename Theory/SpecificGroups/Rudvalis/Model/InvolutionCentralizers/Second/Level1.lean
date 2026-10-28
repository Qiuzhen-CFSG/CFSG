module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Level1Step06
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Orbit1

/-!
# Exact point-image bound with 1 fixed points

Untrusted finite witnesses for the literal ATLAS generator a and its two-point
centralizer stabilizer chain. Every equation used below is checked by Lean's
kernel. No centralizer order or product structure is assumed.
Source: RuG1-p4060B0, attributed in Model.PermutationData; GLS3 Table 5.3r.
Reproduction data and procedure are in Second/source/.
-/

set_option Elab.async false
namespace Rudvalis.InvolutionCentralizers.SecondCertificate
open OuterNormalizer OuterNormalizer.InvarianceCertificate OuterNormalizer.RigidityCertificate

private def decode1Facts (x : Fin 4060) : Prop :=
  c1s6 x = c1s6 1 → point1 (pointInv1 x) = x

private instance (x : Fin 4060) : Decidable (decode1Facts x) := inferInstanceAs (Decidable (c1s6 x = c1s6 1 → point1 (pointInv1 x) = x))

private theorem decode1Facts_b0 : checkBlock decode1Facts 0 = true := by decide +kernel

private theorem decode1Facts_b1 : checkBlock decode1Facts 1 = true := by decide +kernel

private theorem decode1Facts_b2 : checkBlock decode1Facts 2 = true := by decide +kernel

private theorem decode1Facts_b3 : checkBlock decode1Facts 3 = true := by decide +kernel

private theorem decode1Facts_b4 : checkBlock decode1Facts 4 = true := by decide +kernel

private theorem decode1Facts_b5 : checkBlock decode1Facts 5 = true := by decide +kernel

private theorem decode1Facts_b6 : checkBlock decode1Facts 6 = true := by decide +kernel

private theorem decode1Facts_b7 : checkBlock decode1Facts 7 = true := by decide +kernel

private theorem decode1Facts_b8 : checkBlock decode1Facts 8 = true := by decide +kernel

private theorem decode1Facts_b9 : checkBlock decode1Facts 9 = true := by decide +kernel

private theorem decode1Facts_b10 : checkBlock decode1Facts 10 = true := by decide +kernel

private theorem decode1Facts_b11 : checkBlock decode1Facts 11 = true := by decide +kernel

private theorem decode1Facts_b12 : checkBlock decode1Facts 12 = true := by decide +kernel

private theorem decode1Facts_b13 : checkBlock decode1Facts 13 = true := by decide +kernel

private theorem decode1Facts_b14 : checkBlock decode1Facts 14 = true := by decide +kernel

private theorem decode1Facts_b15 : checkBlock decode1Facts 15 = true := by decide +kernel

private theorem decode1Facts_b16 : checkBlock decode1Facts 16 = true := by decide +kernel

private theorem decode1Facts_b17 : checkBlock decode1Facts 17 = true := by decide +kernel

private theorem decode1Facts_b18 : checkBlock decode1Facts 18 = true := by decide +kernel

private theorem decode1Facts_b19 : checkBlock decode1Facts 19 = true := by decide +kernel

private theorem decode1Facts_b20 : checkBlock decode1Facts 20 = true := by decide +kernel

private theorem decode1Facts_b21 : checkBlock decode1Facts 21 = true := by decide +kernel

private theorem decode1Facts_b22 : checkBlock decode1Facts 22 = true := by decide +kernel

private theorem decode1Facts_b23 : checkBlock decode1Facts 23 = true := by decide +kernel

private theorem decode1Facts_b24 : checkBlock decode1Facts 24 = true := by decide +kernel

private theorem decode1Facts_b25 : checkBlock decode1Facts 25 = true := by decide +kernel

private theorem decode1Facts_b26 : checkBlock decode1Facts 26 = true := by decide +kernel

private theorem decode1Facts_b27 : checkBlock decode1Facts 27 = true := by decide +kernel

private theorem decode1Facts_b28 : checkBlock decode1Facts 28 = true := by decide +kernel

private theorem decode1Facts_b29 : checkBlock decode1Facts 29 = true := by decide +kernel

private theorem decode1Facts_b30 : checkBlock decode1Facts 30 = true := by decide +kernel

private theorem decode1Facts_b31 : checkBlock decode1Facts 31 = true := by decide +kernel

private theorem decode1Facts_b32 : checkBlock decode1Facts 32 = true := by decide +kernel

private theorem decode1Facts_b33 : checkBlock decode1Facts 33 = true := by decide +kernel

private theorem decode1Facts_b34 : checkBlock decode1Facts 34 = true := by decide +kernel

private theorem decode1Facts_b35 : checkBlock decode1Facts 35 = true := by decide +kernel

private theorem decode1Facts_b36 : checkBlock decode1Facts 36 = true := by decide +kernel

private theorem decode1Facts_b37 : checkBlock decode1Facts 37 = true := by decide +kernel

private theorem decode1Facts_b38 : checkBlock decode1Facts 38 = true := by decide +kernel

private theorem decode1Facts_b39 : checkBlock decode1Facts 39 = true := by decide +kernel

private theorem decode1Facts_b40 : checkBlock decode1Facts 40 = true := by decide +kernel

private theorem decode1Facts_b41 : checkBlock decode1Facts 41 = true := by decide +kernel

private theorem decode1Facts_b42 : checkBlock decode1Facts 42 = true := by decide +kernel

private theorem decode1Facts_b43 : checkBlock decode1Facts 43 = true := by decide +kernel

private theorem decode1Facts_b44 : checkBlock decode1Facts 44 = true := by decide +kernel

private theorem decode1Facts_b45 : checkBlock decode1Facts 45 = true := by decide +kernel

private theorem decode1Facts_b46 : checkBlock decode1Facts 46 = true := by decide +kernel

private theorem decode1Facts_b47 : checkBlock decode1Facts 47 = true := by decide +kernel

private theorem decode1Facts_b48 : checkBlock decode1Facts 48 = true := by decide +kernel

private theorem decode1Facts_b49 : checkBlock decode1Facts 49 = true := by decide +kernel

private theorem decode1Facts_b50 : checkBlock decode1Facts 50 = true := by decide +kernel

private theorem decode1Facts_b51 : checkBlock decode1Facts 51 = true := by decide +kernel

private theorem decode1Facts_b52 : checkBlock decode1Facts 52 = true := by decide +kernel

private theorem decode1Facts_b53 : checkBlock decode1Facts 53 = true := by decide +kernel

private theorem decode1Facts_b54 : checkBlock decode1Facts 54 = true := by decide +kernel

private theorem decode1Facts_b55 : checkBlock decode1Facts 55 = true := by decide +kernel

private theorem decode1Facts_b56 : checkBlock decode1Facts 56 = true := by decide +kernel

private theorem decode1Facts_b57 : checkBlock decode1Facts 57 = true := by decide +kernel

private theorem decode1Facts_b58 : checkBlock decode1Facts 58 = true := by decide +kernel

private theorem decode1Facts_b59 : checkBlock decode1Facts 59 = true := by decide +kernel

private theorem decode1Facts_b60 : checkBlock decode1Facts 60 = true := by decide +kernel

private theorem decode1Facts_b61 : checkBlock decode1Facts 61 = true := by decide +kernel

private theorem decode1Facts_b62 : checkBlock decode1Facts 62 = true := by decide +kernel

private theorem decode1Facts_b63 : checkBlock decode1Facts 63 = true := by decide +kernel

private theorem decode1Facts_all : ∀ x, decode1Facts x := by
  apply allFinBlocks
  intro b
  fin_cases b
  · exact decode1Facts_b0
  · exact decode1Facts_b1
  · exact decode1Facts_b2
  · exact decode1Facts_b3
  · exact decode1Facts_b4
  · exact decode1Facts_b5
  · exact decode1Facts_b6
  · exact decode1Facts_b7
  · exact decode1Facts_b8
  · exact decode1Facts_b9
  · exact decode1Facts_b10
  · exact decode1Facts_b11
  · exact decode1Facts_b12
  · exact decode1Facts_b13
  · exact decode1Facts_b14
  · exact decode1Facts_b15
  · exact decode1Facts_b16
  · exact decode1Facts_b17
  · exact decode1Facts_b18
  · exact decode1Facts_b19
  · exact decode1Facts_b20
  · exact decode1Facts_b21
  · exact decode1Facts_b22
  · exact decode1Facts_b23
  · exact decode1Facts_b24
  · exact decode1Facts_b25
  · exact decode1Facts_b26
  · exact decode1Facts_b27
  · exact decode1Facts_b28
  · exact decode1Facts_b29
  · exact decode1Facts_b30
  · exact decode1Facts_b31
  · exact decode1Facts_b32
  · exact decode1Facts_b33
  · exact decode1Facts_b34
  · exact decode1Facts_b35
  · exact decode1Facts_b36
  · exact decode1Facts_b37
  · exact decode1Facts_b38
  · exact decode1Facts_b39
  · exact decode1Facts_b40
  · exact decode1Facts_b41
  · exact decode1Facts_b42
  · exact decode1Facts_b43
  · exact decode1Facts_b44
  · exact decode1Facts_b45
  · exact decode1Facts_b46
  · exact decode1Facts_b47
  · exact decode1Facts_b48
  · exact decode1Facts_b49
  · exact decode1Facts_b50
  · exact decode1Facts_b51
  · exact decode1Facts_b52
  · exact decode1Facts_b53
  · exact decode1Facts_b54
  · exact decode1Facts_b55
  · exact decode1Facts_b56
  · exact decode1Facts_b57
  · exact decode1Facts_b58
  · exact decode1Facts_b59
  · exact decode1Facts_b60
  · exact decode1Facts_b61
  · exact decode1Facts_b62
  · exact decode1Facts_b63

public theorem image1_mem_range (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut) (ha : ∀ x, p (aPerm x) = aPerm (p x))
    (hf : ∀ x : Fin 4060, x.val < 1 → p x = x) :
    p 1 ∈ Set.range point1 :=
  ⟨pointInv1 (p 1),decode1Facts_all (p 1)
    (c1s6_preserved p hp ha hf 1)⟩

end Rudvalis.InvolutionCentralizers.SecondCertificate
