module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Level2Step08

/-!
# Exact point-image bound with 2 fixed points

Untrusted finite witnesses for the literal ATLAS generator a and its two-point
centralizer stabilizer chain. Every equation used below is checked by Lean's
kernel. No centralizer order or product structure is assumed.
Source: RuG1-p4060B0, attributed in Model.PermutationData; GLS3 Table 5.3r.
Reproduction data and procedure are in Second/source/.
-/

set_option Elab.async false
namespace Rudvalis.InvolutionCentralizers.SecondCertificate
open OuterNormalizer OuterNormalizer.InvarianceCertificate OuterNormalizer.RigidityCertificate

private def decodeTwoFacts (x : Fin 4060) : Prop :=
  (c2s8 x = c2s8 2 → x = 2) ∧ (c2s8 x = c2s8 3 → x = 3) ∧ (c2s8 x = c2s8 4 → x = 4)

private instance (x : Fin 4060) : Decidable (decodeTwoFacts x) := inferInstanceAs (Decidable ((c2s8 x = c2s8 2 → x = 2) ∧ (c2s8 x = c2s8 3 → x = 3) ∧ (c2s8 x = c2s8 4 → x = 4)))

private theorem decodeTwoFacts_b0 : checkBlock decodeTwoFacts 0 = true := by decide +kernel

private theorem decodeTwoFacts_b1 : checkBlock decodeTwoFacts 1 = true := by decide +kernel

private theorem decodeTwoFacts_b2 : checkBlock decodeTwoFacts 2 = true := by decide +kernel

private theorem decodeTwoFacts_b3 : checkBlock decodeTwoFacts 3 = true := by decide +kernel

private theorem decodeTwoFacts_b4 : checkBlock decodeTwoFacts 4 = true := by decide +kernel

private theorem decodeTwoFacts_b5 : checkBlock decodeTwoFacts 5 = true := by decide +kernel

private theorem decodeTwoFacts_b6 : checkBlock decodeTwoFacts 6 = true := by decide +kernel

private theorem decodeTwoFacts_b7 : checkBlock decodeTwoFacts 7 = true := by decide +kernel

private theorem decodeTwoFacts_b8 : checkBlock decodeTwoFacts 8 = true := by decide +kernel

private theorem decodeTwoFacts_b9 : checkBlock decodeTwoFacts 9 = true := by decide +kernel

private theorem decodeTwoFacts_b10 : checkBlock decodeTwoFacts 10 = true := by decide +kernel

private theorem decodeTwoFacts_b11 : checkBlock decodeTwoFacts 11 = true := by decide +kernel

private theorem decodeTwoFacts_b12 : checkBlock decodeTwoFacts 12 = true := by decide +kernel

private theorem decodeTwoFacts_b13 : checkBlock decodeTwoFacts 13 = true := by decide +kernel

private theorem decodeTwoFacts_b14 : checkBlock decodeTwoFacts 14 = true := by decide +kernel

private theorem decodeTwoFacts_b15 : checkBlock decodeTwoFacts 15 = true := by decide +kernel

private theorem decodeTwoFacts_b16 : checkBlock decodeTwoFacts 16 = true := by decide +kernel

private theorem decodeTwoFacts_b17 : checkBlock decodeTwoFacts 17 = true := by decide +kernel

private theorem decodeTwoFacts_b18 : checkBlock decodeTwoFacts 18 = true := by decide +kernel

private theorem decodeTwoFacts_b19 : checkBlock decodeTwoFacts 19 = true := by decide +kernel

private theorem decodeTwoFacts_b20 : checkBlock decodeTwoFacts 20 = true := by decide +kernel

private theorem decodeTwoFacts_b21 : checkBlock decodeTwoFacts 21 = true := by decide +kernel

private theorem decodeTwoFacts_b22 : checkBlock decodeTwoFacts 22 = true := by decide +kernel

private theorem decodeTwoFacts_b23 : checkBlock decodeTwoFacts 23 = true := by decide +kernel

private theorem decodeTwoFacts_b24 : checkBlock decodeTwoFacts 24 = true := by decide +kernel

private theorem decodeTwoFacts_b25 : checkBlock decodeTwoFacts 25 = true := by decide +kernel

private theorem decodeTwoFacts_b26 : checkBlock decodeTwoFacts 26 = true := by decide +kernel

private theorem decodeTwoFacts_b27 : checkBlock decodeTwoFacts 27 = true := by decide +kernel

private theorem decodeTwoFacts_b28 : checkBlock decodeTwoFacts 28 = true := by decide +kernel

private theorem decodeTwoFacts_b29 : checkBlock decodeTwoFacts 29 = true := by decide +kernel

private theorem decodeTwoFacts_b30 : checkBlock decodeTwoFacts 30 = true := by decide +kernel

private theorem decodeTwoFacts_b31 : checkBlock decodeTwoFacts 31 = true := by decide +kernel

private theorem decodeTwoFacts_b32 : checkBlock decodeTwoFacts 32 = true := by decide +kernel

private theorem decodeTwoFacts_b33 : checkBlock decodeTwoFacts 33 = true := by decide +kernel

private theorem decodeTwoFacts_b34 : checkBlock decodeTwoFacts 34 = true := by decide +kernel

private theorem decodeTwoFacts_b35 : checkBlock decodeTwoFacts 35 = true := by decide +kernel

private theorem decodeTwoFacts_b36 : checkBlock decodeTwoFacts 36 = true := by decide +kernel

private theorem decodeTwoFacts_b37 : checkBlock decodeTwoFacts 37 = true := by decide +kernel

private theorem decodeTwoFacts_b38 : checkBlock decodeTwoFacts 38 = true := by decide +kernel

private theorem decodeTwoFacts_b39 : checkBlock decodeTwoFacts 39 = true := by decide +kernel

private theorem decodeTwoFacts_b40 : checkBlock decodeTwoFacts 40 = true := by decide +kernel

private theorem decodeTwoFacts_b41 : checkBlock decodeTwoFacts 41 = true := by decide +kernel

private theorem decodeTwoFacts_b42 : checkBlock decodeTwoFacts 42 = true := by decide +kernel

private theorem decodeTwoFacts_b43 : checkBlock decodeTwoFacts 43 = true := by decide +kernel

private theorem decodeTwoFacts_b44 : checkBlock decodeTwoFacts 44 = true := by decide +kernel

private theorem decodeTwoFacts_b45 : checkBlock decodeTwoFacts 45 = true := by decide +kernel

private theorem decodeTwoFacts_b46 : checkBlock decodeTwoFacts 46 = true := by decide +kernel

private theorem decodeTwoFacts_b47 : checkBlock decodeTwoFacts 47 = true := by decide +kernel

private theorem decodeTwoFacts_b48 : checkBlock decodeTwoFacts 48 = true := by decide +kernel

private theorem decodeTwoFacts_b49 : checkBlock decodeTwoFacts 49 = true := by decide +kernel

private theorem decodeTwoFacts_b50 : checkBlock decodeTwoFacts 50 = true := by decide +kernel

private theorem decodeTwoFacts_b51 : checkBlock decodeTwoFacts 51 = true := by decide +kernel

private theorem decodeTwoFacts_b52 : checkBlock decodeTwoFacts 52 = true := by decide +kernel

private theorem decodeTwoFacts_b53 : checkBlock decodeTwoFacts 53 = true := by decide +kernel

private theorem decodeTwoFacts_b54 : checkBlock decodeTwoFacts 54 = true := by decide +kernel

private theorem decodeTwoFacts_b55 : checkBlock decodeTwoFacts 55 = true := by decide +kernel

private theorem decodeTwoFacts_b56 : checkBlock decodeTwoFacts 56 = true := by decide +kernel

private theorem decodeTwoFacts_b57 : checkBlock decodeTwoFacts 57 = true := by decide +kernel

private theorem decodeTwoFacts_b58 : checkBlock decodeTwoFacts 58 = true := by decide +kernel

private theorem decodeTwoFacts_b59 : checkBlock decodeTwoFacts 59 = true := by decide +kernel

private theorem decodeTwoFacts_b60 : checkBlock decodeTwoFacts 60 = true := by decide +kernel

private theorem decodeTwoFacts_b61 : checkBlock decodeTwoFacts 61 = true := by decide +kernel

private theorem decodeTwoFacts_b62 : checkBlock decodeTwoFacts 62 = true := by decide +kernel

private theorem decodeTwoFacts_b63 : checkBlock decodeTwoFacts 63 = true := by decide +kernel

private theorem decodeTwoFacts_all : ∀ x, decodeTwoFacts x := by
  apply allFinBlocks
  intro b
  fin_cases b
  · exact decodeTwoFacts_b0
  · exact decodeTwoFacts_b1
  · exact decodeTwoFacts_b2
  · exact decodeTwoFacts_b3
  · exact decodeTwoFacts_b4
  · exact decodeTwoFacts_b5
  · exact decodeTwoFacts_b6
  · exact decodeTwoFacts_b7
  · exact decodeTwoFacts_b8
  · exact decodeTwoFacts_b9
  · exact decodeTwoFacts_b10
  · exact decodeTwoFacts_b11
  · exact decodeTwoFacts_b12
  · exact decodeTwoFacts_b13
  · exact decodeTwoFacts_b14
  · exact decodeTwoFacts_b15
  · exact decodeTwoFacts_b16
  · exact decodeTwoFacts_b17
  · exact decodeTwoFacts_b18
  · exact decodeTwoFacts_b19
  · exact decodeTwoFacts_b20
  · exact decodeTwoFacts_b21
  · exact decodeTwoFacts_b22
  · exact decodeTwoFacts_b23
  · exact decodeTwoFacts_b24
  · exact decodeTwoFacts_b25
  · exact decodeTwoFacts_b26
  · exact decodeTwoFacts_b27
  · exact decodeTwoFacts_b28
  · exact decodeTwoFacts_b29
  · exact decodeTwoFacts_b30
  · exact decodeTwoFacts_b31
  · exact decodeTwoFacts_b32
  · exact decodeTwoFacts_b33
  · exact decodeTwoFacts_b34
  · exact decodeTwoFacts_b35
  · exact decodeTwoFacts_b36
  · exact decodeTwoFacts_b37
  · exact decodeTwoFacts_b38
  · exact decodeTwoFacts_b39
  · exact decodeTwoFacts_b40
  · exact decodeTwoFacts_b41
  · exact decodeTwoFacts_b42
  · exact decodeTwoFacts_b43
  · exact decodeTwoFacts_b44
  · exact decodeTwoFacts_b45
  · exact decodeTwoFacts_b46
  · exact decodeTwoFacts_b47
  · exact decodeTwoFacts_b48
  · exact decodeTwoFacts_b49
  · exact decodeTwoFacts_b50
  · exact decodeTwoFacts_b51
  · exact decodeTwoFacts_b52
  · exact decodeTwoFacts_b53
  · exact decodeTwoFacts_b54
  · exact decodeTwoFacts_b55
  · exact decodeTwoFacts_b56
  · exact decodeTwoFacts_b57
  · exact decodeTwoFacts_b58
  · exact decodeTwoFacts_b59
  · exact decodeTwoFacts_b60
  · exact decodeTwoFacts_b61
  · exact decodeTwoFacts_b62
  · exact decodeTwoFacts_b63

public theorem fix_two_eq_one (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut) (ha : ∀ x, p (aPerm x) = aPerm (p x))
    (hf : ∀ x : Fin 4060, x.val < 2 → p x = x) : p = 1 := by
  apply fix_five_eq_one p hp
  intro x hx
  by_cases h2 : x.val < 2
  · exact hf x h2
  have he : x = 2 ∨ x = 3 ∨ x = 4 := by
    have he : x.val = 2 ∨ x.val = 3 ∨ x.val = 4 := by omega
    rcases he with he | he | he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Or.inl (Fin.ext he))
    · exact Or.inr (Or.inr (Fin.ext he))
  rcases he with rfl | rfl | rfl
  · exact (decodeTwoFacts_all (p 2)).1 (c2s8_preserved p hp ha hf 2)
  · exact (decodeTwoFacts_all (p 3)).2.1 (c2s8_preserved p hp ha hf 3)
  · exact (decodeTwoFacts_all (p 4)).2.2 (c2s8_preserved p hp ha hf 4)

end Rudvalis.InvolutionCentralizers.SecondCertificate
