module

public import Theory.SpecificGroups.Tits.Atlas1600SylowTwoCertificate
public import Theory.SpecificGroups.Tits.Atlas1600OrderData

/-!
# Center certificate for the Parrott Sylow-two subgroup

Commuting with the eight generators at point 0 leaves only normal-form
indices 0 and 65. The latter word commutes with every generator on all
1600 points. Both finite tests are checked by the kernel.

Source: Parrott (1972), p. 683, and the Atlas permutations transcribed in
`refs/original/n-group-global/`.
-/

namespace Tits.Atlas1600SylowTwoCenterCertificate

open Atlas1600SylowTwoCertificate Atlas1600ParrottData

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

@[expose] public def testCentral (x : Equiv.Perm (Fin 1600)) : Bool :=
  (x (s1Perm 0) == s1Perm (x 0)) &&
  (x (s2Perm 0) == s2Perm (x 0)) &&
  (x (s3Perm 0) == s3Perm (x 0)) &&
  (x (s4Perm 0) == s4Perm (x 0)) &&
  (x (s5Perm 0) == s5Perm (x 0)) &&
  (x (s6Perm 0) == s6Perm (x 0)) &&
  (x (s7Perm 0) == s7Perm (x 0)) &&
  (x (s8Perm 0) == s8Perm (x 0))

public theorem central_candidates (i : Fin 2048) :
    testCentral (normalForm i) = true → i = 0 ∨ i = 65 := by
  revert i
  apply Tits.Atlas1600OrderCertificate.allFin
  decide +kernel

public theorem normalForm_zero : normalForm 0 = 1 := by
  norm_num [normalForm]

public theorem normalForm_sixty_five : normalForm 65 = s1Perm * s5Perm ^ 2 := by
  norm_num [normalForm]

@[expose] public def generator : Fin 8 → Equiv.Perm (Fin 1600)
  | 0 => s1Perm
  | 1 => s2Perm
  | 2 => s3Perm
  | 3 => s4Perm
  | 4 => s5Perm
  | 5 => s6Perm
  | 6 => s7Perm
  | 7 => s8Perm

public theorem central_word_commutes (i : Fin 8) :
    (s1Perm * s5Perm ^ 2) * generator i = generator i * (s1Perm * s5Perm ^ 2) := by
  apply Equiv.ext
  revert i
  apply Tits.Atlas1600OrderCertificate.allFin₂
  decide +kernel

public theorem central_word_ne_one : s1Perm * s5Perm ^ 2 ≠ 1 := by
  have h : (s1Perm * s5Perm ^ 2) (0 : Fin 1600) ≠ 0 := by decide +kernel
  intro heq
  exact h (congrArg (fun g : Equiv.Perm (Fin 1600) => g 0) heq)

end Tits.Atlas1600SylowTwoCenterCertificate
