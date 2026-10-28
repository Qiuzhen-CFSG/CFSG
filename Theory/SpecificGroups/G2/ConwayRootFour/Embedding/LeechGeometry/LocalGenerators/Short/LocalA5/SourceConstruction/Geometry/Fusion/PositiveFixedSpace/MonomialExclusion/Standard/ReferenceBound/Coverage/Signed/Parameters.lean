module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage.Contracts

/-!
# Binary parameters and parity-independent square equations

The six hexacode bits and five even-sign bits are decoded by the inverse of
`finFunctionFinEquiv`, so the decoding covers every original parameter. On a
column fixed by the pullback, the tetrad constants cancel in the sign-square
equation. This gives a small necessary test before checking the parity bits.
The mask addition lemma connects binary addition with integer xor.

Source context: the reference calculation for Aschbacher, *Sporadic Groups*
(1994), Lemma 49.5, pp.283–284, and the conventions on p.269. The underlying
hexacode and Golay encoders are the existing attributed ATLAS definitions.
-/

open Atlas.Codes
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage.Signed

/-- Little-endian binary parameters, with the inverse supplied by a finite equivalence. -/
def decodeBits (n : Nat) : Fin (2^n) → (Fin n → Bit) := finFunctionFinEquiv.symm

def decodeHex (n : Fin 64) : HexParameters :=
  ⟨![decodeBits 6 n 0, decodeBits 6 n 1, decodeBits 6 n 2],
    ![decodeBits 6 n 3, decodeBits 6 n 4], decodeBits 6 n 5⟩
def decodeParity : Fin 32 → (Fin 5 → Bit) := decodeBits 5

theorem decodeHex_surjective : Function.Surjective decodeHex := by
  rintro ⟨a,b,c⟩
  obtain ⟨n,hn⟩ := (@finFunctionFinEquiv 2 6).symm.surjective
    (![a 0,a 1,a 2,b 0,b 1,c] : Fin 6 → Fin 2)
  refine ⟨n, ?_⟩
  change decodeBits 6 n = _ at hn
  simp only [decodeHex, hn]
  apply Prod.ext
  · funext i; fin_cases i <;> rfl
  · apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl

theorem decodeParity_surjective : Function.Surjective decodeParity :=
  (@finFunctionFinEquiv 2 5).symm.surjective


/-- Necessary square equations independent of the five tetrad-sign parameters. -/
def TranslationChecks (pi : HexIndex → HexIndex) (u : HexParameters) : Prop :=
  (∀ i : HexIndex, markedPull pi (hexEncoder u)
    (markedPull pi (hexEncoder u) (i,0)) = (i,0)) ∧
  (∀ i : HexIndex, pi i = i →
    signWord pi (hexEncoder u) (i,0) +
      signWord pi (hexEncoder u) (markedPull pi (hexEncoder u) (i,0)) = 0)

instance (pi u) : Decidable (TranslationChecks pi u) := by
  unfold TranslationChecks
  infer_instance

/-- On a fixed column the two equal tetrad constants cancel from the sign square. -/
theorem translationChecks_of_square (pi : HexIndex → HexIndex)
    (u : HexParameters) (r : Fin 5 → Bit)
    (hp : Function.Involutive (markedPull pi (hexEncoder u)))
    (hs : ∀ i, signedWord pi u r i +
      signedWord pi u r (markedPull pi (hexEncoder u) i) = 0) :
    TranslationChecks pi u := by
  refine ⟨fun i => hp (i,0), ?_⟩
  intro i hi
  have h := hs (i,0)
  change signWord pi (hexEncoder u) (i,0) + rho (parityEncoder 5 r) (i,0) +
    (signWord pi (hexEncoder u) (markedPull pi (hexEncoder u) (i,0)) +
      rho (parityEncoder 5 r) (markedPull pi (hexEncoder u) (i,0))) = 0 at h
  have hr : rho (parityEncoder 5 r) (markedPull pi (hexEncoder u) (i,0)) =
      rho (parityEncoder 5 r) (i,0) := by
    change parityEncoder 5 r (hexIndexEquiv (pi i)) = _
    rw [hi]
    rfl
  rw [hr] at h
  have cancel : ∀ x y z : Bit, x + z + (y + z) = x + y := by decide
  simpa only [cancel] using h

theorem maskBit_xor (m n : Nat) (i : Fin 24) :
    maskBit (m ^^^ n) i = maskBit m i + maskBit n i := by
  simp only [maskBit, Nat.testBit_xor]
  cases m.testBit i.val <;> cases n.testBit i.val <;> decide

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage.Signed
