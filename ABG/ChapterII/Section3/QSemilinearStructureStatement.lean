module
public import ABG.ChapterII.Section3.QProjectiveLinearComplement
public import Theory.SpecificGroups.GL2.Semilinear
public import ABG.ChapterII.Section2.UnitarySemilinear

/-!
# The complete Q-group semilinear structure conclusion

This proposition records the full output of ABG II.3 Proposition 3: the
normal matrix constituent and its odd cyclic complement, an embedding into
the actual linear or unitary semilinear group, the exact determinant-level
image, pure coefficient images, and the complement as the ambient odd core
of a chosen Sylow centralizer. The linear alternative retains the supplied
finite field; the unitary alternative uses its quadratic Galois field.

The statement is shared by the construction over canonical finite fields
and its transport to the original group and field. It asserts no existence
by itself. This boundary keeps their common mathematical conclusion fixed.
Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp24--28.
-/

namespace ABG
open Matrix.GeneralLinearGroup GorensteinWalter
universe u

/-- The complete semilinear structure conclusion of II.3 Proposition 3. -/
@[expose] public def qSemilinearStructureConclusion
    {H : Type u} [Group H] [Finite H] (L0 : Subgroup H)
    (F : Type u) [Field F] [Finite F] : Prop :=
  ∃ L E : Subgroup H,
    L.Normal ∧ L0 ≤ L ∧ L.IsComplement' E ∧ IsCyclic E ∧ Odd (Nat.card E) ∧
    ((∃ (m : ℕ) (φ : H →* GammaL2 F),
      Function.Injective φ ∧ 2 ^ m ∣ Nat.card F - 1 ∧
      L.map φ = (determinantTwoPower F m).map SemidirectProduct.inl ∧
      E.map φ ≤ (SemidirectProduct.inr : (F ≃+* F) →* GammaL2 F).range) ∨
    (∃ (p d : ℕ) (hp : p.Prime) (_hpodd : Odd p) (hd : d ≠ 0),
      letI : Fact p.Prime := ⟨hp⟩
      Nat.card F = p ^ d ∧
      ∃ (m : ℕ) (φ : H →* GammaU2 p d hd),
        Function.Injective φ ∧ 2 ^ m ∣ p ^ d + 1 ∧
        L.map φ = (SU2Level p d hd m).map SemidirectProduct.inl ∧
        E.map φ ≤ (SemidirectProduct.inr :
          (GaloisField p (2 * d) ≃+* GaloisField p (2 * d)) →* GammaU2 p d hd).range)) ∧
    ∃ S : Sylow 2 L,
      let C := Subgroup.centralizer (((S : Subgroup L).map L.subtype) : Set H)
      E = (pPrimeCore 2 C).map C.subtype


end ABG
