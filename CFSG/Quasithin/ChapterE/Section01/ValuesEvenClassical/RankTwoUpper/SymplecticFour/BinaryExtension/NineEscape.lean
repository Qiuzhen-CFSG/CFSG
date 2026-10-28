module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.Noninvolutory
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies

/-!
# The field-of-nine escape assembly

All local calculations already hold at the smallest odd square. Linear
actors use their actual PSL₂/PGL₂ placement. In the field branch, a pure
involution reduces to the canonical inner extension or full semilinear
group; the proved rank-two-family calculation and inner-model rank-three
transfer supply full escape. The remaining nonsplit branch has all its
involutions in the linear kernel and uses the existing inner placement.

This module only composes those proved calculations at q=9. It preserves
the entire invariant family, weak closure, original Sylow intersections
and intrinsic E-member conditions. No extension or natural-action selection
is assumed. It closes the PSL₂(9) premise in the binary symplectic case.

Source: Aschbacher–Smith E.1.14(1),(6), printed p.214, with E.1.1–8,
printed pp.209–211 of refs/quasithin.pdf.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration
open SquareGeometry FieldWitnesses PureField

private theorem full_nine_escape {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 3^2) (σ : F ≃+* F) (hs : σ^2=1) (hne : σ ≠ 1)
    [Finite (PGammaL2 F)] :
    ∀ T : Sylow 2 (PGammaL2 F), LargeFamilyEscapeAt T := by
  exact FullEscape.largeFamilyEscape_of_rank_branches Nat.prime_three (by decide) hF
    (FullEscape.RankTwoFamilies.escape Nat.prime_three (by decide) hF (by decide) σ hs hne)
    (FullEscape.RankThreeFamilies.escape_of_innerModel_escape Nat.prime_three (by decide)
      hF (by decide) σ hs hne (InnerEscape.escape Nat.prime_three (by decide) hF σ hs hne))

private theorem pure_nine_escape {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 3^2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (σ : F ≃+* F) (hs : σ^2=1) (hne : σ ≠ 1)
    (hmem : SemidirectProduct.inr σ ∈ S) :
    ∀ T : Sylow 2 S, LargeFamilyEscapeAt T := by
  let : Finite (PGammaL2 F) := finiteFullModel
  exact largeFamilyEscape_of_canonical_models Nat.prime_three (by decide) hF σ hne
    (InnerEscape.escape Nat.prime_three (by decide) hF σ hs hne)
    (full_nine_escape hF σ hs hne) S hS hmem

/-- Every extension of the actual PSL₂(9) with trivial socle centralizer
has the large-family escape required by E.1.14. -/
theorem largeFamilyEscape_of_psl_nine {G : Type*} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    (hL : ClassicalGroup.IsPSL L 2 (3^2)) (hC : centralizer (L : Set G) = ⊥) :
    ∀ T : Sylow 2 G, LargeFamilyEscapeAt T := by
  apply largeFamilyEscape_of_model_calculations L Nat.prime_three (by decide) hL hC
  · intro F _ _ hF S _ hm
    exact LinearWitnesses.largeFamilyEscape_of_linear_model Nat.prime_three (by decide)
      (by decide) hF S hm
  · intro F _ _ hF S _ hS hi _
    exact largeFamilyEscape_of_involution_cases Nat.prime_three (by decide) (by decide)
      (fun F _ _ hF S _ hS σ hs hn hm => pure_nine_escape hF S hS σ hs hn hm)
      (fun F _ _ hF S _ hS hi hk hn => Noninvolutory.largeFamilyEscape
        Nat.prime_three (by decide) hF (by decide) S hS hi hk hn)
      hF S hS hi
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration
