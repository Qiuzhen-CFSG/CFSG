module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport

/-!
# Escape in the two canonical pure-field models

The supplied pure field involution splits the actual matrix subgroup as the
join of its linear kernel and that involution. The kernel alternatives
therefore identify the subgroup with either the canonical PSL₂ extension
or the full PΓL₂. The theorem below transports escape from precisely these
two models, preserving the family, intrinsic E-member quotients and literal
Sylow intersection through `EscapeTransport`.

Both model calculations are explicit remaining premises. Neither this
conditional assembly nor the constructed rank-three actor proves the hpure
input of `FieldWitnesses.largeFamilyEscape_of_involution_cases` yet.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.3(2), E.1.2 and E.1.14(6), printed pp.33, 209--210 and 214;
the last cites Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField
universe u
variable {F : Type u} [Field F] [Finite F]

/-- Finiteness of the full matrix model, used locally in the assembly signature. -/
theorem finiteFullModel : Finite (PGammaL2 F) := by
  let : Finite (PGL2 F) := Finite.of_surjective
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  exact Finite.of_equiv (PGL2 F × (F ≃+* F)) SemidirectProduct.equivProd.symm

attribute [local instance] finiteFullModel

/-- Conditional final assembly for the pure-field branch. The two remaining
inputs concern fixed, actual matrix models, rather than arbitrary extensions. -/
theorem largeFamilyEscape_of_canonical_models {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (σ : F ≃+* F) (hne : σ ≠ 1)
    (hinner : ∀ T : Sylow 2 (innerModel F σ), LargeFamilyEscapeAt T)
    (hfull : ∀ T : Sylow 2 (PGammaL2 F), LargeFamilyEscapeAt T)
    (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (hσ : SemidirectProduct.inr σ ∈ S) :
    ∀ T : Sylow 2 S, LargeFamilyEscapeAt T := by
  rcases eq_innerModel_or_top hp hodd hF S hS σ hne hσ with h | h
  · exact largeFamilyEscape_of_equiv (MulEquiv.subgroupCongr h).symm hinner
  · exact largeFamilyEscape_of_equiv
      ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv).symm hfull

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField
