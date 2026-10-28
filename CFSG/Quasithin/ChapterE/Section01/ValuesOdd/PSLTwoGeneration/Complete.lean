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

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
/-!
# Complete odd PSL₂ rank-one E-generation

The quadratic-field proof composes the actual linear, pure-field and nonsplit
model calculations. For the full semilinear model its rank-two families escape
by their proved coordinate construction; its rank-three families transfer to
the canonical inner-field model. All small prime cases are included. Strong
quasithinness restricts the defining field to a prime or prime square, and the
simple-socle whole-group E₂ construction handles the remaining small actors.

Source: Aschbacher–Smith E.1.14(6), p.214, with E.1.1–8, pp.209–211.
-/
public section

open Subgroup GorensteinWalter Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration
open SquareGeometry FieldWitnesses PureField

private theorem full_square_escape {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hq : 5 < p^2)
    (hF : Nat.card F = p^2) (σ : F ≃+* F) (hs : σ^2=1) (hne : σ ≠ 1)
    [Finite (PGammaL2 F)] :
    ∀ T : Sylow 2 (PGammaL2 F), LargeFamilyEscapeAt T := by
  exact FullEscape.largeFamilyEscape_of_rank_branches hp ho hF
    (FullEscape.RankTwoFamilies.escape hp ho hF hq σ hs hne)
    (FullEscape.RankThreeFamilies.escape_of_innerModel_escape hp ho
      hF hq σ hs hne (InnerEscape.escape hp ho hF σ hs hne))

private theorem pure_square_escape {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hq : 5 < p^2)
    (hF : Nat.card F = p^2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (σ : F ≃+* F) (hs : σ^2=1) (hne : σ ≠ 1)
    (hmem : SemidirectProduct.inr σ ∈ S) :
    ∀ T : Sylow 2 S, LargeFamilyEscapeAt T := by
  let : Finite (PGammaL2 F) := finiteFullModel
  exact largeFamilyEscape_of_canonical_models hp ho hF σ hne
    (InnerEscape.escape hp ho hF σ hs hne)
    (full_square_escape hp ho hq hF σ hs hne) S hS hmem

/-- Every self-centralizing normal prime-square PSL₂ socle supplies the actual
large-family escape, including all diagonal and field extensions. -/
theorem largeFamilyEscape_of_square_socle {G : Type*} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hq : 5 < p^2)
    (hL : ClassicalGroup.IsPSL L 2 (p^2)) (hC : centralizer (L : Set G) = ⊥) :
    ∀ T : Sylow 2 G, LargeFamilyEscapeAt T := by
  apply largeFamilyEscape_of_model_calculations L hp ho hL hC
  · intro F _ _ hF S _ hm
    exact LinearWitnesses.largeFamilyEscape_of_linear_model hp ho
      hq hF S hm
  · intro F _ _ hF S _ hS hi _
    exact largeFamilyEscape_of_involution_cases hp ho hq
      (fun F _ _ hF S _ hS σ hs hn hm => pure_square_escape hp ho hq hF S hS σ hs hn hm)
      (fun F _ _ hF S _ hS hi hk hn => Noninvolutory.largeFamilyEscape
        hp ho hF hq S hS hi hk hn)
      hF S hS hi
/-- Odd PSL₂ with simple generalized Fitting subgroup and an actual Sylow
supplement is rank-one E-generated. All large-family and small-actor
calculations are discharged, with no additional local geometry hypothesis. -/
theorem isEGenerated_one_of_model {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} (hG : IsSQTK κ G)
    [IsSimpleGroup (generalizedFitting G)] (T : Sylow 2 G)
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {q : ℕ} (ho : Odd q) (hq : 5 < q)
    (hm : ClassicalGroup.IsPSL (generalizedFitting G) 2 q) : IsEGenerated 1 G := by
  have hn := nonabelian_of_model (generalizedFitting G) hq hm
  have hs := SimpleSocle.structure_of_sylow_supplement hn T hLT
  apply isEGenerated_of_prime_and_square_calculations hG (generalizedFitting G) ho hq hm
  · intro S A _ _ hne
    exact ValuesEvenClassical.RankOneUpper.eCaseComponent_top hn T hLT (S : Subgroup G) A hne
  · intro p hp hpo hp5 hmodel
    exact PrimeGeometry.largeFamilyEscape_of_prime_socle hp hpo hp5 hmodel hs.1 hs.2.2.1
  · intro p hp hpo hp5 hmodel
    exact largeFamilyEscape_of_square_socle (generalizedFitting G) hp hpo hp5 hmodel hs.1
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration
