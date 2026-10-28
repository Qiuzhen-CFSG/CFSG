module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.ResidualCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.SourceCatalogue
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.Quasithin.CoprimeRank

/-!
# Excluding the nonquasisimple source rows

The full A.3.6 common data identify the Fitting subgroup with the odd core.
In both the natural and nilpotent rows the quotient by this literal subgroup
is an odd-characteristic SL₂. Its two-rank is one, and the odd kernel does
not increase two-rank. This contradicts the rank lower bound supplied by
the original moved-component geometry.

Source: Aschbacher--Smith, A.3.6(2c,d), used in 3.3.12 and 3.3.16,
printed pp.589--591. Recognition and the terminal application remain with
qt-d-1222-natural-line-action.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}

open Chapter1.Section02 Chapter1.Section02.LocalModels
open scoped MatrixGroups

private theorem rank_one_of_odd_fitting_sl2 {Q : Type*} [Group Q] [Finite Q]
    (hc : A36Common Q) {p : ℕ} (ho : Odd p)
    (hm : IsSL (Q ⧸ fittingSubgroup Q) 2 p) : primeRank 2 Q ≤ 1 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup Q))
  have hk : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',hc.1]
    exact pPrimeCore_coprime_card
  have hr := primeRank_le_of_coprime_ker 2 f hk
  rw [Matrix.SpecialLinearGroup.primeRank_two_eq_one
    (Field.two_ne_zero_of_odd_card F (hF ▸ ho))] at hr
  exact hr

private theorem natural_rank_one {Q : Type*} [Group Q] [Finite Q]
    (h : A36Natural Q) (hc : A36Common Q) : primeRank 2 Q ≤ 1 := by
  obtain ⟨p,hp,hlarge,F,hF,hfin,hcard,v,e,_⟩ := h.2
  apply rank_one_of_odd_fitting_sl2 hc (hp.odd_of_ne_two (by omega))
  exact ⟨F,hF,hfin,hcard,⟨(QuotientGroup.quotientMulEquivOfEq h.1).symm.trans e⟩⟩

private theorem nilpotent_rank_one {Q : Type*} [Group Q] [Finite Q]
    (h : A36Nilpotent Q) (hc : A36Common Q) : primeRank 2 Q ≤ 1 := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h.2.2.1
  apply rank_one_of_odd_fitting_sl2 hc (by decide : Odd 5)
  exact ⟨F,hF,hfin,hcard,⟨(QuotientGroup.quotientMulEquivOfEq h.1).symm.trans e⟩⟩

namespace MovedComponent
variable (E : MovedComponent S f A)

/-- Exclude the natural A.3.6 row using its literal odd-kernel SL₂ quotient. -/
theorem quotient_not_natural :
    ¬ A36Natural (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  intro hn
  have hu := natural_rank_one hn E.componentQuotient_source.2
  rw [primeRank_equiv 2 topEquiv] at hu
  have hl := E.quotient_rank_two_ge_two
  omega

/-- Exclude the nilpotent A.3.6 row using its literal odd-kernel SL₂(5) quotient. -/
theorem quotient_not_nilpotent :
    ¬ A36Nilpotent (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  intro hn
  have hu := nilpotent_rank_one hn E.componentQuotient_source.2
  rw [primeRank_equiv 2 topEquiv] at hu
  have hl := E.quotient_rank_two_ge_two
  omega

end MovedComponent
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
