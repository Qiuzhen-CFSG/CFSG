module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.Commutator
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalInput

/-!
# The shadow commutator obstruction on the original chosen quotient

The two subgroups inside V are literal inverse images under
D.toCentralQuotient. The field is exactly S.field. The third subgroup is
nontrivial because its quotient subspace is nonzero. Thus the commutator
construction supplies a nonzero equivariant bilinear map on these same
ambient groups and applies the eigenvalue contradiction.

All displayed Cartan, commutator and scalar-structure inputs are still
intermediate obligations of 11.3.3--8. This is a conditional application,
not the source theorem 11.3.2 or the nonbinary natural exclusion.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.8--9 and the final paragraph of 11.3.2, printed p.775.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

local instance preimageElementary (U : Submodule (ZMod 2) D.chosenCentralQuotient) :
    IsElementaryAbelian 2 (D.centralQuotientPreimage U) :=
  D.centralQuotientPreimage_elementary U

/-- The terminal commutator contradiction on the same chosen central quotient.
Neither a bilinear pairing, its equivariance, nor a nonzero value is an input. -/
theorem centralQuotientPreimage_shadow_impossible (S : D.NonbinaryNaturalInput)
    (U₁ U₃ : Submodule (ZMod 2) D.chosenCentralQuotient) (hU₃ : U₃ ≠ ⊥)
    (W₂ X : Subgroup G) [IsMulCommutative W₂]
    [Module S.field.Carrier (Additive (D.centralQuotientPreimage U₁))]
    [Module S.field.Carrier (Additive W₂)]
    [Module S.field.Carrier (Additive (D.centralQuotientPreimage U₃))]
    (hc : ⁅D.centralQuotientPreimage U₁, W₂⁆ = D.centralQuotientPreimage U₃)
    (hz : D.centralQuotientPreimage U₃ ≤
      centralizer ((D.centralQuotientPreimage U₁ ⊔ W₂ : Subgroup G) : Set G))
    (hX₁ : X ≤ normalizer (D.centralQuotientPreimage U₁ : Set G))
    (hX₂ : X ≤ normalizer (W₂ : Set G))
    (hX₃ : X ≤ normalizer (D.centralQuotientPreimage U₃ : Set G))
    (hleft : ∀ a : S.field.Carrier, a ≠ 0 → ∃ x ∈ X,
      ScalarConjugation (D.centralQuotientPreimage U₁) x a ∧
      ScalarConjugation W₂ x (1 : S.field.Carrier) ∧
      ScalarConjugation (D.centralQuotientPreimage U₃) x a)
    (hright : ∀ a : S.field.Carrier, a ≠ 0 → ∃ x ∈ X,
      ScalarConjugation (D.centralQuotientPreimage U₁) x (1 : S.field.Carrier) ∧
      ScalarConjugation W₂ x a ∧
      ScalarConjugation (D.centralQuotientPreimage U₃) x a)
    {a : S.field.Carrier} (ha : a ≠ 0)
    (horder : orderOf a = 2 ^ S.field.degree - 1) (y : X)
    (hy₁ : ScalarConjugation (D.centralQuotientPreimage U₁) (y : G) (a ^ 2))
    (hy₂ : ScalarConjugation W₂ (y : G) a)
    (hy₃ : ScalarConjugation (D.centralQuotientPreimage U₃) (y : G) a⁻¹) : False :=
  false_of_cartan_commutator (D.centralQuotientPreimage U₁) W₂
    (D.centralQuotientPreimage U₃) X hc (D.centralQuotientPreimage_ne_bot U₃ hU₃)
    hz hX₁ hX₂ hX₃ hleft hright S.nonbinary ha horder y hy₁ hy₂ hy₃

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
