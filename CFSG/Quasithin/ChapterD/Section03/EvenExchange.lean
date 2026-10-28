module
public import CFSG.Quasithin.ChapterD.Section03.EvenTensor
public import Theory.Representation.SL2.EvenSquareExchange

/-!
# The even-linear exchanged tensor alternatives

A small cubic actor that exchanges two SL₂ factors has rank at most n+1.
If its exchanger fixes the actual Schur field, exact displacement and scalar
descent construct the whole binary natural tensor, including the exchange
twist. Otherwise the nontrivial Schur action moves at least half the space,
so the original binary dimension is at most 4(n+1).

The original Chapter 10 seed applies this alternative with its unchanged
quotient maps. Exclusion of the natural tensor, the remaining Schur action,
and the component-preserving constituent branch is still required there.
Source: Aschbacher--Smith D.3.7, printed pp.197--199.
-/


@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
local instance evenSquareExchangeAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2
open Representation.QuadraticFourGroup.TensorClassification

/-- The remaining explicit tensor alternatives. The natural branch carries a
whole-space binary intertwiner; the other exchange acts on the Schur field. -/
def EvenSquareTensorAnalysis
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V) (n : ℕ) : Prop :=
    (EvenFactorConstituent (σ.comp (MonoidHom.inl SL(2,F) SL(2,F))) n ∨
      EvenFactorConstituent (σ.comp (MonoidHom.inr SL(2,F) SL(2,F))) n) ∨
    (∃ α : MulAut SL(2,F), Nonempty (σ.Equiv (restrictScalars (k := ZMod 2)
      (externalTensor ((SL2.BinarySmall.embeddedNatural (RingHom.id F)).comp α.symm.toMonoidHom)
        (SL2.BinarySmall.embeddedNatural (RingHom.id F)))))) ∨
    ∃ A : Subgroup (linearNormalizer σ), IsElementaryTwo A ∧
      IsCubic (normalizerRepresentation σ) A ∧
      fixedCodim (normalizerRepresentation σ) A ≤ 2*rank A ∧ rank A ≤ n+1 ∧
      Module.finrank (ZMod 2) V ≤ 4*(n+1) ∧
      ∃ a ∈ A, a.val ∉ SquarePreserving.group σ ∧
        ¬ SchurNormalizer.IsSchurLinear σ a ∧ ∃ α : MulAut SL(2,F), ∀ g v,
          normalizerRepresentation σ a (σ g v)=
            σ (α g.2,α.symm g.1) (normalizerRepresentation σ a v)

/-- D.3.7's small Schur-linear exchange gives the actual natural tensor.
Every remaining exchange must move the original Schur field, and then the
entire binary degree is at most four times one plus the defining degree. -/
theorem even_square_tensor_analysis
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (n : ℕ) (hn : 3 ≤ n) (hF : Nat.card F=2^n)
    (h : EvenSquareAnalysis σ n) : EvenSquareTensorAnalysis σ n := by
  let := hi
  rcases h with hc | ⟨A,hA,hc,hd,hr,a,ha,hnorm,α,hex⟩
  · exact Or.inl hc
  · let : IsElementaryAbelian 2 A := hA.2
    have h2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a ha
    have hdisp := NaturalTensor.operatorFixedCodim_le_fixedCodim
      (normalizerRepresentation σ) A ha
    change Module.finrank (ZMod 2) (a.val.val-1).range ≤ _ at hdisp
    by_cases hlin : SchurNormalizer.IsSchurLinear σ a
    · exact Or.inr (Or.inl ⟨α,SL2.EvenSquare.twisted_schur_linear_exchange_natural
        σ hf n hn hF a h2 hlin α hex (hdisp.trans (hd.trans (by omega)))⟩)
    · have hb := SchurNormalizer.finrank_le_twice_fixedCodim σ a hlin
      rw [fixedCodim_zpowers_eq_displacement_rank] at hb
      change Module.finrank (ZMod 2) V ≤ 2*Module.finrank (ZMod 2) (a.val.val-1).range at hb
      exact Or.inr (Or.inr ⟨A,hA,hc,hd,hr,by omega,a,ha,hnorm,hlin,α,hex⟩)
end CFSG.Quasithin.ChapterD
