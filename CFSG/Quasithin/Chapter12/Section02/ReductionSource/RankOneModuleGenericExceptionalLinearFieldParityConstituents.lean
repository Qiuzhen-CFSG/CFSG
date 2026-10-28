module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.DisplacementConstituents
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityOddQuotient

/-!
# Applying the residual constituent bound to the chosen module

The completed residual producer supplies maximality and nonfaithfulness for
the literal odd-degree product. H.4.7 then bounds the contribution from a
faithful constituent of the actual quotient action that is irreducible for
F*(H/O₂(H)). The conjugation coordinates keep U/Z₁ and the original subgroup
representatives throughout; an involution modulo the two-core needs no
involutory lift.

The F.8 geometry and the Cartan multiplicity step remain with the parity
assembly owner, qt-d-1222-linear-field-parity. This application proves only
the single-constituent bound, not the final nine-dimensional displacement.
Source: Aschbacher–Smith 5.1.17, printed p.641, used in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
  {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  (D : ChosenModule T L V)
include D

/-- The actual source product and the contribution of each faithful residual constituent. -/
theorem rankOne_odd_constituent_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (U : Subgroup G) (hf : (setup T L U H A).Hypothesis) :
    ∃ e : ((H ⧸ pCore 2 H) × A) ≃*
        ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)),
      (∀ (x : H) (a : A),
        e (QuotientGroup.mk' (pCore 2 H) x, a) =
          QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
            ⟨(x : G) * (a : G), mul_mem_sup x.property a.property⟩) ∧
      ∀ (ρ : Representation (ZMod 2)
          ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) X),
        BinaryConjugationSection (H ⊔ A) (setup T L U H A).U
          (setup T L U H A).V₁
          (ρ.comp (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G)))) →
        ∀ J : Subrepresentation (residualFactorAction e ρ),
          Function.Injective J.toRepresentation →
          IsIrreducible (J.toRepresentation.comp
            (generalizedFitting (H ⧸ pCore 2 H)).subtype) →
          ∀ y, y ∈ H → y ^ 2 ∈ H.pCoreIn 2 → y ∉ H.pCoreIn 2 →
            3 ≤ displacement (setup T L U H A) y := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hm,hf'⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact odd_constituent_displacement hi hH c hodd hm hf' hlinear U hf

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
