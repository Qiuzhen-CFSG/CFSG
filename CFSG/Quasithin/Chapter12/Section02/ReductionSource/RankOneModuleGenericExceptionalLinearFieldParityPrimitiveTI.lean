module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupPrimitiveTI
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityKernelFusion

/-!
# The primitive point actor on the chosen Chapter12 module

The original chosen module supplies its proved natural Fundamental Setup.
Zsigmondy then constructs a prime Cartan subgroup acting irreducibly on
Ω₁Z(T) ∩ V. Its normalizer has point TI. The second application selects a
Sylow subgroup of the point stabilizer in the literal quotient-centralizer
and proves TI under that Sylow subgroup's full ambient normalizer.

The parity owner qt-d-1222-linear-field-parity retains the promotion to a
Sylow subgroup of the entire quotient-centralizer, full residual-normalizer
TI, block exclusion and Seed discharge. These results impose no natural
marking or irreducibility callback and use no Suzuki recognition premise.
Source: Aschbacher–Smith 5.1.17, p.640, used in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The actual primitive Cartan actor and its normalizer's point TI. -/
theorem rankOne_odd_primitive_point_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n) :
    ∃ (p : ℕ) (C : Subgroup G), p.Prime ∧ p ≠ 2 ∧
      orderOf (2 : ZMod p) = n ∧ C ≤ A ∧ Nat.card C = p ∧
      (∀ X : Subgroup G, X ≤ (setup T L V H A).V₁ →
        C ≤ normalizer (X : Set G) → X = ⊥ ∨ X = (setup T L V H A).V₁) ∧
      ∀ g ∈ normalizer (C : Set G),
        (setup T L V H A).V₁ ⊓
            (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁ := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_primitive_actor_exists F hi.sylow_normalizes hpsl hn hodd hnat c

/-- A literal Sylow subgroup of the quotient-centralizer point stabilizer
containing the primitive actor, with TI under its full ambient normalizer. -/
theorem rankOne_odd_point_stabilizer_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n) :
    let J := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
      (normalizer (residual H : Set G)).subtype ⊓ (setup T L V H A).G₁
    ∃ (p : ℕ) (_hp : Fact p.Prime) (C : Subgroup G) (P : Sylow p J),
      p ≠ 2 ∧ orderOf (2 : ZMod p) = n ∧ C ≤ A ∧ Nat.card C = p ∧
      C ≤ (P : Subgroup J).map J.subtype ∧
      ∀ g ∈ normalizer ((P : Subgroup J).map J.subtype : Set G),
        (setup T L V H A).V₁ ⊓
            (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁ := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_point_stabilizer_sylow_exists hi hH hm hnf hlinear F hodd hnat c

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
