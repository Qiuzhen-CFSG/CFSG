module

public import CFSG.Quasithin.Chapter3.Section02.SourceXiSigns
public import Theory.GroupAction.TwoCyclicFiveFactors

/-!
# The literal automizer conclusion from two preserved Frattini factors

Restriction to two generating order-five subgroups gives a two-group on the
Frattini quotient. Burnside's automorphism kernel then gives the {2,5}
condition on the original image of N_G(X) acting on X/O₂(X).

The two subgroups and their preservation are explicit here. The source
small-support argument must construct them from the original module; this
conditional application does not assert that construction.

Source: Aschbacher--Smith, 3.2.13, printed pp.584--585.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Two actual generating order-five subgroups of the source Frattini
quotient, permuted by the original ambient normalizer action. -/
@[expose] def HasNormalizerFrattiniPair (X : Subgroup G) : Prop :=
  ∃ B C : Subgroup (Chapter1.XiFrattiniQuotient X),
    Nat.card B = 5 ∧ Nat.card C = 5 ∧ B ≠ C ∧ B ⊔ C = ⊤ ∧
    ∀ n : normalizer (X : Set G),
      let f := quotientAut (frattini (Chapter1.XiQuotient X))
        (Chapter3.xiQuotientNormalizerAction X n)
      (B.map f.toMonoidHom = B ∧ C.map f.toMonoidHom = C) ∨
      (B.map f.toMonoidHom = C ∧ C.map f.toMonoidHom = B)

/-- Two preserved Frattini factors control precisely the automizer occurring
in Definition 3.2.12, without replacing it by an abstract automorphism group. -/
theorem source_mem_XiMinus_of_frattini_pair {T X : Subgroup G}
    (hX : X ∈ Chapter1.Xi G T) (h5 : IsPGroup 5 (Chapter1.XiQuotient X))
    (B C : Subgroup (Chapter1.XiFrattiniQuotient X))
    (hB : Nat.card B = 5) (hC : Nat.card C = 5) (hne : B ≠ C)
    (hgen : B ⊔ C = ⊤)
    (hperm : ∀ n : normalizer (X : Set G),
      let f := quotientAut (frattini (Chapter1.XiQuotient X))
        (Chapter3.xiQuotientNormalizerAction X n)
      (B.map f.toMonoidHom = B ∧ C.map f.toMonoidHom = C) ∨
      (B.map f.toMonoidHom = C ∧ C.map f.toMonoidHom = B)) :
    X ∈ Chapter3.XiMinus G T := by
  refine ⟨hX, Or.inr ⟨h5, ?_⟩⟩
  apply prime_divisors_of_permutes_frattini_order_five_pair h5
    (Chapter3.xiQuotientAutomizer X) B C hB hC hne hgen
  intro a
  obtain ⟨n, hn⟩ := a.property
  simpa only [← hn] using hperm n

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
