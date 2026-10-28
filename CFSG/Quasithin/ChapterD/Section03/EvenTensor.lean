module
public import CFSG.Quasithin.ChapterD.Section03.EvenConstituent
public import Theory.Representation.BinaryOffender.SquarePreserving
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Even-linear tensor constituents and genuine exchanges

A small cubic actor preserving both simple factors yields a proper faithful
constituent of binary degree twice the field degree, with an actual natural
or Hermitian intertwiner. The component and its original matrix marking are
retained in either factor orientation. The other branch constructs an actual
twisted exchange on the original square representation; the same actor has
rank at most one plus the field degree.

This is the constituent/exchange reduction in D.3.7, not a tensor exclusion:
the natural tensor is a genuine small cubic module. The original Chapter10
application must still use its ambient hypotheses to eliminate that case.
Source: Aschbacher--Smith D.3.7, printed pp.197--199.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
local instance evenTensorAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- An actual irreducible proper factor constituent, retaining its matrix action
and binary intertwiner, rather than merely its dimension or group family. -/
def EvenFactorConstituent (τ : Representation (ZMod 2) SL(2,F) V) (n : ℕ) : Prop :=
  ∃ U : Subrepresentation τ, U.toRepresentation.IsIrreducible ∧
    Function.Injective U.toRepresentation ∧ U.toSubmodule ≠ ⊤ ∧
    Module.finrank (ZMod 2) U.toSubmodule = 2*n ∧
    (SL2.BinarySmall.IsNatural U.toRepresentation ∨
      ∃ s : ℕ, n = 2*s ∧ ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩;
        SL2.BinarySmall.IsHermitian U.toRepresentation s)

/-- The two concrete constituent models, or an actual twisted exchange with
its original cubic actor and the sharp rank bound. -/
def EvenSquareAnalysis (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (n : ℕ) : Prop :=
    (EvenFactorConstituent (σ.comp (MonoidHom.inl SL(2,F) SL(2,F))) n ∨
      EvenFactorConstituent (σ.comp (MonoidHom.inr SL(2,F) SL(2,F))) n) ∨
    ∃ A : Subgroup (linearNormalizer σ), IsElementaryTwo A ∧
      IsCubic (normalizerRepresentation σ) A ∧
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A ∧
      rank A ≤ n+1 ∧ ∃ a ∈ A, a.val ∉ SquarePreserving.group σ ∧ ∃ α : MulAut SL(2,F), ∀ g v,
        normalizerRepresentation σ a (σ g v) =
          σ (α g.2,α.symm g.1) (normalizerRepresentation σ a v)

variable [IsSimpleGroup SL(2,F)] [IsQuasisimple SL(2,F)]

/-- Small actors preserving the two factors force a genuine small constituent
in at least one of the two literal factor restrictions. Outer actors are retained. -/
theorem even_square_preserving_constituent
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (hS : IsSQTK KnownSimple.IsKnownSimple SL(2,F))
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hsmall : cubicRatio (SquarePreserving.action σ) ≤ 2) :
    EvenFactorConstituent (σ.comp (MonoidHom.inl SL(2,F) SL(2,F))) n ∨
      EvenFactorConstituent (σ.comp (MonoidHom.inr SL(2,F) SL(2,F))) n := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let ρ := SquarePreserving.action σ
  let L := SquarePreserving.left σ
  let K := SquarePreserving.right σ
  let eL := SquarePreserving.leftEquiv σ hf
  let eK := SquarePreserving.rightEquiv σ hf
  let : IsSimpleGroup L := eL.symm.isSimpleGroup
  let : IsSimpleGroup K := eK.symm.isSimpleGroup
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv eK
  let : Nontrivial L := eL.symm.surjective.nontrivial
  let : Nontrivial K := eK.symm.surjective.nontrivial
  have hρ := SquarePreserving.action_faithful σ
  have hirr := SquarePreserving.pair_irreducible σ hi hf
  have hcomm := SquarePreserving.right_centralizes_left σ
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hsmall
  rcases pair_actor_moves_factor ρ L K hirr hρ A hA.1.2.1 with hm | hm
  · obtain ⟨U,hU,hfU,hproper,_,_,_,hd,hmodel⟩ := even_pair_moved_constituent
      ρ hρ L K (hS.knownSimple_of_equiv eL) eL.symm n hn hF hirr hcomm A hA hm
    let U' := U.compActors eL.toMonoidHom
    have hi' : U'.toRepresentation.IsIrreducible :=
      (irreducible_comp_surjective_iff eL.toMonoidHom eL.surjective U.toRepresentation).mpr hU
    exact Or.inl ⟨U',hi',hfU.comp eL.injective,hproper,hd,hmodel⟩
  · obtain ⟨U,hU,hfU,hproper,_,_,_,hd,hmodel⟩ := even_pair_moved_constituent
      ρ hρ K L (hS.knownSimple_of_equiv eK) eK.symm n hn hF (by rwa [sup_comm])
      (le_centralizer_iff.mp hcomm) A hA hm
    let U' := U.compActors eK.toMonoidHom
    have hi' : U'.toRepresentation.IsIrreducible :=
      (irreducible_comp_surjective_iff eK.toMonoidHom eK.surjective U.toRepresentation).mpr hU
    exact Or.inr ⟨U',hi',hfU.comp eK.injective,hproper,hd,hmodel⟩

/-- For the full square normalizer, either an actual small cubic actor moves
one of the factor images, or a natural/Hermitian constituent is constructed.
This exhausts actors without assuming that they belong to the inner square. -/
theorem even_square_constituent_or_exchange
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (hS : IsSQTK KnownSimple.IsKnownSimple SL(2,F))
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hsmall : cubicRatio (normalizerRepresentation σ) ≤ 2) :
    EvenSquareAnalysis σ n := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff (normalizerRepresentation σ) 2).mp hsmall
  by_cases hpres : ∀ a ∈ A, a.val ∈ SquarePreserving.group σ
  · exact Or.inl (even_square_preserving_constituent σ hi hf hS n hn hF
      (SquarePreserving.cubic_le_of_preserving_actor σ A hA hc hd
        (fun a ha => (hpres a ha).1) (fun a ha => (hpres a ha).2)))
  · push Not at hpres
    obtain ⟨a,ha,hnorm⟩ := hpres
    let : IsElementaryAbelian 2 A := hA.2
    have h2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a ha
    obtain ⟨α,hα⟩ := (SquarePreserving.involution_preserves_or_exchanges σ
      center_eq_bot_of_simple_perfect hf a h2).resolve_left hnorm
    have hr := SquarePreserving.twisted_exchange_rank_le σ
      center_eq_bot_of_simple_perfect hi hf A a ha α hα
    have hfield := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le
      (F := F) (show 2 ≤ n from by omega) hF
    have hrank : rank A ≤ n+1 := hr.trans (Nat.add_le_add_right hfield 1)
    exact Or.inr ⟨A,hA,hc,hd,hrank,a,ha,hnorm,α,hα⟩
end CFSG.Quasithin.ChapterD
