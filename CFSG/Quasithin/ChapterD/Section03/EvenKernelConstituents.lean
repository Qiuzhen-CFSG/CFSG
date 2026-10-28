module
public import CFSG.Quasithin.ChapterD.Section03.EvenFaithfulPair
public import Theory.Representation.SL2.PairNatural

/-!
# Natural or Hermitian constituents for the two-kernel square

Disjoint nonzero kernels in the same preserving starred actor force movement
of both factors. The original strict constituent descent therefore applies
in both orientations. If both constituents are natural, cubic fixed-point
freeness on the two full restrictions gives dimension 4n and the whole-space
natural tensor, including its factor twist.

Every remaining square has even field degree and an actual Hermitian
constituent over the fixed half-field. Both original component constituents
and both actor kernels remain in the output. The Chapter 10 central Hall
consumer supplies all inputs; Hermitian exclusion and the ambient natural
tensor exclusion are still needed for the source theorem.
Source: Aschbacher--Smith D.3.7, printed pp.198--199, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.QuadraticFourGroup.TensorClassification
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- Both kernels are used: the same actor moves both original components. -/
theorem even_square_double_kernel_constituents
    [IsSimpleGroup SL(2,F)] [IsQuasisimple SL(2,F)]
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (hS : IsSQTK KnownSimple.IsKnownSimple SL(2,F))
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F=2^n)
    (hd : EvenSquareDoubleKernel σ) :
    EvenFactorConstituent (σ.comp (MonoidHom.inl _ _)) n ∧
      EvenFactorConstituent (σ.comp (MonoidHom.inr _ _)) n := by
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
  have hirr := SquarePreserving.pair_irreducible σ hi hf
  have hcomm := SquarePreserving.right_centralizes_left σ
  have hρ := SquarePreserving.action_faithful σ
  obtain ⟨A,hA,hL,hK,hdis⟩ := hd
  have hmL : ¬ A ≤ centralizer (L : Set (SquarePreserving.group σ)) := by
    intro hh
    apply hK
    apply bot_unique
    intro a ha
    exact (disjoint_def.mp hdis ⟨ha.1,hh ha.1⟩ ha)
  have hmK : ¬ A ≤ centralizer (K : Set (SquarePreserving.group σ)) := by
    intro hh
    apply hL
    apply bot_unique
    intro a ha
    exact (disjoint_def.mp hdis ha ⟨ha.1,hh ha.1⟩)
  constructor
  · obtain ⟨U,hU,hfU,hproper,_,_,_,hd,hmodel⟩ := even_pair_moved_constituent
      ρ hρ L K (hS.knownSimple_of_equiv eL) eL.symm n hn hF hirr hcomm A hA hmL
    let U' := U.compActors eL.toMonoidHom
    have hi' : U'.toRepresentation.IsIrreducible :=
      (irreducible_comp_surjective_iff eL.toMonoidHom eL.surjective U.toRepresentation).mpr hU
    exact ⟨U',hi',hfU.comp eL.injective,hproper,hd,hmodel⟩
  · obtain ⟨U,hU,hfU,hproper,_,_,_,hd,hmodel⟩ := even_pair_moved_constituent
      ρ hρ K L (hS.knownSimple_of_equiv eK) eK.symm n hn hF (by rwa [sup_comm])
      (le_centralizer_iff.mp hcomm) A hA hmK
    let U' := U.compActors eK.toMonoidHom
    have hi' : U'.toRepresentation.IsIrreducible :=
      (irreducible_comp_surjective_iff eK.toMonoidHom eK.surjective U.toRepresentation).mpr hU
    exact ⟨U',hi',hfU.comp eK.injective,hproper,hd,hmodel⟩

/-- The actual Hermitian constituent, including the unchanged factor marking. -/
@[expose] def EvenFactorHermitian (τ : Representation (ZMod 2) SL(2,F) V)
    (s : ℕ) [NeZero s] : Prop :=
  ∃ U : Subrepresentation τ, U.toRepresentation.IsIrreducible ∧
    Function.Injective U.toRepresentation ∧ U.toSubmodule ≠ ⊤ ∧
    Module.finrank (ZMod 2) U.toSubmodule = 4*s ∧ SL2.BinarySmall.IsHermitian U.toRepresentation s

/-- Every remaining non-natural square has an actual Hermitian constituent and
both nonzero actor kernels. Both component constituent statements are retained. -/
@[expose] def EvenSquareHermitianKernel
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V) (n : ℕ) : Prop :=
  EvenSquareDoubleKernel σ ∧
  EvenFactorConstituent (σ.comp (MonoidHom.inl _ _)) n ∧
  EvenFactorConstituent (σ.comp (MonoidHom.inr _ _)) n ∧
  ∃ s : ℕ, n = 2*s ∧ ∃ hs : 1 < s, letI : NeZero s := ⟨(by omega)⟩;
    EvenFactorHermitian (σ.comp (MonoidHom.inl _ _)) s ∨
      EvenFactorHermitian (σ.comp (MonoidHom.inr _ _)) s

variable {n : ℕ}

/-- Two natural constituents close the two-kernel calculation; all other
non-natural squares retain a genuine Hermitian constituent of even field degree. -/
theorem even_square_natural_or_hermitian_kernel
    [IsSimpleGroup SL(2,GaloisField 2 n)] [IsQuasisimple SL(2,GaloisField 2 n)]
    (σ : Representation (ZMod 2) (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (hS : IsSQTK KnownSimple.IsKnownSimple SL(2,GaloisField 2 n))
    (hn : 3 ≤ n) (hsmall : cubicRatio (normalizerRepresentation σ) ≤ 2) :
    (∃ α : MulAut SL(2,GaloisField 2 n), Nonempty (σ.Equiv (restrictScalars (k := ZMod 2)
      (externalTensor
        ((SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n))).comp α.symm.toMonoidHom)
        (SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n))))))) ∨
      EvenSquareHermitianKernel σ n := by
  let := hi
  rcases even_square_natural_or_double_kernel σ hi hf hS n hn
      (GaloisField.card 2 n (by omega)) hsmall with hnat | hk
  · exact Or.inl hnat
  have hc := even_square_double_kernel_constituents σ hi hf hS n
    (by omega) (GaloisField.card 2 n (by omega)) hk
  obtain ⟨I,hI,hfI,hIt,hdI,hmodI⟩ := hc.1
  obtain ⟨J,hJ,hfJ,hJt,hdJ,hmodJ⟩ := hc.2
  rcases hmodI with hnatI | ⟨s,hs,hpos,hherm⟩
  · rcases hmodJ with hnatJ | ⟨s,hs,hpos,hherm⟩
    · have hdim := SL2.PairNatural.degree_of_natural_constituents σ (by omega)
        ⟨I,hI,hnatI⟩ ⟨J,hJ,hnatJ⟩
      exact Or.inl (SL2.SmallSquare.small_square_natural_tensor σ hf n hn
        (GaloisField.card 2 n (by omega)) (by omega))
    · exact Or.inr ⟨hk,hc.1,hc.2,s,hs,(by omega),Or.inr
        ⟨J,hJ,hfJ,hJt,(by omega),hherm⟩⟩
  · exact Or.inr ⟨hk,hc.1,hc.2,s,hs,(by omega),Or.inl
      ⟨I,hI,hfI,hIt,(by omega),hherm⟩⟩
end CFSG.Quasithin.ChapterD
