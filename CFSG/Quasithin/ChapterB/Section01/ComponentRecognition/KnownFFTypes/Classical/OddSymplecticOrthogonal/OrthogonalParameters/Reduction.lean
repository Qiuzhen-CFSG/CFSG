module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.ImageReduction
public import Theory.Representation.BinaryOffender.QuasisimpleNormalizer
public import Theory.Representation.BinaryOffender.EndFieldTransport

/-!
# The actual orthogonal action in the cross-characteristic problem

An offender in the full linear normalizer generates, together with the
component image, a finite supplement whose generalized Fitting subgroup is
that image. Its action is faithful and its restriction to the component is
irreducible. Passing to the supplement's commuting endomorphism field gives
an absolutely irreducible action with the same offender cardinality inequality.
The component's central quotient is identified with the original quotient.

The three applications retain the exact catalogue predicates and concrete
orthogonal carriers, including split rank three and minus rank two. These
reductions establish the input to the representation estimates, not those
estimates or the requested numerical restrictions.

Source: Aschbacher--Smith B.1.11--13, printed pp.72--74; Guralnick--Malle,
*Classification of 2F-modules, I*, Introduction and Proposition 4.5. See
`Source.md` in this directory for the distinction between F and 2F.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped MonoidAlgebra

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.OrthogonalParameters

universe u v
variable {L : Type u} {W : Type v} [Group L] [IsQuasisimple L]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (σ : Representation (ZMod 2) L W)

/-- The faithful supplement retains the original binary module and central quotient.
No assertion about F* of the full linear normalizer is used. -/
theorem exists_binary_supplement (hk : σ.ker ≤ center L)
    (hi : σ.IsIrreducible) (hff : IsFFModule (normalizerRepresentation σ)) :
    ∃ (H : Type v) (_ : Group H) (_ : Finite H)
      (N : Subgroup H) (_ : N.Normal) (_ : IsQuasisimple N)
      (ρ : Representation (ZMod 2) H W),
      generalizedFitting H = N ∧ Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Representation.IsIrreducible (ρ.comp N.subtype) ∧ IsFFModule ρ ∧
      Nonempty (L ⧸ center L ≃* N ⧸ center N) := by
  let := hi
  obtain ⟨A, hA⟩ := hff
  let H := supplement σ A
  let N := component σ A
  let : Finite H := supplement_finite σ A
  let : N.Normal := component_normal σ A
  let : IsQuasisimple N := component_quasisimple σ hk A
  exact ⟨H, inferInstance, inferInstance, N, inferInstance, inferInstance,
    linearAction H, supplement_fitting σ hk A hA.1.2, linearAction_injective H,
    supplement_irreducible σ A, component_irreducible σ A, supplement_ff σ A hA,
    ⟨(cover σ hk A).quotientCenterEquiv⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The scalar change is made for the supplement, so the offender remains a
linear actor. Absolute irreducibility of its component restriction is not claimed. -/
theorem exists_absolute_supplement (hk : σ.ker ≤ center L)
    (hi : σ.IsIrreducible) (hff : IsFFModule (normalizerRepresentation σ)) :
    ∃ (H : Type v) (_ : Group H) (_ : Finite H)
      (N : Subgroup H) (_ : N.Normal) (_ : IsQuasisimple N)
      (E : Type v) (_ : Field E) (_ : Finite E) (_ : CharP E 2)
      (_ : Module E W) (_ : FiniteDimensional E W)
      (ρ : Representation E H W),
      generalizedFitting H = N ∧ Function.Injective ρ ∧ ρ.IsAbsolutelyIrreducible ∧
      Representation.IsIrreducible (ρ.comp N.subtype) ∧
      Nonempty (L ⧸ center L ≃* N ⧸ center N) ∧
      ∃ A : Subgroup H, IsElementaryTwo A ∧
        Nat.card W ≤ Nat.card A * Nat.card (Representation.invariants (ρ.comp A.subtype)) := by
  obtain ⟨H, hH, hfin, N, hn, hqs, τ, hfit, hf, hirr, hn_irr, hff, he⟩ :=
    exists_binary_supplement σ hk hi hff
  let := hirr
  let := hn_irr
  let E := Module.End (ZMod 2)[H] τ.asModule
  let : CharP E 2 := endFieldRep_charTwo τ
  let : Module E W := endFieldModule τ
  let : FiniteDimensional E W := endFieldRep_finiteDimensional τ
  refine ⟨H, hH, hfin, N, hn, hqs, E, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, τ.endFieldRep,
    hfit, endFieldRep_injective τ hf, endFieldRep_isAbsolutelyIrreducible τ,
    endFieldRep_comp_isIrreducible τ N, he, ?_⟩
  exact (isFFModule_iff_endField_card τ).mp hff

omit [FiniteDimensional (ZMod 2) W] in
/-- Split models pass through the actual central covering map without changing
the rank-three part of the catalogue. -/
theorem supplement_orthogonalPlus (hk : σ.ker ≤ center L)
    (A : Subgroup (linearNormalizer σ)) {r q : ℕ}
    (hp : KnownSimple.OrthogonalPlusParameters r q)
    (hm : ClassicalGroup.IsPOmegaPlus (L ⧸ center L) r q) :
    KnownSimple.OrthogonalPlusParameters r q ∧
      ClassicalGroup.IsPOmegaPlus
        (component σ A ⧸ center (component σ A)) r q :=
  ⟨hp, hm.of_mulEquiv (cover σ hk A).quotientCenterEquiv.symm⟩

omit [FiniteDimensional (ZMod 2) W] in
/-- Odd orthogonal models pass through the actual central covering map. -/
theorem supplement_orthogonalOdd (hk : σ.ker ≤ center L)
    (A : Subgroup (linearNormalizer σ)) {r q : ℕ}
    (hp : KnownSimple.OrthogonalOddParameters r q)
    (hm : ClassicalGroup.IsPOmegaOdd (L ⧸ center L) r q) :
    KnownSimple.OrthogonalOddParameters r q ∧
      ClassicalGroup.IsPOmegaOdd
        (component σ A ⧸ center (component σ A)) r q :=
  ⟨hp, hm.of_mulEquiv (cover σ hk A).quotientCenterEquiv.symm⟩

omit [FiniteDimensional (ZMod 2) W] in
/-- Minus models pass through the actual central covering map, including
every rank-two parameter. -/
theorem supplement_orthogonalMinus (hk : σ.ker ≤ center L)
    (A : Subgroup (linearNormalizer σ)) {r q : ℕ}
    (hp : KnownSimple.OrthogonalMinusParameters r q)
    (hm : ClassicalGroup.IsPOmegaMinus (L ⧸ center L) r q) :
    KnownSimple.OrthogonalMinusParameters r q ∧
      ClassicalGroup.IsPOmegaMinus
        (component σ A ⧸ center (component σ A)) r q :=
  ⟨hp, hm.of_mulEquiv (cover σ hk A).quotientCenterEquiv.symm⟩

/-- The binary supplement construction with any of the three literal orthogonal
models. The parameter predicates and quotient witness are carried together. -/
theorem exists_orthogonal_supplement (hk : σ.ker ≤ center L)
    (hi : σ.IsIrreducible) (hff : IsFFModule (normalizerRepresentation σ))
    {r q : ℕ}
    (hm :
      (KnownSimple.OrthogonalPlusParameters r q ∧
        ClassicalGroup.IsPOmegaPlus (L ⧸ center L) r q) ∨
      (KnownSimple.OrthogonalOddParameters r q ∧
        ClassicalGroup.IsPOmegaOdd (L ⧸ center L) r q) ∨
      (KnownSimple.OrthogonalMinusParameters r q ∧
        ClassicalGroup.IsPOmegaMinus (L ⧸ center L) r q)) :
    ∃ (H : Type v) (_ : Group H) (_ : Finite H)
      (N : Subgroup H) (_ : N.Normal) (_ : IsQuasisimple N)
      (ρ : Representation (ZMod 2) H W),
      generalizedFitting H = N ∧ Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Representation.IsIrreducible (ρ.comp N.subtype) ∧ IsFFModule ρ ∧
      ((KnownSimple.OrthogonalPlusParameters r q ∧
          ClassicalGroup.IsPOmegaPlus (N ⧸ center N) r q) ∨
        (KnownSimple.OrthogonalOddParameters r q ∧
          ClassicalGroup.IsPOmegaOdd (N ⧸ center N) r q) ∨
        (KnownSimple.OrthogonalMinusParameters r q ∧
          ClassicalGroup.IsPOmegaMinus (N ⧸ center N) r q)) := by
  obtain ⟨H, hH, hfin, N, hn, hqs, ρ, hfit, hf, hirr, hn_irr, hff, ⟨e⟩⟩ :=
    exists_binary_supplement σ hk hi hff
  refine ⟨H, hH, hfin, N, hn, hqs, ρ, hfit, hf, hirr, hn_irr, hff, ?_⟩
  rcases hm with ⟨hp, hm⟩ | ⟨hp, hm⟩ | ⟨hp, hm⟩
  · exact Or.inl ⟨hp, hm.of_mulEquiv e.symm⟩
  · exact Or.inr (Or.inl ⟨hp, hm.of_mulEquiv e.symm⟩)
  · exact Or.inr (Or.inr ⟨hp, hm.of_mulEquiv e.symm⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The component itself has an absolutely irreducible realization over its
own commuting field. Its absolute degree bounds the original binary module
size. This scalar change is independent of the supplement's scalar change. -/
theorem exists_absolute_component (hk : σ.ker ≤ center L) (hi : σ.IsIrreducible) :
    ∃ (E : Type v) (_ : Field E) (_ : Finite E) (_ : CharP E 2)
      (_ : Module E W) (_ : FiniteDimensional E W)
      (ρ : Representation E (actionImage σ) W),
      Function.Injective ρ ∧ ρ.IsAbsolutelyIrreducible ∧
      Nonempty (L ⧸ center L ≃* actionImage σ ⧸ center (actionImage σ)) ∧
      2 ^ Module.finrank E W ≤ Nat.card W := by
  let τ := imageRepresentation σ
  let : τ.IsIrreducible := imageRepresentation_isIrreducible σ hi
  let E := Module.End (ZMod 2)[actionImage σ] τ.asModule
  let : CharP E 2 := endFieldRep_charTwo τ
  let : Module E W := endFieldModule τ
  let : FiniteDimensional E W := endFieldRep_finiteDimensional τ
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    τ.endFieldRep, endFieldRep_injective τ (imageRepresentation_injective σ),
    endFieldRep_isAbsolutelyIrreducible τ,
    ⟨actionImage_quotientCenterEquiv σ hk⟩, two_pow_endField_finrank_le_card τ⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.OrthogonalParameters
