module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionQuotientTransfer
public import Mathlib.RepresentationTheory.Semisimple

/-!
# The two-term local filtration in the binary exhaustion branch

A module spanned by the two component types maps nontrivially onto an image
only if one simple constituent maps nontrivially. The two-group quotient of
the local actor then extends that map to an embedding of the exchanged pair.
Consequently a second copy fills U/W: otherwise the next quotient supplies
a third copy, contradicting the original actor's checked ratio budget.
Component semisimplicity splits the resulting filtration into two copies.

The actual Chapter12 application is SeedAlternativesMovedExhaustionBinaryMultiplicity.
The centralizer calculation and final U = W / Source325 assembly remain with
qt-baumann-fsu. No splitting for the full local actor is asserted.
Source: Aschbacher--Smith D.3.9(1), printed pp.199--200, used in D.3.13 and
3.2.5, pp.202,580; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H E F X : Type*} [Group H]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

/-- Every nonzero image of a module spanned by the two component types contains
an actual copy of the exchanged simple ambient module. -/
theorem embedding_of_two_type_span
    (K : Subgroup H) [K.Normal] (hQ : IsPGroup 2 (H ⧸ K))
    (τ : Representation (ZMod 2) H E) [IsIrreducible τ]
    (ρ : Representation (ZMod 2) H F) (σ : Representation (ZMod 2) H X)
    (I J : Subrepresentation (τ.comp K.subtype))
    (hi : IsIrreducible I.toRepresentation) (hj : IsIrreducible J.toRepresentation)
    (hc : IsCompl I.toSubmodule J.toSubmodule)
    {ι : Type*} (R : ι → Subrepresentation (ρ.comp K.subtype))
    (hspan : (⨆ a, (R a).toSubmodule) = ⊤)
    (htypes : ∀ a, Nonempty (I.toRepresentation.Equiv (R a).toRepresentation) ∨
      Nonempty (J.toRepresentation.Equiv (R a).toRepresentation))
    (q : ρ.IntertwiningMap σ) (hq : q ≠ 0) :
    ∃ i : τ.IntertwiningMap σ, Function.Injective i := by
  let r (a : ι) : (R a).toRepresentation.IntertwiningMap (σ.comp K.subtype) := {
    toLinearMap := q.toLinearMap.comp (R a).toSubmodule.subtype
    isIntertwining' k := by ext v; exact LinearMap.congr_fun (q.isIntertwining' k.val) v.val }
  have hex : ∃ a, r a ≠ 0 := by
    by_contra! hz
    have hh : (⊤ : Submodule (ZMod 2) F) ≤ q.toLinearMap.ker := by
      rw [←hspan]
      refine iSup_le fun a v hv => ?_
      exact congrArg (fun f : (R a).toRepresentation.IntertwiningMap (σ.comp K.subtype) =>
        f ⟨v,hv⟩) (hz a)
    apply hq
    ext v
    exact hh (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) F))
  obtain ⟨a,ha⟩ := hex
  have step (B C : Subrepresentation (τ.comp K.subtype))
      (hB : IsIrreducible B.toRepresentation)
      (hBC : IsCompl B.toSubmodule C.toSubmodule)
      (e : B.toRepresentation.Equiv (R a).toRepresentation) :
      ∃ i : τ.IntertwiningMap σ, Function.Injective i := by
    let := hB
    let : Nontrivial B.toSubmodule := Subrepresentation.irreducible_module_nontrivial B.toRepresentation
    let f := (r a).comp e.toIntertwiningMap
    have hf : f ≠ 0 := by
      intro hz
      apply ha
      ext v
      obtain ⟨w,rfl⟩ := e.surjective v
      exact congrArg (fun f : B.toRepresentation.IntertwiningMap (σ.comp K.subtype) => f w) hz
    exact embedding_of_two_quotient_of_summand K hQ τ σ B C hBC f
      ((IsIrreducible.injective_or_eq_zero f).resolve_right hf)
  rcases htypes a with he | he
  · obtain ⟨e⟩ := he
    exact step I J hi hc e
  · obtain ⟨e⟩ := he
    exact step J I hj hc.symm e

/-- An injective intertwiner identifies its actual range as a subrepresentation. -/
def equivRangeOfInjective (τ : Representation (ZMod 2) H E)
    (σ : Representation (ZMod 2) H X) (i : τ.IntertwiningMap σ)
    (hi : Function.Injective i) : τ.Equiv i.range.toRepresentation :=
  .mk (LinearEquiv.ofInjective i.toLinearMap hi) (by
    intro g
    ext v
    exact LinearMap.congr_fun (i.isIntertwining' g) v)

/-- A second local copy fills the quotient as soon as every further nonzero
quotient contains another copy and three successive copies are excluded. -/
theorem quotient_equiv_of_no_three_sections
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (S : Subrepresentation ρ)
    (i : S.toRepresentation.IntertwiningMap S.quotientRepresentation)
    (hi : Function.Injective i)
    (hnext : ∀ B : Subrepresentation S.quotientRepresentation, B ≠ ⊤ →
      ∃ j : S.toRepresentation.IntertwiningMap B.quotientRepresentation, Function.Injective j)
    (hno : ∀ (B : Subrepresentation S.quotientRepresentation)
      (C : Subrepresentation B.quotientRepresentation),
      ¬ (Nonempty (S.toRepresentation.Equiv B.toRepresentation) ∧
        Nonempty (S.toRepresentation.Equiv C.toRepresentation))) :
    Nonempty (S.toRepresentation.Equiv S.quotientRepresentation) := by
  have ht : i.range = ⊤ := by
    by_contra hn
    obtain ⟨j,hj⟩ := hnext i.range hn
    exact hno i.range j.range ⟨⟨equivRangeOfInjective _ _ i hi⟩,
      ⟨equivRangeOfInjective _ _ j hj⟩⟩
  refine ⟨i.ofBijective ⟨hi,?_⟩⟩
  intro v
  have hv : v ∈ i.range := ht ▸ (show v ∈ (⊤ : Subrepresentation S.quotientRepresentation) from trivial)
  exact hv


/-- Component semisimplicity splits the two-term filtration into two copies
of its original section, preserving the component action. -/
theorem split_double_of_quotient_equiv
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (S : Subrepresentation ρ)
    (hs : Representation.IsSemisimpleRepresentation ρ)
    (e : S.toRepresentation.Equiv S.quotientRepresentation) :
    Nonempty (ρ.Equiv (S.toRepresentation.prod S.toRepresentation)) := by
  let := hs
  obtain ⟨B,hB⟩ := exists_isCompl S
  have hc : IsCompl S.toSubmodule B.toSubmodule := by
    constructor
    · exact disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hB.inf_eq_bot)
    · exact codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hB.sup_eq_top)
  let a : (S.toRepresentation.prod B.toRepresentation).Equiv ρ :=
    .mk (S.toSubmodule.prodEquivOfIsCompl B.toSubmodule hc) (by
      intro g
      apply LinearMap.ext
      intro v
      exact (map_add (ρ g) v.1.val v.2.val).symm)
  let b : B.toRepresentation.Equiv S.quotientRepresentation :=
    .mk (S.toSubmodule.quotientEquivOfIsCompl B.toSubmodule hc).symm (by
      intro g
      rfl)
  let c := b.trans e.symm
  let d : (S.toRepresentation.prod B.toRepresentation).Equiv
      (S.toRepresentation.prod S.toRepresentation) :=
    .mk ((LinearEquiv.refl (ZMod 2) S.toSubmodule).prodCongr c.toLinearEquiv) (by
      intro g
      apply LinearMap.ext
      intro v
      exact Prod.ext rfl (LinearMap.congr_fun (c.isIntertwining' g) v.2))
  exact ⟨a.symm.trans d⟩

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
