module

public import Theory.Representation.BinaryAlternatingSixPerfectOvergroups.Permutation
public import Theory.LinearAlgebra.BinaryFourAlternatingEight
public import Theory.Representation.BinaryPermutationMulAction
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# Perfect overgroups of the binary natural A₆

The faithful natural action marks an actual subgroup of order 360 in the
multiplicative automorphisms of the binary four-space. The existing exceptional
isomorphism identifies this automorphism group with A₈. Relative indices,
perfectness, and the faithful coset action then leave precisely the marked A₆,
an actual A₇, or the full A₈. No overgroup table or exhaustive matrix search is
assumed. The only finite arithmetic certificate checks the divisors of 56.

This supplies the candidate groups for the M₂₄-code row of Aschbacher–Smith,
Proposition 8.2.8(1), printed p.719/PDF p.736. The exceptional isomorphism is
reused through `BinaryFourAlternatingEight`; its ATLAS attribution and license
are retained in that module and its imports. Representation exclusions are a
separate step in the source application.
-/

public section
namespace BinaryAlternatingSixPerfectOvergroups
open Subgroup

/-- The multiplicative additive group of the natural six-letter binary module. -/
abbrev SixModule := Multiplicative (BinaryPermutation.natural (Fin 6))

/-- The literal image of the marked A₆ action. -/
@[expose] noncomputable def alternatingImage : Subgroup (MulAut SixModule) :=
  (alternatingGroup (Fin 6)).map (BinaryPermutation.naturalMulAction (Fin 6))

private theorem naturalMulAction_injective :
    Function.Injective (BinaryPermutation.naturalMulAction (Fin 6)) := by
  intro g h he
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by simp)
  apply LinearMap.ext
  intro v
  exact congrArg Multiplicative.toAdd
    (MulEquiv.congr_fun he (Multiplicative.ofAdd v))

/-- Faithfulness identifies the marked subgroup with the concrete A₆. -/
noncomputable def alternatingImageEquiv : alternatingGroup (Fin 6) ≃* alternatingImage :=
  (alternatingGroup (Fin 6)).equivMapOfInjective
    (BinaryPermutation.naturalMulAction (Fin 6)) naturalMulAction_injective

theorem alternatingImage_card : Nat.card alternatingImage = 360 := by
  rw [← Nat.card_congr alternatingImageEquiv.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private def linearAutEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    MulAut (Multiplicative V) ≃* (V ≃ₗ[ZMod 2] V) where
  toFun a := { AddEquiv.toMultiplicative.symm a with
    map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm a) }
  invFun a := a.toAddEquiv.toMultiplicative
  left_inv := by intro a; ext; rfl
  right_inv := by intro a; ext; rfl
  map_mul' := by intro a b; ext; rfl

/-- The actual automorphism group of the marked four-space is A₈. -/
noncomputable def automorphismEquivAlternatingEight :
    MulAut SixModule ≃* alternatingGroup (Fin 8) :=
  linearAutEquiv.trans (BinaryFourAlternatingEight.linearEquivAlternatingEight (by
    simpa using BinaryPermutation.finrank_natural_even (Fin 6) (by decide)))

/-- Every perfect overgroup of the literal A₆ image is that image, A₇, or A₈.
The latter alternatives supply genuine multiplicative equivalences. -/
theorem perfect_overgroup_alternatives (H : Subgroup (MulAut SixModule))
    [Group.IsPerfect H] (hAH : alternatingImage ≤ H) :
    H = alternatingImage ∨ Nonempty (H ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 8)) := by
  let e := automorphismEquivAlternatingEight
  let A := alternatingImage.map e.toMonoidHom
  let D := H.map e.toMonoidHom
  let : Group.IsPerfect D := Group.IsPerfect.map _
  have hA : Nat.card A = 360 :=
    (Nat.card_congr (alternatingImage.equivMapOfInjective e.toMonoidHom
      e.injective).toEquiv).symm.trans alternatingImage_card
  rcases permutation_alternatives A D hA (map_mono hAH) with h | h | h
  · exact Or.inl ((map_injective e.injective) h)
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inl ⟨(H.equivMapOfInjective e.toMonoidHom e.injective).trans f⟩)
  · exact Or.inr (Or.inr ⟨(H.equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)⟩)

end BinaryAlternatingSixPerfectOvergroups
