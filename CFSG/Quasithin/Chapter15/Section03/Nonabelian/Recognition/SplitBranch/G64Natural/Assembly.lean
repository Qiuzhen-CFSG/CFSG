module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.Sieve
public import Theory.Representation.PSL3Two.SurjectiveCoordinates
public import Theory.Representation.BinaryQuadraticConstituent.Faithfulness

/-!
# Lifting the split image recognition to actual natural models

Each constituent image is the natural GL₃(2) action by the G.6.4 sieve. Its
perfectness and the cyclic quotient K⟨v⟩/K force the image of K to be the whole
linear group, giving natural coordinates with a surjective actor map.
These coordinates rule out self-duality without assuming that map injective.
The invariant quadratic form therefore vanishes on each irreducible summand.
Its nondegenerate polar pairing makes both summands faithful, eliminating the
remaining kernels and producing actual K ≃* PSL₃(2) natural-module coordinates.

Every source input is explicit. Neither a recognized group nor faithfulness
of a constituent is an input. Minimality and the at-most-two factor bound are
unnecessary once the supplied nonabelian simple-power decomposition is known.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first split
paragraph of 15.3.58, printed p.1149; the quadratic form is from 15.3.56(1).
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
universe u w
variable {A E : Type u} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- Perfectness makes K surject onto the recognized natural linear image. -/
theorem constituent_natural_cover
    (ρ : Representation (ZMod 2) A E) (K : Subgroup A) [K.Normal] (v : A)
    (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule)
    (hmodel : HasActionModel (imageRepresentation (constituentAction J hv))
      (linearRepresentation 3)) :
    Nonempty (BinaryLinearThree.NaturalCover J.toRepresentation) := by
  obtain ⟨eA, eE, hE⟩ := hmodel
  let := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let : Group.IsPerfect (actionImage (constituentAction J hv)) :=
    Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective
  let f := (actionHom (constituentAction J hv)).comp
    (inclusion (le_sup_left : K ≤ extensionActor K v))
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    change ((actionHom (constituentAction J hv)).comp
      (inclusion (le_sup_left : K ≤ extensionActor K v))).range = ⊤
    rw [MonoidHom.range_comp, inclusion_range]
    apply top_unique
    rw [← Group.IsPerfect.commutator_eq_top]
    exact image_commutator_le K v _ (constituentAction J hv).asGroupHom.rangeRestrict_surjective
  let c : K →* BinaryLinearThree.Group :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp (eA.toMonoidHom.comp f)
  refine ⟨⟨c, (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp
    (eA.surjective.comp hf), eE, ?_⟩⟩
  intro a x
  have hh := hE (f a) x
  change eE (J.toRepresentation a x) = (eA (f a)) (eE x) at hh
  rw [hh]
  change (eA (f a)) (eE x) =
    BinaryLinear.OuterCyclic.slEquivLinear 3
      ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm (eA (f a))) (eE x)
  rw [MulEquiv.apply_symm_apply]

/-- Recognize both original constituents, discharging image recognition,
centralizer transport, and both constituent kernels from the genuine source data. -/
theorem natural_models_of_source_data [Finite A] [Finite E] {κ : GroupClass.{u}}
    (hG64 : G64SourceTheorem κ)
    {S : Type w} [Group S] [IsSimpleGroup S] {n : ℕ}
    (hna : ¬ IsMulCommutative S) (K : Subgroup A) [K.Normal]
    (e : K ≃* (Fin n → S)) (ρ : Representation (ZMod 2) A E)
    (hfaith : Function.Injective ρ) (v : A) (s : ℕ) (hs : 0 < s)
    (p : SplitPair ρ K v s)
    (Q : QuadraticForm (ZMod 2) E) (hQ : ∀ a x, Q (ρ a x) = Q x)
    (hnd : Q.polarBilin.Nondegenerate)
    (T : Sylow 2 A) (ht : v ∈ (center T).map (T : Subgroup A).subtype)
    (hplane : Nat.Coprime 3 (Nat.card (subspaceStabilizer ρ
      (LinearMap.range (ρ v - LinearMap.id)))))
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* A) (hq : Function.Surjective q) (hcover : IsSQTK κ Cover) :
    p.HasNaturalModels := by
  have h₁ := constituent_linear_three hG64 hna K e ρ v T ht
    p.first p.first_invariant p.first_irreducible p.first_displacement
    (by rw [p.first_dimension]; omega) hplane q hq hcover
  have h₂ := constituent_linear_three hG64 hna K e ρ v T ht
    p.second p.second_invariant p.second_irreducible p.second_displacement
    (by rw [p.second_dimension]; omega) hplane q hq hcover
  obtain ⟨m₁⟩ := constituent_natural_cover ρ K v p.first p.first_invariant h₁
  obtain ⟨m₂⟩ := constituent_natural_cover ρ K v p.second p.second_invariant h₂
  have hsing (J : Subrepresentation (ρ.comp K.subtype))
      (hJ : J.toRepresentation.IsIrreducible)
      (hd : 1 < Module.finrank (ZMod 2) J.toSubmodule)
      (m : BinaryLinearThree.NaturalCover J.toRepresentation) :
      ∀ x ∈ J.toSubmodule, Q x = 0 := by
    let := hJ
    have hz := BinaryQuadraticConstituent.quadratic_eq_zero_of_not_self_dual
      J.toRepresentation hd (Q.comp J.toSubmodule.subtype)
      (fun a x => hQ a.val x.val) m.not_self_dual
    intro x hx
    exact congrArg (fun q : QuadraticForm (ZMod 2) J.toSubmodule => q ⟨x, hx⟩) hz
  have hs₁ := hsing p.first p.first_irreducible (by rw [p.first_dimension]; omega) m₁
  have hs₂ := hsing p.second p.second_irreducible (by rw [p.second_dimension]; omega) m₂
  have hf : Function.Injective (ρ.comp K.subtype) := hfaith.comp Subtype.val_injective
  have hf₁ := BinaryQuadraticConstituent.faithful_of_singular_complement
    (ρ.comp K.subtype) hf Q (fun a x => hQ a.val x) p.second p.first
    p.complement.symm hnd hs₂
  have hf₂ := BinaryQuadraticConstituent.faithful_of_singular_complement
    (ρ.comp K.subtype) hf Q (fun a x => hQ a.val x) p.first p.second
    p.complement hnd hs₁
  exact ⟨⟨m₁.toNaturalModel hf₁⟩, ⟨m₂.toNaturalModel hf₂⟩⟩
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
