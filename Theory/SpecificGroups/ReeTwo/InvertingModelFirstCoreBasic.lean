module

public import Theory.SpecificGroups.ReeTwo.InvertingActionCensus
public import Theory.SpecificGroups.ReeTwo.CyclicFourCentralExtensionTransport
public import Theory.GroupTheory.UpperCentralSeriesCentralizerTransport

/-!
# The marked intrinsic first cores of the census models

The embedded last root is central because it is central in the core and is
fixed by every core automorphism. It thus belongs to the centralizer of the
second upper central term. Marked ambient isomorphisms transfer its fixed-point
property for automorphisms of this intrinsic subgroup.

Source: the Shinoda core coordinates and the cyclic carry model, together with
the functoriality of the upper central series. This module is independent of
`InvertingExtensionFirstCore`, which assembles the arbitrary-extension result.
-/

@[expose] public section
namespace ReeTwo.InvertingModel
open Core.InvertingActionCensus CyclicFourCentralExtension

/-- A census action with either marked fourth power. -/
abbrev Model (i : Fin 20) (ε : Bool) :=
  CyclicFourCentralExtension.Model (representative i) (representative_four i) ε

/-- The intrinsic first core of a census model. -/
def firstCore (i : Fin 20) (ε : Bool) : Subgroup (Model i ε) :=
  Subgroup.centralizer (Subgroup.upperCentralSeries (Model i ε) 2 : Set (Model i ε))

/-- The embedded last root. -/
def mark (i : Fin 20) (ε : Bool) : Model i ε := embed (Core.root 9)

/-- The last root is central for every action and either fourth power. -/
theorem mark_mem_center (i : Fin 20) (ε : Bool) :
    mark i ε ∈ Subgroup.center (Model i ε) := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply mul_inv_eq_iff_eq_mul.mp
  change x * embed (Core.root 9) * x⁻¹ = embed (Core.root 9)
  rw [conj_embed, Core.aut_root_nine]
  have h := Subgroup.mem_center_iff.mp Core.root_nine_mem_center x.core
  rw [h, mul_inv_cancel_right]

/-- Membership in the intrinsic subgroup, uniformly in all forty models. -/
theorem mark_mem_firstCore (i : Fin 20) (ε : Bool) : mark i ε ∈ firstCore i ε :=
  Subgroup.center_le_centralizer _ (mark_mem_center i ε)

/-- The marked subgroup element with canonical membership proof. -/
def centralInvolution (i : Fin 20) (ε : Bool) : firstCore i ε :=
  ⟨mark i ε, mark_mem_firstCore i ε⟩

theorem centralInvolution_mem_center (i : Fin 20) (ε : Bool) :
    centralInvolution i ε ∈ Subgroup.center (firstCore i ε) := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (mark_mem_center i ε) x.val

theorem centralInvolution_ne_one (i : Fin 20) (ε : Bool) : centralInvolution i ε ≠ 1 := by
  intro h
  have he := congrArg (fun x : firstCore i ε => x.val.core) h
  exact (by decide +kernel : Core.root 9 ≠ 1) he

/-- Transfer the fixed mark along a marked ambient isomorphism. -/
theorem fixed_of_marked_equiv {i j : Fin 20} {ε η : Bool}
    (e : Model i ε ≃* Model j η) (he : e (mark i ε) = mark j η)
    (hfixed : ∀ a : MulAut (firstCore j η),
      a (centralInvolution j η) = centralInvolution j η)
    (a : MulAut (firstCore i ε)) : a (centralInvolution i ε) = centralInvolution i ε := by
  let f : firstCore i ε ≃* firstCore j η :=
    Subgroup.centralizerUpperCentralSeriesEquiv e 2
  have hx : f (centralInvolution i ε) = centralInvolution j η := Subtype.ext he
  apply f.injective
  have hf := hfixed (f.symm.trans (a.trans f))
  rw [← hx] at hf
  change f (a (f.symm (f (centralInvolution i ε)))) = f (centralInvolution i ε) at hf
  simpa only [f.symm_apply_apply] using hf

/-- The membership proof can be arbitrary in the fixed-point conclusion. -/
theorem fixed_all_membership_proofs {i : Fin 20} {ε : Bool}
    (hfixed : ∀ a : MulAut (firstCore i ε), a (centralInvolution i ε) = centralInvolution i ε)
    (hz : mark i ε ∈ firstCore i ε) (a : MulAut (firstCore i ε)) :
    a ⟨mark i ε, hz⟩ = ⟨mark i ε, hz⟩ := hfixed a

end ReeTwo.InvertingModel
