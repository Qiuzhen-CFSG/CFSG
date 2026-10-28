module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.Basic
public import Theory.Representation.GeneralLinearNatural

/-!
# A transvection occupies one natural factor

The actual product action on each natural support is its coordinate action.
Naturality makes that action faithful. If two coordinates of a transvection
were nonidentity, its displacement vector would lie in both independent
supports. Thus exactly one coordinate can be nonidentity, and the
transvection lies in its literal subgroup factor.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.1.8 and the proof of 13.8.5, printed p.947 (PDF p.964).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors
open ChapterB
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E}

theorem product_action_on_support (d : SolvableFFFactors ρ)
    (x : (i : Fin d.count) → d.factor i) (i : Fin d.count)
    (w : subspaceCommutator ρ ⊤ (d.factor i)) :
    ρ (d.productInclusion x) (w : E) = ρ (x i : A) (w : E) := by
  let W := subspaceCommutator ρ ⊤ (d.factor i)
  let ψ := (stabilizerRepresentation ρ W).comp
    ((inclusion (d.offenderSubgroup_le_support_stabilizer i)).comp d.groupProduct.toMonoidHom)
  let χ := ((stabilizerRepresentation ρ W).comp
    (inclusion (d.factor_le_support_stabilizer i i))).comp
      (Pi.evalMonoidHom (fun j => d.factor j) i)
  have he : ψ = χ := by
    apply MonoidHom.pi_ext
    intro j g
    ext v
    change ρ (d.productInclusion (Pi.mulSingle j g)) (v : E) =
      ρ ((Pi.mulSingle (M := fun j => d.factor j) j g i : d.factor i) : A) (v : E)
    rw [d.productInclusion_single]
    by_cases hji : j = i
    · subst j
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hji)]
      simpa using d.factor_fixes_other_support hji g v.property
  exact congrArg (fun f => (f x w : E)) he

theorem factor_support_faithful (d : SolvableFFFactors ρ) (i : Fin d.count)
    (g : d.factor i) (hf : ∀ w : subspaceCommutator ρ ⊤ (d.factor i), ρ (g : A) w = w) :
    g = 1 := by
  apply (d.factorModel i).injective
  apply specialLinearNatural_injective 2
  rw [map_one, map_one]
  apply LinearMap.ext
  intro w
  apply (d.naturalEquiv i).symm.injective
  apply Subtype.ext
  simpa only [LinearEquiv.apply_symm_apply, Module.End.one_apply] using
    (d.naturalEquiv_action i g ((d.naturalEquiv i).symm w)).symm.trans
    (hf ((d.naturalEquiv i).symm w))

/-- A transvection in the offender product belongs to one actual coordinate
factor: two nonidentity coordinates would move vectors on independent supports. -/
theorem transvection_mem_factor (d : SolvableFFFactors ρ) (t : A)
    (ht : IsTransvection ρ t) (hJ : t ∈ offenderSubgroup ρ) :
    ∃ i, t ∈ d.factor i := by
  classical
  let x := d.groupProduct.symm ⟨t, hJ⟩
  have hx : d.productInclusion x = t :=
    congrArg Subtype.val (d.groupProduct.apply_symm_apply ⟨t, hJ⟩)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 1 := by
    by_contra! h
    have he : x = 1 := funext h
    have : t = 1 := by rw [← hx, he, map_one]
    exact ht.ne_one this
  obtain ⟨f, v, _, hv, _, he⟩ := ht
  have hv_mem (j : Fin d.count) (hj : x j ≠ 1) :
      v ∈ subspaceCommutator ρ ⊤ (d.factor j) := by
    obtain ⟨w, hw⟩ : ∃ w : subspaceCommutator ρ ⊤ (d.factor j),
        ρ (x j : A) w ≠ w := by
      by_contra! h
      exact hj (factor_support_faithful d j (x j) h)
    have hmove : ρ t (w : E) ≠ w := by
      rw [← hx, product_action_on_support]
      exact hw
    have hfv : f (w : E) ≠ 0 := by
      intro hz
      exact hmove (by rw [he, hz, zero_smul, add_zero])
    apply (Submodule.smul_mem_iff _ hfv).mp
    have hs := d.factor_preserves_support j (x j) w.property
    rw [← product_action_on_support d x j w, hx, he] at hs
    exact (Submodule.add_mem_iff_right _ w.property).mp hs
  have hcoord : ∀ j, j ≠ i → x j = 1 := by
    intro j hji
    by_contra hj
    exact hv ((Submodule.disjoint_def.mp
      (d.supports_independent.pairwiseDisjoint hji)) _ (hv_mem j hj) (hv_mem i hi))
  have hsingle : x = Pi.mulSingle i (x i) := by
    funext j
    by_cases hji : j = i
    · subst j
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hji, hcoord j hji]
  refine ⟨i, ?_⟩
  rw [← hx, hsingle, d.productInclusion_single]
  exact (x i).property

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors

end
