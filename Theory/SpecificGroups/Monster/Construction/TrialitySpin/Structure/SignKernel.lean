/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Automorphisms

/-!
# The standard-automorphism kernel is the Golay cocode

The perfect cocode pairing gives actual sign-changing loop permutations. The
normal-form correction equation shows that every automorphism in the code
kernel is one of these permutations, uniquely. This constructs a multiplicative
equivalence with the kernel, and proves its order is 4096.
Source: Aschbacher, Lemma 27.1(1), using the concrete cocode of Section 19.

Adapted from Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerStandardKernel.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Changes: CFSG module imports, local triality namespace, Lean 4.33 proof syntax,
and compatibility with the existing concrete `IsStandard` predicate.
-/

@[expose] public section

noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin
open Atlas.Fischer Atlas.Codes

/-- Every actual cocode word acts by its perfect-pairing sign character. -/
def parkerCocodeStandard (d : Cocode) : ParkerStandardGroup :=
  ⟨parkerLoopLift (LinearEquiv.refl Bit golay) (fun a => cocodePairing a d), by
    apply (isStandard_iff _).mpr
    refine ⟨?_,?_,1,?_⟩
    · apply parkerLoopLift_preserves_multiply
      intro a b
      change cocodeDualEquiv d (a+b)+cocodeDualEquiv d a+cocodeDualEquiv d b=
        parkerGolayFactorSet a b+parkerGolayFactorSet a b
      rw [map_add,CharTwo.add_self_eq_zero]
      calc
        _ = (cocodeDualEquiv d a+cocodeDualEquiv d b)+
            (cocodeDualEquiv d a+cocodeDualEquiv d b) := by abel
        _ = 0 := CharTwo.add_self_eq_zero _
    · exact parkerLoopLift_fixes_sign _ _ (map_zero (cocodeDualEquiv d))
    · intro x
      exact (parkerCodeEquiv_one x.1).symm⟩

@[simp] theorem parkerCocodeStandard_apply (d : Cocode) (x : ParkerLoop) :
    (parkerCocodeStandard d).val x=(x.1,x.2+cocodePairing x.1 d) := rfl

@[simp] theorem parkerCocodeStandard_projection (d : Cocode) :
    parkerStandardProjection (parkerCocodeStandard d)=1 := by
  apply parkerCodeEquiv_faithful
  intro a
  exact (parkerStandardProjection_spec (parkerCocodeStandard d) (a,0)).symm.trans
    (parkerCodeEquiv_one a).symm

/-- The cocode embeds as actual sign-changing loop permutations. -/
def parkerCocodeHom : Multiplicative Cocode →* ParkerStandardGroup where
  toFun d := parkerCocodeStandard d.toAdd
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    simp [parkerCocodeStandard_apply,cocodePairing]
  map_mul' d e := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change (x.1,x.2+cocodePairing x.1 (d.toAdd+e.toAdd))=
      ((parkerCocodeStandard d.toAdd).val ((parkerCocodeStandard e.toAdd).val x))
    rw [parkerCocodeStandard_apply,parkerCocodeStandard_apply]
    apply Prod.ext
    · rfl
    · change x.2+cocodePairing x.1 (d.toAdd+e.toAdd)=
        (x.2+cocodePairing x.1 e.toAdd)+cocodePairing x.1 d.toAdd
      simp only [cocodePairing,map_add,LinearMap.add_apply]
      abel

def parkerCocodeKernelHom : Multiplicative Cocode →* parkerStandardProjection.ker where
  toFun d := ⟨parkerCocodeHom d,parkerCocodeStandard_projection d.toAdd⟩
  map_one' := Subtype.ext parkerCocodeHom.map_one
  map_mul' d e := Subtype.ext (parkerCocodeHom.map_mul d e)

theorem parkerCocodeKernelHom_injective : Function.Injective parkerCocodeKernelHom := by
  intro d e h
  apply Multiplicative.toAdd.injective
  apply cocodeDualEquiv.injective
  ext a
  have he := congrArg (fun k : parkerStandardProjection.ker => (k.val.val (a,0)).2) h
  change 0+cocodePairing a d.toAdd=0+cocodePairing a e.toAdd at he
  simpa only [zero_add,cocodePairing] using he

/-- Every standard loop automorphism inducing the identity on the marked
Golay code is exactly the sign action of a unique actual cocode word. -/
theorem parkerCocodeKernelHom_surjective : Function.Surjective parkerCocodeKernelHom := by
  intro e
  let η := parkerPermutationCorrection e.val.val
  have hzero : η 0=0 := parkerPermutationCorrection_zero e.val.val e.val.prop.2.1
  have hcode (x : ParkerLoop) : (e.val.val x).1=x.1 := by
    have h := parkerStandardProjection_spec e.val x
    rw [show parkerStandardProjection e.val=1 from e.prop,parkerCodeEquiv_one] at h
    exact h
  have hη (a b : golay) : η (a+b)+η a+η b=0 := by
    have h := parkerPermutationCorrection_equation e.val.val (LinearEquiv.refl Bit golay)
      e.val.prop.1 e.val.prop.2.1 hcode a b
    simpa only [LinearEquiv.refl_apply,CharTwo.add_self_eq_zero] using h
  let f : golay →+ Bit := {
    toFun := η
    map_zero' := hzero
    map_add' := by
      intro a b
      have h : η (a+b)+(η a+η b)=0 := by simpa only [add_assoc] using hη a b
      exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq _) }
  let l := f.toZModLinearMap 2
  let d := cocodeDualEquiv.symm l
  refine ⟨Multiplicative.ofAdd d,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have he := parkerPermutation_normal_form e.val.val (LinearEquiv.refl Bit golay)
    e.val.prop.1 e.val.prop.2.1 hcode x
  change (parkerCocodeStandard d).val x=e.val.val x
  rw [parkerCocodeStandard_apply,he]
  apply Prod.ext
  · rfl
  · change x.2+cocodePairing x.1 d=x.2+η x.1
    apply congrArg (x.2+·)
    change cocodeDualEquiv (cocodeDualEquiv.symm l) x.1=l x.1
    rw [cocodeDualEquiv.apply_symm_apply]

/-- Exact kernel identification with the actual Golay cocode. -/
def parkerCocodeKernelEquiv : Multiplicative Cocode ≃* parkerStandardProjection.ker :=
  MulEquiv.ofBijective parkerCocodeKernelHom
    ⟨parkerCocodeKernelHom_injective,parkerCocodeKernelHom_surjective⟩

theorem parkerStandardProjection_kernel_card : Nat.card parkerStandardProjection.ker=4096 := by
  rw [← Nat.card_congr parkerCocodeKernelEquiv.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative Cocode ≃ Cocode),cocode_card]


abbrev parkerCocodeEmbedding : Multiplicative Cocode →* ParkerStandardGroup := parkerCocodeHom

@[simp] theorem parkerCocodeEmbedding_apply (d : Multiplicative Cocode) (x : ParkerLoop) :
    (parkerCocodeEmbedding d).val x=(x.1,x.2+cocodePairing x.1 d.toAdd) := rfl

theorem parkerCocodeEmbedding_injective : Function.Injective parkerCocodeEmbedding := by
  intro d e h
  apply parkerCocodeKernelHom_injective
  exact Subtype.ext h

theorem parkerCocodeEmbedding_range : parkerCocodeEmbedding.range=parkerStandardProjection.ker := by
  apply le_antisymm
  · rintro _ ⟨d,rfl⟩
    exact parkerCocodeStandard_projection d.toAdd
  · intro e he
    obtain ⟨d,hd⟩ := parkerCocodeKernelHom_surjective ⟨e,he⟩
    exact ⟨d,congrArg Subtype.val hd⟩

abbrev parkerStandardKernelEquiv : Multiplicative Cocode ≃* parkerStandardProjection.ker :=
  parkerCocodeKernelEquiv

end Sporadic.Monster.Construction.TrialitySpin
