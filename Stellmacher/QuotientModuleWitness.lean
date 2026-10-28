module
public import Stellmacher.LaterDefs
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Faithful local quotient modules

If a finite subgroup `A` normalizes `V ≤ A`, its conjugation image in
`MulAut V` realizes `A/C_A(V)` together with the action on the original
ambient subgroup `V`. This constructs the quotient-module witness used in
Stellmacher (8.1), journal p.37, without identifying the module with its
image in the quotient (which would collapse it in the abelian case).

The existing subgroup conjugation action provides the homomorphism; its
range restriction is surjective and its kernel is exactly the centralizer.
Conversely, compatibility and the specified kernel make the action of any
such witness faithful. The last theorem supplies the fixing-subgroup form
required by Section 1 for the explicit action instance obtained from the
witness's action homomorphism.
-/

namespace Stellmacher.Later

universe u

/-- The conjugation image realizes the local quotient and its module. -/
public theorem exists_quotientModuleWitness
    {G : Type u} [Group G] [Finite G] (A V : Subgroup G)
    (hVA : V ≤ A) (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    Nonempty (QuotientModuleWitness A
      (A ⊓ Subgroup.centralizer (V : Set G)) V) := by
  let := Subgroup.conjMulDistribMulActionOfLeNormalizer A V hAV
  let f : A →* MulAut V := MulDistribMulAction.toMulAut A V
  let X := f.range
  have hker : f.rangeRestrict.ker =
      (A ⊓ Subgroup.centralizer (V : Set G)).subgroupOf A := by
    rw [MonoidHom.ker_rangeRestrict]
    ext a
    change f a = 1 ↔ (a : G) ∈ A ⊓ Subgroup.centralizer (V : Set G)
    constructor
    · intro ha
      refine ⟨a.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro v hv
      have hfix := MulEquiv.congr_fun ha (⟨v, hv⟩ : V)
      have hval := congrArg Subtype.val hfix
      change (a : G) * v * (a : G)⁻¹ = v at hval
      exact (mul_inv_eq_iff_eq_mul.mp hval).symm
    · intro ha
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      change (a : G) * (v : G) * (a : G)⁻¹ = v
      rw [← Subgroup.mem_centralizer_iff.mp ha.2 v v.property]
      simp
  exact ⟨{
    X := X
    projection := f.rangeRestrict
    surjective := f.rangeRestrict_surjective
    kernel_eq := hker
    module_le := hVA
    action := f.range.subtype
    action_compatible := fun _ _ ↦ rfl }⟩

/-- Every centralizer quotient witness acts injectively by automorphisms. -/
public theorem QuotientModuleWitness.action_injective
    {G : Type u} [Group G] {A V : Subgroup G}
    (w : QuotientModuleWitness A
      (A ⊓ Subgroup.centralizer (V : Set G)) V) :
    Function.Injective w.action := by
  let := w.groupX
  apply (MonoidHom.ker_eq_bot_iff w.action).mp
  apply bot_unique
  intro x hx
  obtain ⟨a, rfl⟩ := w.surjective x
  have ha : a ∈ w.projection.ker := by
    rw [w.kernel_eq]
    refine ⟨a.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    have hfix := MulEquiv.congr_fun hx (⟨v, hv⟩ : V)
    have hval := congrArg Subtype.val hfix
    rw [w.action_compatible] at hval
    exact (mul_inv_eq_iff_eq_mul.mp hval).symm
  exact ha

/-- Faithfulness in the fixing-subgroup formulation used by Section 1. -/
public theorem QuotientModuleWitness.action_faithful
    {G : Type u} [Group G] {A V : Subgroup G}
    (w : QuotientModuleWitness A
      (A ⊓ Subgroup.centralizer (V : Set G)) V) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom V w.action
    fixingSubgroup w.X (Set.univ : Set V) = ⊥ := by
  let := w.groupX
  let := MulDistribMulAction.compHom V w.action
  apply bot_unique
  intro x hx
  apply (w.action_injective)
  rw [map_one]
  apply MulEquiv.ext
  intro v
  rw [mem_fixingSubgroup_iff] at hx
  exact hx v (Set.mem_univ _)

end Stellmacher.Later

