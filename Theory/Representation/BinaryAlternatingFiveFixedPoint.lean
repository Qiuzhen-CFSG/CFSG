module
public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.NormalInvariants
public import Theory.Representation.RepEquiv

/-!
# Recognizing the binary A₅ module from a Borel fixed point

A vector fixed by the point stabilizer gives an equivariant family of five
vectors. Linear combination defines a map from the five-point permutation
module. If the original vector is moved by A₅, this map is nonzero on the
augmentation core. That core is irreducible, so the map is injective; an
irreducible target makes it surjective. Thus a nonzero Borel fixed point in
a nontrivial irreducible binary representation identifies the actual
orthogonal A₅ module, with an explicit intertwining equivalence.

This is the field-four module distinction used in Aschbacher--Smith,
5.1.19, printed pp.643--644, and the exceptional 5.2.3 branch. No dimension
bound, module classification, or chosen-module splitting is assumed.
-/

public noncomputable section
open Representation BinaryPermutation
namespace Representation.BinaryAlternatingFiveFixedPoint
abbrev A5 := alternatingGroup (Fin 5)

private theorem exists_mover (i : Fin 5) : ∃ g : A5, g.val 4 = i := by
  have h : ∀ i : Fin 5, ∃ g : A5, g.val 4 = i := by decide +kernel
  exact h i

private def mover (i : Fin 5) : A5 := (exists_mover i).choose
private theorem mover_apply (i : Fin 5) : (mover i).val 4 = i :=
  (exists_mover i).choose_spec

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) A5 W) (v : W)
  (hv : ∀ b : BinaryPermutation.AlternatingFiveBorel.B, ρ b.val v = v)

private def value (i : Fin 5) : W := ρ (mover i) v

include hv in
private theorem value_equivariant (g : A5) (i : Fin 5) :
    value ρ v (g.val i) = ρ g (value ρ v i) := by
  let b := (mover (g.val i))⁻¹ * g * mover i
  have hb : b ∈ BinaryPermutation.AlternatingFiveBorel.B := by
    change (mover (g.val i)).val.symm (g.val ((mover i).val 4)) = 4
    rw [mover_apply]
    exact (mover (g.val i)).val.symm_apply_eq.mpr (mover_apply (g.val i)).symm
  have hh := congrArg (ρ (mover (g.val i))) (hv ⟨b,hb⟩)
  simp only [b, ← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] at hh
  simpa only [value, map_mul, Module.End.mul_apply] using hh.symm

include hv in
private theorem value_four : value ρ v 4 = v :=
  hv ⟨mover 4, mover_apply 4⟩

private def orbitMap : IntertwiningMap (alternatingCoreRepresentation (Fin 5)) ρ := {
  toLinearMap := {
    toFun := fun a => ∑ i : Fin 5, a.val i • value ρ v i
    map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro a
    change (∑ i : Fin 5, a.val (g.val.symm i) • value ρ v i) =
      ρ g (∑ i : Fin 5, a.val i • value ρ v i)
    rw [map_sum]
    simp only [map_smul, ← value_equivariant ρ v hv]
    exact (Equiv.sum_comp g.val
      (fun i => a.val (g.val.symm i) • value ρ v i)).symm.trans (by simp) }

include hv in
private theorem orbitMap_ne_zero (hmove : ∃ g, ρ g v ≠ v) : orbitMap ρ v hv ≠ 0 := by
  intro hz
  obtain ⟨g,hg⟩ := hmove
  let w : core (Fin 5) := ⟨Pi.single (g.val 4) 1 - Pi.single 4 1, by
    simp [mem_core, Finset.sum_sub_distrib]⟩
  have hh := congrArg
    (fun f : IntertwiningMap (alternatingCoreRepresentation (Fin 5)) ρ => f w) hz
  have he : value ρ v (g.val 4) - value ρ v 4 = 0 := by
    change (∑ i : Fin 5, ((Pi.single (g.val 4) 1 : Fin 5 → ZMod 2) i -
      (Pi.single 4 1 : Fin 5 → ZMod 2) i) • value ρ v i) = 0 at hh
    simpa [sub_smul, Finset.sum_sub_distrib] using hh
  rw [value_equivariant ρ v hv, value_four ρ v hv] at he
  exact hg (sub_eq_zero.mp he)

private def coreNaturalEquiv :
    alternatingCoreRepresentation (Fin 5) ≃ₗ alternatingNaturalRepresentation (Fin 5) :=
  .mk (coreEquivNatural (Fin 5) (by decide)) (by
    intro g
    apply LinearMap.ext
    intro v
    exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val v)

include hv in
/-- A Borel fixed point moved by the group recognizes an irreducible target. -/
theorem equiv_natural_of_borel_fixed [ρ.IsIrreducible]
    (hmove : ∃ g, ρ g v ≠ v) :
    Nonempty (ρ.Equiv (alternatingNaturalRepresentation (Fin 5))) := by
  let : (alternatingCoreRepresentation (Fin 5)).IsIrreducible :=
    coreNaturalEquiv.irreducible_of_euqiv (alternatingNatural_isIrreducible (by decide))
  let f := orbitMap ρ v hv
  have hf : f ≠ 0 := orbitMap_ne_zero ρ v hv hmove
  let e := f.ofBijective ⟨(IsIrreducible.injective_or_eq_zero f).resolve_right hf,
    (IsIrreducible.surjective_or_eq_zero f).resolve_right hf⟩
  exact ⟨e.symm.trans coreNaturalEquiv.toRepresentationEquiv⟩

include hv in
/-- A nonzero Borel fixed point identifies every nontrivial irreducible target. -/
theorem equiv_natural_of_nonzero_borel_fixed [ρ.IsIrreducible]
    (hρ : ρ ≠ 1) (hv0 : v ≠ 0) :
    Nonempty (ρ.Equiv (alternatingNaturalRepresentation (Fin 5))) := by
  apply equiv_natural_of_borel_fixed ρ v hv
  by_contra! hall
  have hn : invariants (ρ.comp (⊤ : Subgroup A5).subtype) ≠ ⊥ := by
    intro hz
    apply hv0
    exact hz.le (fun g => hall g)
  have hk := ρ.le_ker_of_normal_invariants_ne_bot ⊤ hn
  apply hρ
  apply MonoidHom.ext
  intro g
  exact hk (Subgroup.mem_top g)

/-- The recognized representation retains its original action for an arbitrary
point stabilizer; an inner conjugation moves the fixed point to coordinate four. -/
theorem equiv_natural_of_point_fixed [ρ.IsIrreducible]
    (hρ : ρ ≠ 1) (hv0 : v ≠ 0) (i : Fin 5)
    (hi : ∀ g : A5, g.val i = i → ρ g v = v) :
    Nonempty (ρ.Equiv (alternatingNaturalRepresentation (Fin 5))) := by
  let a := mover i
  let w := ρ a⁻¹ v
  have hw : w ≠ 0 := by
    intro hz
    apply hv0
    have hh := congrArg (ρ a) hz
    simpa only [w, ρ.self_inv_apply, map_zero] using hh
  apply equiv_natural_of_nonzero_borel_fixed ρ w _ hρ hw
  intro b
  have hbi : (a * b.val * a⁻¹).val i = i := by
    change a.val (b.val.val (a.val.symm i)) = i
    have hai : a.val.symm i = 4 := a.val.symm_apply_eq.mpr (mover_apply i).symm
    rw [hai, show b.val.val 4 = 4 from b.property]
    exact mover_apply i
  have hh := congrArg (ρ a⁻¹) (hi (a * b.val * a⁻¹) hbi)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left] at hh
  simpa only [w, map_mul, Module.End.mul_apply] using hh

end Representation.BinaryAlternatingFiveFixedPoint
