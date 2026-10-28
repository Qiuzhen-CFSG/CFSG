module

public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even
public import Theory.Representation.BinaryPermutationNaturalDuality
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Vanishing of first cohomology for the dual augmentation core

The dot product identifies the dual of the binary augmentation core with the
full permutation module modulo constants, with the literal contragredient
coordinate action. In even degree its augmentation is well-defined. Perfectness
forces every alternating-group cocycle into the natural submodule. In degrees
six and eight, point-stabilizer normalization writes that cocycle as a principal
cocycle plus a coordinate displacement. Both are principal in the larger deleted
module, so the first cohomology of the dual core vanishes.

This supplies the action-comparison input for the quartic radical in
Aschbacher–Smith I.2.2(6), printed pp.410 and 412 (combined manuscript of
1 March 2004). The natural-module calculation is I.1.6(1), printed p.408,
and the permutation-module conventions are those of §B.3.
-/

@[expose] public section

open Representation Representation.OneCohomology
namespace BinaryPermutation
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω]

noncomputable def fullCorePairing : Full Ω →ₗ[ZMod 2] Module.Dual (ZMod 2) (core Ω) :=
  (core Ω).dualRestrict.comp (dotProductEquiv (ZMod 2) Ω).toLinearMap

@[simp] theorem fullCorePairing_apply (w : Full Ω) (v : core Ω) :
    fullCorePairing Ω w v = ∑ i, w i * v.val i := rfl

theorem fullCorePairing_ker [Nonempty Ω] : (fullCorePairing Ω).ker = constants Ω := by
  ext w
  constructor
  · intro hw
    let b : Ω := Classical.choice inferInstance
    have hc (i : Ω) : w i = w b := by
      let v : core Ω := ⟨Pi.single i 1 + Pi.single b 1, by
        simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩
      have h := LinearMap.congr_fun hw v
      change dotProduct w (Pi.single i 1 + Pi.single b 1) = 0 at h
      simp only [dotProduct_add, dotProduct_single, mul_one] at h
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
    exact Submodule.mem_span_singleton.mpr ⟨w b, funext fun i => by
      simpa only [Pi.smul_apply, allOne, smul_eq_mul, mul_one] using (hc i).symm⟩
  · intro hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    apply LinearMap.ext
    intro v
    change (∑ i, (c • allOne Ω) i * v.val i) = 0
    simp only [Pi.smul_apply, allOne, smul_eq_mul, mul_one, ← Finset.mul_sum]
    rw [show ∑ i, v.val i = 0 from v.property, mul_zero]

theorem fullCorePairing_surjective : Function.Surjective (fullCorePairing Ω) :=
  Subspace.dualRestrict_surjective.comp (dotProductEquiv (ZMod 2) Ω).surjective

noncomputable def deletedCoreDualEquiv [Nonempty Ω] :
    Deleted Ω ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (core Ω) :=
  (Submodule.quotEquivOfEq (constants Ω) (fullCorePairing Ω).ker
    (fullCorePairing_ker Ω).symm).trans
      ((fullCorePairing Ω).quotKerEquivOfSurjective (fullCorePairing_surjective Ω))

@[simp] theorem deletedCoreDualEquiv_mk [Nonempty Ω] (w : Full Ω) :
    deletedCoreDualEquiv Ω ((constants Ω).mkQ w) = fullCorePairing Ω w := by
  simp [deletedCoreDualEquiv]

theorem deletedCoreDualEquiv_equivariant [Nonempty Ω] (g : Equiv.Perm Ω)
    (v : Deleted Ω) :
    deletedCoreDualEquiv Ω (deletedRepresentation Ω g v) =
      (coreRepresentation Ω).dual g (deletedCoreDualEquiv Ω v) := by
  obtain ⟨w, rfl⟩ := (constants Ω).mkQ_surjective v
  rw [deletedRepresentation_mk, deletedCoreDualEquiv_mk]
  ext u
  change (∑ i, w (g.symm i) * u.val i) = ∑ i, w i * u.val (g i)
  simpa using Equiv.sum_comp g.symm (fun i => w i * u.val (g i))

abbrev alternatingDeletedRepresentation :
    Representation (ZMod 2) (alternatingGroup Ω) (Deleted Ω) :=
  (deletedRepresentation Ω).comp (alternatingGroup Ω).subtype

def deletedAugmentation (heven : Even (Fintype.card Ω)) : Deleted Ω →ₗ[ZMod 2] ZMod 2 :=
  (constants Ω).liftQ (augmentation Ω) ((constants_le_core_iff Ω).mpr heven)

omit [DecidableEq Ω] in
@[simp] theorem deletedAugmentation_mk (heven : Even (Fintype.card Ω)) (w : Full Ω) :
    deletedAugmentation Ω heven ((constants Ω).mkQ w) = augmentation Ω w := rfl

omit [DecidableEq Ω] in
theorem deletedAugmentation_invariant (heven : Even (Fintype.card Ω))
    (g : Equiv.Perm Ω) (v : Deleted Ω) :
    deletedAugmentation Ω heven (deletedRepresentation Ω g v) =
      deletedAugmentation Ω heven v := by
  obtain ⟨w, rfl⟩ := (constants Ω).mkQ_surjective v
  rw [deletedRepresentation_mk, deletedAugmentation_mk, deletedAugmentation_mk,
    augmentation_permute]

omit [DecidableEq Ω] in
theorem mem_natural_iff_deletedAugmentation (heven : Even (Fintype.card Ω))
    (v : Deleted Ω) : v ∈ natural Ω ↔ deletedAugmentation Ω heven v = 0 := by
  obtain ⟨w, rfl⟩ := (constants Ω).mkQ_surjective v
  constructor
  · rintro ⟨u, hu, he⟩
    have h := congrArg (deletedAugmentation Ω heven) he
    rw [deletedAugmentation_mk, deletedAugmentation_mk] at h
    exact h.symm.trans hu
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem deletedCocycle_mem_natural (hcard : 5 ≤ Fintype.card Ω)
    (heven : Even (Fintype.card Ω))
    (f : cocycles (alternatingDeletedRepresentation Ω)) (g : alternatingGroup Ω) :
    f.val g ∈ natural Ω := by
  let p := deletedAugmentation Ω heven
  let χ : alternatingGroup Ω →* Multiplicative (ZMod 2) :=
    { toFun g := Multiplicative.ofAdd (p (f.val g))
      map_one' := by
        have hf := f.property 1 1
        have hz : f.val 1 = 0 := by simpa using hf.symm
        change p (f.val 1) = 0
        rw [hz, map_zero]
      map_mul' g h := by
        change p (f.val (g * h)) = p (f.val g) + p (f.val h)
        rw [f.property, map_add]
        change deletedAugmentation Ω heven (deletedRepresentation Ω g.val (f.val h)) +
          p (f.val g) = _
        rw [deletedAugmentation_invariant]
        exact add_comm _ _ }
  have hg : g ∈ commutator (alternatingGroup Ω) := by
    rw [commutator_alternatingGroup_eq_top (by simpa [Nat.card_eq_fintype_card] using hcard)]
    exact Subgroup.mem_top g
  exact (mem_natural_iff_deletedAugmentation Ω heven _).mpr
    (Abelianization.commutator_subset_ker χ hg)

theorem alternatingDeleted_principal_surjective (n : ℕ) (hn : n = 6 ∨ n = 8) :
    Function.Surjective (principal (alternatingDeletedRepresentation (Fin n))) := by
  let b : Fin n := ⟨0, by omega⟩
  have heven : Even (Fintype.card (Fin n)) := by
    rcases hn with rfl | rfl <;> decide
  intro f
  let F : cocycles (alternatingNaturalRepresentation (Fin n)) :=
    ⟨fun g => ⟨f.val g, deletedCocycle_mem_natural (Fin n) (by simp; omega) heven f g⟩,
      fun g h => Subtype.ext (f.property g h)⟩
  obtain ⟨v, hv⟩ := alternatingNatural_normalize_pointStabilizer n hn b F
  obtain ⟨a, ha⟩ := alternatingNatural_normalized_eq_coordinate n hn b
    (F - principal (alternatingNaturalRepresentation (Fin n)) v) (by
      intro g hg
      change F.val g - (alternatingNaturalRepresentation (Fin n) g v - v) = 0
      rw [hv g hg, sub_self])
  refine ⟨a • (constants (Fin n)).mkQ (Pi.single b 1) + v.val, ?_⟩
  apply Subtype.ext
  funext g
  have h := congrArg (fun c : cocycles (alternatingNaturalRepresentation (Fin n)) =>
    (c.val g).val) ha
  change f.val g - (deletedRepresentation (Fin n) g.val v.val - v.val) =
    a • (constants (Fin n)).mkQ
      (representation (Fin n) g.val (Pi.single b 1) - Pi.single b 1) at h
  change deletedRepresentation (Fin n) g.val
      (a • (constants (Fin n)).mkQ (Pi.single b 1) + v.val) -
    (a • (constants (Fin n)).mkQ (Pi.single b 1) + v.val) = f.val g
  rw [map_add, map_smul, deletedRepresentation_mk]
  rw [map_sub, smul_sub] at h
  have h' := sub_eq_iff_eq_add.mp h
  rw [h']
  abel

theorem alternatingCore_dual_principal_surjective (n : ℕ) (hn : n = 6 ∨ n = 8) :
    Function.Surjective (principal (alternatingCoreRepresentation (Fin n)).dual) := by
  have : NeZero n := ⟨by omega⟩
  let E := deletedCoreDualEquiv (Fin n)
  have he (g : alternatingGroup (Fin n)) (v : Deleted (Fin n)) :
      E (alternatingDeletedRepresentation (Fin n) g v) =
        (alternatingCoreRepresentation (Fin n)).dual g (E v) :=
    deletedCoreDualEquiv_equivariant (Fin n) g.val v
  intro f
  let F : cocycles (alternatingDeletedRepresentation (Fin n)) :=
    ⟨fun g => E.symm (f.val g), by
      intro g h
      apply E.injective
      simp only [map_add, E.apply_symm_apply, he]
      exact f.property g h⟩
  obtain ⟨v, hv⟩ := alternatingDeleted_principal_surjective n hn F
  refine ⟨E v, ?_⟩
  apply Subtype.ext
  funext g
  have h := congrArg (fun c : cocycles (alternatingDeletedRepresentation (Fin n)) =>
    E (c.val g)) hv
  change E (alternatingDeletedRepresentation (Fin n) g v - v) = E (E.symm (f.val g)) at h
  rw [map_sub, he, E.apply_symm_apply] at h
  exact h
end BinaryPermutation
