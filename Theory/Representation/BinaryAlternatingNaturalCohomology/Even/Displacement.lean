module

public import Theory.Representation.BinaryAlternatingNaturalCohomology
import Mathlib.Tactic.Abel

/-!
# Nonzero even-degree natural-module cohomology classes

Displacing any full permutation vector gives a cocycle valued in the natural
section. In even degree this cocycle is principal precisely when the vector
has augmentation zero. Thus the displacement of a single-coordinate vector
is nonprincipal, giving the lower bound for the natural modules of A₆ and A₈.

The key kernel calculation uses the absence of binary characters of alternating
groups: if all displacements of a vector are constant, that vector is constant.
The coordinate cocycle vanishes on its point stabilizer, and every full-vector
displacement has its scalar-plus-principal normal form.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §B.3 and Lemma I.1.6(1), printed p.408, citing
Exercise 6.3 of Aschbacher, *Finite Group Theory* (1986).
-/

@[expose] public section

open Representation Representation.OneCohomology
open Equiv Equiv.Perm
namespace BinaryPermutation
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω]

private theorem binary_character (φ : alternatingGroup Ω →* Multiplicative (ZMod 2))
    (g : alternatingGroup Ω) : φ g = 1 := by
  have hker : (⊤ : Subgroup (alternatingGroup Ω)) ≤ φ.ker := by
    rw [← alternatingGroup.closure_isThreeCycles_eq_top, Subgroup.closure_le]
    intro t ht
    have ht3 : t ^ 3 = 1 := by
      apply Subtype.ext
      change (t.val) ^ 3 = 1
      rw [← ht.orderOf]
      exact pow_orderOf_eq_one _
    have h3 : φ t ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
    have h2 : φ t ^ 2 = 1 := by
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd (φ t * φ t) = 0
      exact CharTwo.add_self_eq_zero _
    simpa [pow_succ, h2] using h3
  exact hker (Subgroup.mem_top g)

/-- A vector whose alternating displacements are constant is itself constant. -/
theorem mem_constants_of_alternating_displacement (hcard : 3 ≤ Nat.card Ω)
    (w : Full Ω) (hw : ∀ g : alternatingGroup Ω,
      representation Ω g.val w - w ∈ constants Ω) : w ∈ constants Ω := by
  classical
  have : Nonempty Ω := Finite.card_pos_iff.mp (by omega)
  let b : Ω := Classical.choice inferInstance
  have hconst (g : alternatingGroup Ω) (i : Ω) :
      (representation Ω g.val w - w) i = (representation Ω g.val w - w) b := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hw g)
    rw [← hc]
    rfl
  let φ : alternatingGroup Ω →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd ((representation Ω g.val w - w) b)
      map_one' := by simp
      map_mul' := fun g h => by
        change w ((g * h).val.symm b) - w b =
          (w (g.val.symm b) - w b) + (w (h.val.symm b) - w b)
        have he := hconst h (g.val.symm b)
        change w (h.val.symm (g.val.symm b)) - w (g.val.symm b) =
          w (h.val.symm b) - w b at he
        change w (h.val.symm (g.val.symm b)) - w b = _
        rw [sub_eq_iff_eq_add.mp he]
        abel }
  have hfix (g : alternatingGroup Ω) : representation Ω g.val w = w := by
    funext i
    apply sub_eq_zero.mp
    exact (hconst g i).trans (congrArg Multiplicative.toAdd (binary_character Ω φ g))
  let : MulAction.IsPretransitive (alternatingGroup Ω) Ω :=
    alternatingGroup.isPretransitive_of_three_le_card Ω hcard
  apply Submodule.mem_span_singleton.mpr
  refine ⟨w b, ?_⟩
  funext i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup Ω) i b
  have hi : g.val.symm b = i := (Equiv.symm_apply_eq _).mpr hg.symm
  have he := congrFun (hfix g) b
  simpa [representation_apply, hi, allOne] using he.symm

omit [DecidableEq Ω] in
@[simp] theorem coreToNatural_apply (v : core Ω) :
    (coreToNatural Ω v : Deleted Ω) = (constants Ω).mkQ v := rfl

/-- Displacement of a full permutation vector, valued in the natural section. -/
def naturalDisplacement : Full Ω →ₗ[ZMod 2]
    cocycles (alternatingNaturalRepresentation Ω) where
  toFun w := ⟨fun g => ⟨(constants Ω).mkQ (representation Ω g.val w - w), by
    refine ⟨representation Ω g.val w - w, ?_, rfl⟩
    change augmentation Ω _ = 0
    rw [map_sub, augmentation_permute, sub_self]⟩, by
      intro g h
      apply Subtype.ext
      change (constants Ω).mkQ (representation Ω (g * h).val w - w) =
        deletedRepresentation Ω g.val ((constants Ω).mkQ
          (representation Ω h.val w - w)) +
            (constants Ω).mkQ (representation Ω g.val w - w)
      rw [deletedRepresentation_mk, ← map_add]
      congr 1
      change representation Ω (g.val * h.val) w - w = _
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel⟩
  map_add' x y := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    change (constants Ω).mkQ (representation Ω g.val (x + y) - (x + y)) =
      (constants Ω).mkQ (representation Ω g.val x - x) +
        (constants Ω).mkQ (representation Ω g.val y - y)
    rw [← map_add, map_add]
    congr 1
    abel
  map_smul' a x := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    change (constants Ω).mkQ (representation Ω g.val (a • x) - a • x) =
      a • (constants Ω).mkQ (representation Ω g.val x - x)
    rw [map_smul, ← smul_sub, map_smul]

@[simp] theorem naturalDisplacement_core (v : core Ω) :
    naturalDisplacement Ω v = principal (alternatingNaturalRepresentation Ω)
      (coreToNatural Ω v) := by
  apply Subtype.ext
  funext g
  apply Subtype.ext
  change (constants Ω).mkQ (representation Ω g.val v - v) =
    deletedRepresentation Ω g.val ((constants Ω).mkQ v) - (constants Ω).mkQ v
  rw [deletedRepresentation_mk, map_sub]

theorem naturalDisplacement_eq_zero_iff (hcard : 3 ≤ Nat.card Ω) (w : Full Ω) :
    naturalDisplacement Ω w = 0 ↔ w ∈ constants Ω := by
  constructor
  · intro hw
    apply mem_constants_of_alternating_displacement Ω hcard w
    intro g
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrArg (fun f : cocycles (alternatingNaturalRepresentation Ω) =>
      (f.val g : Deleted Ω)) hw
  · intro hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    apply Subtype.ext
    funext g
    apply Subtype.ext
    change (constants Ω).mkQ (representation Ω g.val (c • allOne Ω) -
      c • allOne Ω) = 0
    rw [map_smul, permute_allOne, sub_self, map_zero]

/-- In even degree a displacement cocycle is principal exactly when its vector
has even augmentation. -/
theorem naturalDisplacement_principal_iff (hcard : 3 ≤ Nat.card Ω)
    (heven : Even (Fintype.card Ω)) (w : Full Ω) :
    (∃ v, principal (alternatingNaturalRepresentation Ω) v = naturalDisplacement Ω w) ↔
      augmentation Ω w = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, hu, huv⟩ := v.property
    let u' : core Ω := ⟨u, hu⟩
    have he : coreToNatural Ω u' = v := Subtype.ext huv
    have hd : naturalDisplacement Ω (w - u) = 0 := by
      rw [map_sub]
      change naturalDisplacement Ω w - naturalDisplacement Ω u' = 0
      rw [naturalDisplacement_core, he, hv]
      exact sub_self (naturalDisplacement Ω w)
    have hc := (constants_le_core_iff Ω).mpr heven
      ((naturalDisplacement_eq_zero_iff Ω hcard _).mp hd)
    change augmentation Ω (w - u) = 0 at hc
    change augmentation Ω u = 0 at hu
    simpa [map_sub, hu] using hc
  · intro hw
    exact ⟨coreToNatural Ω ⟨w, hw⟩, (naturalDisplacement_core Ω ⟨w, hw⟩).symm⟩

/-- A single-coordinate vector defines the nonzero natural-module cohomology class. -/
def naturalCoordinateCocycle (b : Ω) : cocycles (alternatingNaturalRepresentation Ω) :=
  naturalDisplacement Ω (Pi.single b 1)

theorem naturalCoordinateCocycle_not_principal (hcard : 3 ≤ Nat.card Ω)
    (heven : Even (Fintype.card Ω)) (b : Ω) :
    ¬ ∃ v, principal (alternatingNaturalRepresentation Ω) v =
      naturalCoordinateCocycle Ω b := by
  rw [naturalCoordinateCocycle, naturalDisplacement_principal_iff Ω hcard heven]
  simp [augmentation]

theorem alternatingNatural_finrank_H1_pos_of_even (hcard : 3 ≤ Nat.card Ω)
    (heven : Even (Fintype.card Ω)) :
    0 < Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation Ω)) := by
  have : Nonempty Ω := Finite.card_pos_iff.mp (by omega)
  let b : Ω := Classical.choice inferInstance
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨classMap (alternatingNaturalRepresentation Ω) (naturalCoordinateCocycle Ω b), ?_⟩
  rw [ne_eq, classMap_eq_zero_iff]
  exact naturalCoordinateCocycle_not_principal Ω hcard heven b

/-- The distinguished cocycle vanishes on the stabilizer of its base coordinate. -/
theorem naturalCoordinateCocycle_apply_of_fixed (b : Ω) (g : alternatingGroup Ω)
    (hg : g.val b = b) : (naturalCoordinateCocycle Ω b).val g = 0 := by
  have he : representation Ω g.val (Pi.single b 1) = Pi.single b 1 := by
    funext i
    simp [representation_apply, Pi.single_apply, Equiv.symm_apply_eq, hg]
  apply Subtype.ext
  change (constants Ω).mkQ (representation Ω g.val (Pi.single b 1) - Pi.single b 1) = 0
  rw [he, sub_self, map_zero]

/-- Every full-vector displacement has the coordinate-cocycle normal form. -/
theorem naturalDisplacement_normalForm (b : Ω) (w : Full Ω) :
    ∃ v : natural Ω, naturalDisplacement Ω w =
      augmentation Ω w • naturalCoordinateCocycle Ω b +
        principal (alternatingNaturalRepresentation Ω) v := by
  let u : core Ω := ⟨w - augmentation Ω w • Pi.single b 1, by
    change augmentation Ω _ = 0
    simp [augmentation, map_sub, map_smul]⟩
  refine ⟨coreToNatural Ω u, ?_⟩
  rw [← naturalDisplacement_core]
  change naturalDisplacement Ω w =
    augmentation Ω w • naturalDisplacement Ω (Pi.single b 1) + naturalDisplacement Ω u
  rw [← map_smul, ← map_add]
  congr 1
  exact (add_sub_cancel _ _).symm

end BinaryPermutation
