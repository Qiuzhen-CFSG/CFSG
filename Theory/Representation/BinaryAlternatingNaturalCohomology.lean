module

public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# First cohomology of odd-degree binary alternating natural modules

The natural module is exactly the image of the augmentation kernel in the
quotient of the permutation module by its constant line, as in `BinaryPermutation`.
The representations below restrict this construction to the alternating group.

Every cocycle on the full permutation module is principal: evaluation at a
fixed coordinate gives a binary character of its point stabilizer, which
vanishes since the alternating group on the remaining coordinates is generated
by elements of order three. Transitivity then constructs a principal vector.
In odd degree, subtracting its augmentation times the all-one vector places
that vector in the core. The equivariant identification of the core with the
natural module proves vanishing of first cohomology, including degrees 5 and 7.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §B.3 and Lemma I.1.6(1), printed p.408 (citing
Exercise 6.3 of Aschbacher, *Finite Group Theory*, 1986).
-/

@[expose] public section

open Representation Representation.OneCohomology
open Equiv Equiv.Perm

namespace BinaryPermutation
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω]

private theorem alternating_binary_character_eq_one
    (φ : alternatingGroup Ω →* Multiplicative (ZMod 2)) (g : alternatingGroup Ω) :
    φ g = 1 := by
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

-- The stabilizer character vanishes because its domain is an alternating group
-- on the complement of the base point.
private theorem cocycle_apply_of_fixed (f : cocycles (alternatingRepresentation Ω))
    (i : Ω) (g : alternatingGroup Ω) (hg : g.val i = i) : f.val g i = 0 := by
  let s := Finset.univ.erase i
  have hinv (t : alternatingGroup s) :
      ((alternatingGroup.ofSubtype s t).val).symm i = i := by
    change (Equiv.Perm.ofSubtype t.val).symm i = i
    rw [← Equiv.Perm.inv_def, ← map_inv]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp [s])
  let φ : alternatingGroup s →* Multiplicative (ZMod 2) :=
    { toFun := fun t => Multiplicative.ofAdd (f.val (alternatingGroup.ofSubtype s t) i)
      map_one' := by
        have hf := congrFun (f.property 1 1) i
        simpa using hf.symm
      map_mul' := fun t u => by
        change f.val (alternatingGroup.ofSubtype s (t * u)) i =
          f.val (alternatingGroup.ofSubtype s t) i + f.val (alternatingGroup.ofSubtype s u) i
        rw [map_mul, f.property]
        change f.val (alternatingGroup.ofSubtype s u)
          (((alternatingGroup.ofSubtype s t).val).symm i) + _ = _
        rw [hinv, add_comm] }
  have hgs : g ∈ (alternatingGroup.ofSubtype s).range := by
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    intro j hj
    simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    subst j
    exact Equiv.Perm.mem_support.mp hj hg
  obtain ⟨t, rfl⟩ := hgs
  exact congrArg Multiplicative.toAdd (alternating_binary_character_eq_one s φ t)

private theorem cocycle_apply_eq_of_inv_apply_eq (f : cocycles (alternatingRepresentation Ω))
    (i : Ω) (g h : alternatingGroup Ω) (heq : g.val.symm i = h.val.symm i) :
    f.val g i = f.val h i := by
  have hfix : (g * h⁻¹).val i = i := by
    change g.val (h.val.symm i) = i
    rw [← heq, Equiv.apply_symm_apply]
  have hfix' : (g * h⁻¹).val.symm i = i := by
    exact (Equiv.symm_apply_eq _).mpr hfix.symm
  have hc := congrFun (f.property (g * h⁻¹) h) i
  change f.val ((g * h⁻¹) * h) i = f.val h ((g * h⁻¹).val.symm i) +
    f.val (g * h⁻¹) i at hc
  simpa only [inv_mul_cancel_right, hfix', cocycle_apply_of_fixed Ω f i _ hfix,
    add_zero] using hc

/-- Every binary alternating permutation-module cocycle is principal. -/
theorem alternating_principal_surjective (hcard : 3 ≤ Nat.card Ω) :
    Function.Surjective (principal (alternatingRepresentation Ω)) := by
  classical
  let : MulAction.IsPretransitive (alternatingGroup Ω) Ω :=
    alternatingGroup.isPretransitive_of_three_le_card Ω hcard
  have : Nonempty Ω := Finite.card_pos_iff.mp (by omega)
  let b : Ω := Classical.choice inferInstance
  have hex (i : Ω) : ∃ t : alternatingGroup Ω, t.val i = b :=
    MulAction.exists_smul_eq (alternatingGroup Ω) i b
  choose t ht using hex
  have hti (i : Ω) : (t i).val.symm b = i := (Equiv.symm_apply_eq _).mpr (ht i).symm
  intro f
  refine ⟨fun i => f.val (t i) b, ?_⟩
  apply Subtype.ext
  funext g i
  change f.val (t (g.val.symm i)) b - f.val (t i) b = f.val g i
  have hc := congrFun (f.property (t i) g) b
  change f.val (t i * g) b = f.val g ((t i).val.symm b) + f.val (t i) b at hc
  rw [hti] at hc
  have heq : (t i * g).val.symm b = (t (g.val.symm i)).val.symm b := by
    change g.val.symm ((t i).val.symm b) = _
    rw [hti, hti]
  rw [cocycle_apply_eq_of_inv_apply_eq Ω f b _ _ heq] at hc
  exact sub_eq_iff_eq_add.mpr hc

/-- In odd degree the principal vector can be chosen in the augmentation kernel. -/
theorem alternatingCore_principal_surjective (hcard : 3 ≤ Nat.card Ω)
    (hodd : Odd (Fintype.card Ω)) :
    Function.Surjective (principal (alternatingCoreRepresentation Ω)) := by
  intro f
  let F : cocycles (alternatingRepresentation Ω) :=
    ⟨fun g => (f.val g : Full Ω), fun g h => by
      exact congrArg Subtype.val (f.property g h)⟩
  obtain ⟨w, hw⟩ := alternating_principal_surjective Ω hcard F
  have hone : augmentation Ω (allOne Ω) = 1 := by
    rw [augmentation_allOne, hodd.natCast_zmod_two]
  let v : core Ω := ⟨w - augmentation Ω w • allOne Ω, by
    change augmentation Ω _ = 0
    simp [hone]⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  funext g
  apply Subtype.ext
  have he := congrArg (fun c : cocycles (alternatingRepresentation Ω) => c.val g) hw
  change representation Ω g.val w - w = (f.val g : Full Ω) at he
  change representation Ω g.val (w - augmentation Ω w • allOne Ω) -
    (w - augmentation Ω w • allOne Ω) = (f.val g : Full Ω)
  rw [map_sub, map_smul, permute_allOne, ← he]
  abel

/-- First cohomology of the odd-degree augmentation kernel vanishes. -/
theorem alternatingCore_subsingleton_H1 (hcard : 3 ≤ Nat.card Ω)
    (hodd : Odd (Fintype.card Ω)) :
    Subsingleton (H1 (alternatingCoreRepresentation Ω)) :=
  Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr
    (alternatingCore_principal_surjective Ω hcard hodd))

/-- First cohomology of the odd-degree natural alternating module vanishes. -/
theorem alternatingNatural_finrank_H1_eq_zero_of_odd (hcard : 3 ≤ Nat.card Ω)
    (hodd : Odd (Fintype.card Ω)) :
    Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation Ω)) = 0 := by
  let e := H1Congr (alternatingCoreRepresentation Ω) (alternatingNaturalRepresentation Ω)
    (MulEquiv.refl _) (coreEquivNatural Ω hodd)
    (fun g v => coreEquivNatural_equivariant Ω hodd g.val v)
  rw [← e.finrank_eq]
  let := alternatingCore_subsingleton_H1 Ω hcard hodd
  exact Module.finrank_zero_of_subsingleton

/-- The degree-five vanishing assertion of Aschbacher–Smith I.1.6(1). -/
theorem alternatingFive_natural_finrank_H1 :
    Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation (Fin 5))) = 0 := by
  apply alternatingNatural_finrank_H1_eq_zero_of_odd
  · simp
  · decide

/-- The degree-seven vanishing assertion of Aschbacher–Smith I.1.6(1). -/
theorem alternatingSeven_natural_finrank_H1 :
    Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation (Fin 7))) = 0 := by
  apply alternatingNatural_finrank_H1_eq_zero_of_odd
  · simp
  · decide

end BinaryPermutation
