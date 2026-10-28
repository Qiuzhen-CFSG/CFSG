module

public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even.Displacement

/-!
# Point-stabilizer normalization for even-degree natural modules

For the binary natural modules of A₆ and A₈, every cocycle restricts to a
principal cocycle on each point stabilizer. The natural module is the image
of the augmentation kernel modulo the constant line, with its actual
coordinate-permutation action.

Extension by zero identifies the augmentation kernel on the complement of
the fixed point with the natural module. Injectivity follows because a
constant vector vanishing at that point is zero. For surjectivity, subtract
the base coordinate times the all-one vector from an even core representative.
Extension by zero intertwines the complement action with the ambient action.
Transporting the restricted cocycle across this equivalence reduces the
claim to the proved odd-degree core result, in degree five or seven.

This is the point-stabilizer normalization step for Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
Lemma I.1.6(1), printed p.408 (PDF p.419); the natural module is defined in
§B.3, printed p.83. The full dimension-one conclusion is assembled separately.
-/

@[expose] public section

open Representation Representation.OneCohomology
open Equiv Equiv.Perm
namespace BinaryPermutation

variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] (b : Ω)

private abbrev pointComplement := Finset.univ.erase b

private def extendZero : Full (pointComplement Ω b) →ₗ[ZMod 2] Full Ω where
  toFun w i := if hi : i ∈ pointComplement Ω b then w ⟨i, hi⟩ else 0
  map_add' w z := by
    funext i
    by_cases hi : i ∈ pointComplement Ω b <;>
      simp only [Pi.add_apply, hi, ↓reduceDIte, add_zero]
  map_smul' a w := by
    funext i
    by_cases hi : i ∈ pointComplement Ω b <;>
      simp only [Pi.smul_apply, hi, ↓reduceDIte, smul_zero, RingHom.id_apply]

private theorem extendZero_at_base (w : Full (pointComplement Ω b)) :
    extendZero Ω b w b = 0 := by
  simp [extendZero, pointComplement]

private theorem extendZero_at_complement (w : Full (pointComplement Ω b))
    (i : pointComplement Ω b) : extendZero Ω b w i.val = w i := by
  change (if hi : i.val ∈ pointComplement Ω b then w ⟨i.val, hi⟩ else 0) = w i
  rw [dif_pos i.property]

private theorem augmentation_extendZero (w : Full (pointComplement Ω b)) :
    augmentation Ω (extendZero Ω b w) = augmentation (pointComplement Ω b) w := by
  change ∑ i, extendZero Ω b w i = ∑ i, w i
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b), extendZero_at_base, add_zero]
  rw [← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl (fun i _ => extendZero_at_complement Ω b w i)

private def extendCore : core (pointComplement Ω b) →ₗ[ZMod 2] core Ω :=
  ((extendZero Ω b).comp (core (pointComplement Ω b)).subtype).codRestrict (core Ω)
    (fun w => by
      change augmentation Ω (extendZero Ω b w) = 0
      rw [augmentation_extendZero]
      exact w.property)

private def complementToNatural : core (pointComplement Ω b) →ₗ[ZMod 2] natural Ω :=
  (coreToNatural Ω).comp (extendCore Ω b)

private theorem complementToNatural_injective :
    Function.Injective (complementToNatural Ω b) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have hc : extendZero Ω b w ∈ constants Ω :=
    (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hw)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  have hz : c = 0 := by
    have h := congrFun hc b
    simpa only [Pi.smul_apply, allOne, smul_eq_mul, mul_one, extendZero_at_base] using h
  subst c
  have hzero : extendZero Ω b w = 0 := by simpa only [zero_smul] using hc.symm
  apply Subtype.ext
  funext i
  change w.val i = 0
  have hi := congrFun hzero i.val
  simpa only [extendZero_at_complement, Pi.zero_apply] using hi

private theorem complementToNatural_surjective (heven : Even (Fintype.card Ω)) :
    Function.Surjective (complementToNatural Ω b) := by
  intro v
  obtain ⟨u, hu, huv⟩ := v.property
  let u' : Full Ω := u - u b • allOne Ω
  have hc : u b • allOne Ω ∈ constants Ω :=
    (constants Ω).smul_mem _ (Submodule.subset_span (by simp))
  have hu' : u' ∈ core Ω :=
    (core Ω).sub_mem hu ((constants_le_core_iff Ω).mpr heven hc)
  have hb : u' b = 0 := by simp [u', allOne]
  let w : core (pointComplement Ω b) := ⟨fun i => u' i.val, by
    change ∑ i : pointComplement Ω b, u' i.val = 0
    rw [Finset.sum_coe_sort]
    have hsum := Finset.sum_erase_add Finset.univ u' (Finset.mem_univ b)
    rw [hb, add_zero] at hsum
    exact hsum.trans hu'⟩
  have hw : extendZero Ω b w = u' := by
    funext i
    by_cases hi : i = b
    · subst i
      rw [extendZero_at_base, hb]
    · exact extendZero_at_complement Ω b w ⟨i, by simp [pointComplement, hi]⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change (constants Ω).mkQ (extendZero Ω b w) = v.val
  rw [hw]
  change (constants Ω).mkQ (u - u b • allOne Ω) = v.val
  have hc0 : (constants Ω).mkQ (u b • allOne Ω) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hc
  rw [map_sub, hc0, sub_zero]
  exact huv

private theorem extendZero_equivariant (g : Equiv.Perm (pointComplement Ω b))
    (w : Full (pointComplement Ω b)) :
    extendZero Ω b (representation (pointComplement Ω b) g w) =
      representation Ω (Equiv.Perm.ofSubtype g) (extendZero Ω b w) := by
  funext i
  change extendZero Ω b (representation (pointComplement Ω b) g w) i =
    extendZero Ω b w ((Equiv.Perm.ofSubtype g).symm i)
  rw [← Equiv.Perm.inv_def, ← map_inv]
  by_cases hi : i ∈ pointComplement Ω b
  · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hi]
    change extendZero Ω b (representation (pointComplement Ω b) g w)
      (⟨i, hi⟩ : pointComplement Ω b).val = _
    rw [extendZero_at_complement, extendZero_at_complement]
    rfl
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hi]
    simp only [extendZero, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi]

private theorem complementToNatural_equivariant
    (g : alternatingGroup (pointComplement Ω b)) (w : core (pointComplement Ω b)) :
    complementToNatural Ω b (alternatingCoreRepresentation (pointComplement Ω b) g w) =
      alternatingNaturalRepresentation Ω (alternatingGroup.ofSubtype (pointComplement Ω b) g)
        (complementToNatural Ω b w) := by
  apply Subtype.ext
  change (constants Ω).mkQ
    (extendZero Ω b (representation (pointComplement Ω b) g.val w)) =
      deletedRepresentation Ω (Equiv.Perm.ofSubtype g.val)
        ((constants Ω).mkQ (extendZero Ω b w))
  rw [deletedRepresentation_mk, extendZero_equivariant]

/-- Every natural-module cocycle is principal on a point stabilizer in degrees six and eight. -/
theorem alternatingNatural_normalize_pointStabilizer (n : ℕ) (hn : n = 6 ∨ n = 8)
    (b : Fin n) (f : cocycles (alternatingNaturalRepresentation (Fin n))) :
    ∃ v : natural (Fin n), ∀ g : alternatingGroup (Fin n),
      g.val b = b → f.val g = alternatingNaturalRepresentation (Fin n) g v - v := by
  let s := pointComplement (Fin n) b
  have heven : Even (Fintype.card (Fin n)) := by
    rcases hn with rfl | rfl <;> decide
  let e : core s ≃ₗ[ZMod 2] natural (Fin n) :=
    LinearEquiv.ofBijective (complementToNatural (Fin n) b)
      ⟨complementToNatural_injective (Fin n) b,
        complementToNatural_surjective (Fin n) b heven⟩
  have he (g : alternatingGroup s) (w : core s) :
      e (alternatingCoreRepresentation s g w) =
        alternatingNaturalRepresentation (Fin n) (alternatingGroup.ofSubtype s g) (e w) :=
    complementToNatural_equivariant (Fin n) b g w
  let F : cocycles (alternatingCoreRepresentation s) :=
    ⟨fun g => e.symm (f.val (alternatingGroup.ofSubtype s g)), by
      intro g h
      apply e.injective
      simp only [map_add, e.apply_symm_apply, he]
      rw [map_mul]
      exact f.property (alternatingGroup.ofSubtype s g) (alternatingGroup.ofSubtype s h)⟩
  have hs : Fintype.card s = n - 1 := by
    simp [s, pointComplement]
  have hs3 : 3 ≤ Nat.card s := by
    rw [Nat.card_eq_fintype_card, hs]
    rcases hn with rfl | rfl <;> decide
  have hsodd : Odd (Fintype.card s) := by
    rw [hs]
    rcases hn with rfl | rfl <;> decide
  obtain ⟨w, hw⟩ := alternatingCore_principal_surjective s hs3 hsodd F
  refine ⟨e w, fun g hg => ?_⟩
  have hgs : g ∈ (alternatingGroup.ofSubtype s).range := by
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    intro j hj
    simp only [s, pointComplement, Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    subst j
    exact Equiv.Perm.mem_support.mp hj hg
  obtain ⟨t, rfl⟩ := hgs
  have ht := congrArg (fun c : cocycles (alternatingCoreRepresentation s) => e (c.val t)) hw
  change e (alternatingCoreRepresentation s t w - w) =
    e (e.symm (f.val (alternatingGroup.ofSubtype s t))) at ht
  rw [map_sub, he, e.apply_symm_apply] at ht
  exact ht.symm

end BinaryPermutation
