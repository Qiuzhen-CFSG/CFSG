module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Automorphisms fixing a characteristic subgroup and its quotient

For a finite group G and characteristic p-subgroup C, the kernel of the
combined restriction to C and action on G/C is a p-group. Consequently,
p-group images for both actions force the whole automorphism group to be
a p-group. A convenience corollary assumes the full automorphism groups
of C and G/C are p-groups; the image version allows a smaller quotient
action, such as one fixing a distinguished involution.
If the full automorphism group of C is a p-group, the quotient action
alone has p-group kernel, by taking the preimage of Aut(C) × {1} under
the paired action.

An automorphism f in the combined kernel defines the displacement function
x ↦ x⁻¹*f(x) into C. Since f fixes C pointwise, displacement sends composition
to pointwise multiplication and embeds the kernel into G → C. Finiteness
of C supplies a uniform p-power exponent, making this function group and
the kernel p-groups. The usual kernel/image extension argument completes
the reductions. Centrality of C is unnecessary: pointwise fixation is
exactly what the displacement calculation uses.

This is the general automorphism-kernel prerequisite for the central and
characteristic-square subgroup arguments in Alperin–Brauer–Gorenstein,
Chapter II §1 Lemma 3, article p.10. It uses no campaign imports or local
classification hypotheses. The quotient and paired action constructions
have public application lemmas; their implementation bodies stay private.
-/

namespace Subgroup

variable {G : Type*} [Group G] (C : Subgroup G) [C.Characteristic]

/-- The action of automorphisms on the quotient by a characteristic subgroup. -/
public def quotientAut : MulAut G →* MulAut (G ⧸ C) where
  toFun f := QuotientGroup.congr C C f (characteristic_iff_map_eq.mp inferInstance f)
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h x => rfl
  map_mul' f g := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h x => rfl

@[simp] public theorem quotientAut_apply_mk (f : MulAut G) (x : G) :
    quotientAut C f (QuotientGroup.mk' C x) = QuotientGroup.mk' C (f x) := by rfl

/-- The combined restriction and quotient action of the automorphism group. -/
public def automorphismPair : MulAut G →* MulAut C × MulAut (G ⧸ C) :=
  (MulAut.characteristic C).prod (quotientAut C)

@[simp] public theorem automorphismPair_apply (f : MulAut G) :
    automorphismPair C f = (MulAut.characteristic C f, quotientAut C f) := by rfl

private theorem pair_kernel_fixes (f : (automorphismPair C).ker) (x : C) :
    (f : MulAut G) x = x := by
  have h := congrArg Prod.fst f.property
  have hx := DFunLike.congr_fun h x
  exact congrArg Subtype.val hx

private theorem pair_kernel_displacement_mem (f : (automorphismPair C).ker) (x : G) :
    x⁻¹ * (f : MulAut G) x ∈ C := by
  have h := congrArg Prod.snd f.property
  have hx := DFunLike.congr_fun h (QuotientGroup.mk' C x)
  have he : QuotientGroup.mk' C x = QuotientGroup.mk' C ((f : MulAut G) x) := hx.symm
  exact QuotientGroup.eq.mp he

private def pairKernelDisplacement : (automorphismPair C).ker →* (G → C) where
  toFun f x := ⟨x⁻¹ * (f : MulAut G) x, pair_kernel_displacement_mem C f x⟩
  map_one' := by funext x; apply Subtype.ext; simp
  map_mul' f g := by
    funext x
    apply Subtype.ext
    change x⁻¹ * (f : MulAut G) ((g : MulAut G) x) =
      (x⁻¹ * (f : MulAut G) x) * (x⁻¹ * (g : MulAut G) x)
    have hf := pair_kernel_fixes C f
      ⟨x⁻¹ * (g : MulAut G) x, pair_kernel_displacement_mem C g x⟩
    change (f : MulAut G) (x⁻¹ * (g : MulAut G) x) =
      x⁻¹ * (g : MulAut G) x at hf
    rw [map_mul, map_inv] at hf
    calc
      _ = x⁻¹ * ((f : MulAut G) x *
          ((f : MulAut G) x)⁻¹ * (f : MulAut G) ((g : MulAut G) x)) := by simp
      _ = _ := by rw [mul_assoc ((f : MulAut G) x), hf, mul_assoc]

private theorem pairKernelDisplacement_injective :
    Function.Injective (pairKernelDisplacement C) := by
  intro f g h
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  have hx := congrArg Subtype.val (congrFun h x)
  exact mul_left_cancel hx

/-- Automorphisms fixing a characteristic p-subgroup and its quotient form a p-group. -/
public theorem isPGroup_automorphism_pair_kernel [Finite G] {p : ℕ}
    (hC : IsPGroup p C) : IsPGroup p (automorphismPair C).ker := by
  have hfunc : IsPGroup p (G → C) := by
    obtain ⟨k, hk⟩ := hC.exists_card_dvd_pow
    intro f
    refine ⟨k, ?_⟩
    funext x
    exact orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard (f x)).trans hk)
  exact hfunc.of_injective (pairKernelDisplacement C) (pairKernelDisplacement_injective C)

private theorem pgroup_prod {A B : Type*} [Group A] [Group B] {p : ℕ}
    (hA : IsPGroup p A) (hB : IsPGroup p B) : IsPGroup p (A × B) := by
  intro g
  obtain ⟨i, hi⟩ := hA g.1
  obtain ⟨j, hj⟩ := hB g.2
  refine ⟨i + j, Prod.ext ?_ ?_⟩
  · change g.1 ^ (p ^ (i + j)) = 1
    rw [pow_add, pow_mul, hi, one_pow]
  · change g.2 ^ (p ^ (i + j)) = 1
    rw [Nat.add_comm, pow_add, pow_mul, hj, one_pow]

/-- A p-group image of the paired action, together with a p-subgroup C, controls all automorphisms. -/
public theorem isPGroup_mulAut_of_automorphism_pair_range [Finite G] {p : ℕ}
    (hC : IsPGroup p C) (hRange : IsPGroup p (automorphismPair C).range) :
    IsPGroup p (MulAut G) := by
  have ht := hRange.comap_of_ker_isPGroup (automorphismPair C)
    (isPGroup_automorphism_pair_kernel C hC)
  have he : (automorphismPair C).range.comap (automorphismPair C) = ⊤ := by
    ext f
    simp
  rw [he] at ht
  exact ht.of_surjective (⊤ : Subgroup (MulAut G)).subtype (by
    intro f
    exact ⟨⟨f, mem_top f⟩, rfl⟩)

/-- It suffices for the restriction and quotient action images to be p-groups. -/
public theorem isPGroup_mulAut_of_characteristic_action_ranges [Finite G] {p : ℕ}
    (hC : IsPGroup p C) (hRestriction : IsPGroup p (MulAut.characteristic C).range)
    (hQuotient : IsPGroup p (quotientAut C).range) : IsPGroup p (MulAut G) := by
  apply isPGroup_mulAut_of_automorphism_pair_range C hC
  have hp : IsPGroup p ((MulAut.characteristic C).range.prod (quotientAut C).range) :=
    (pgroup_prod hRestriction hQuotient).of_equiv
      ((MulAut.characteristic C).range.prodEquiv (quotientAut C).range).symm
  apply hp.to_le
  rintro f ⟨g, rfl⟩
  exact ⟨⟨g, rfl⟩, ⟨g, rfl⟩⟩

/-- Automorphism groups of a characteristic p-subgroup and its quotient control the ambient group. -/
public theorem isPGroup_mulAut_of_characteristic_subgroup_quotient [Finite G] {p : ℕ}
    (hC : IsPGroup p C) (hRestriction : IsPGroup p (MulAut C))
    (hQuotient : IsPGroup p (MulAut (G ⧸ C))) : IsPGroup p (MulAut G) :=
  isPGroup_mulAut_of_characteristic_action_ranges C hC
    (hRestriction.to_subgroup _) (hQuotient.to_subgroup _)

/-- If the characteristic subgroup and its automorphism group are p-groups,
the kernel of the action on the quotient is a p-group. -/
public theorem isPGroup_quotientAut_kernel_of_mulAut [Finite G] {p : ℕ}
    (hC : IsPGroup p C) (hRestriction : IsPGroup p (MulAut C)) :
    IsPGroup p (quotientAut C).ker := by
  let A : Subgroup (MulAut C) := ⊤
  let B : Subgroup (MulAut (G ⧸ C)) := ⊥
  have hp : IsPGroup p (A.prod B) :=
    (pgroup_prod (hRestriction.to_subgroup A) IsPGroup.of_bot).of_equiv
      (A.prodEquiv B).symm
  have hpre := hp.comap_of_ker_isPGroup (automorphismPair C)
    (isPGroup_automorphism_pair_kernel C hC)
  apply hpre.to_le
  intro f hf
  exact ⟨mem_top _, hf⟩

end Subgroup
