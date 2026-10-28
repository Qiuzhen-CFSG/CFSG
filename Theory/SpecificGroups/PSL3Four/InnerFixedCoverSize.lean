module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.RootCoverage
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Large fixed inner images in central covers of PSL₃(4)

For an inner automorphism of square one, the image under conjugation of its
actual fixed subgroup has order greater than four. This holds for every finite
group whose quotient by its whole center is the actual PSL₃(4) model, including
SL₃(4) and covers with nontrivial two-centers.

Write the actor as conjugation by x. Its square being one says only that x²
is central. In the projective quotient, conjugate the image of x to the
highest-root element with coordinate c. The four unitriangular elements
with coordinates (1,c,i), for i in F₄, are distinct nonidentity square roots
of that element. If y lifts any such square root, then y² and x differ by a
central element, so y centralizes x. Distinct projective elements have distinct
inner images. These four fixed images and the identity prove the strict bound.

This supplies the lifted-fixer bound used in the inner-actor case of
Aschbacher--Smith 15.3.38, printed p.1137 (1 March 2004 manuscript).
The square-root argument works for all central covers directly; the exceptional
multiplier calculations of GLS3 5.5.11, 6.1.4 and 6.3.3 are therefore unnecessary
for this bound. In particular, the projective centralizer order need not be
assumed and the image of the lifted fixer is never equated to that centralizer.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.InnerFixedCoverSize

private theorem conj_kernel {E : Type*} [Group E] :
    (MulAut.conj : E →* MulAut E).ker = center E := by
  ext x
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    have he := MulEquiv.congr_fun hx y
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    ext y
    change x * y * x⁻¹ = y
    rw [← mem_center_iff.mp hx y, mul_inv_cancel_right]

private theorem conj_eq_iff_map_eq {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hk : f.ker = center E) (x y : E) :
    MulAut.conj x = MulAut.conj y ↔ f x = f y := by
  rw [(MulAut.conj : E →* MulAut E).eq_iff, f.eq_iff, conj_kernel, hk]

private theorem card_lt_inner_fixed_image_of_square_roots
    {E B ι : Type*} [Group E] [Finite E] [Group B] [Finite ι]
    (f : E →* B) (hf : Function.Surjective f) (hk : f.ker = center E)
    (x : E) (s : ι → B) (hi : Function.Injective s)
    (hn : ∀ i, s i ≠ 1) (hs : ∀ i, s i ^ 2 = f x) :
    Nat.card ι < Nat.card ((MulAut.conj x).fixedSubgroup.map
      (MulAut.conj : E →* MulAut E)) := by
  classical
  choose l hl using fun i => hf (s i)
  have hfixed (i : ι) : l i ∈ (MulAut.conj x).fixedSubgroup := by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    have he : MulAut.conj (l i ^ 2) = MulAut.conj x :=
      (conj_eq_iff_map_eq f hk _ _).mpr (by rw [map_pow, hl, hs])
    rw [← he, MulAut.conj_apply]
    group
  let C := (MulAut.conj x).fixedSubgroup.map (MulAut.conj : E →* MulAut E)
  let k : ι → C := fun i => ⟨MulAut.conj (l i), mem_map_of_mem _ (hfixed i)⟩
  have hki : Function.Injective k := by
    intro i j hij
    apply hi
    rw [← hl i, ← hl j]
    exact (conj_eq_iff_map_eq f hk _ _).mp (congrArg Subtype.val hij)
  have hkn : ¬ Function.Surjective k := by
    intro h
    obtain ⟨i, hi⟩ := h 1
    have he : MulAut.conj (l i) = MulAut.conj (1 : E) := by
      have he' := congrArg Subtype.val hi
      change MulAut.conj (l i) = 1 at he'
      simpa only [map_one] using he'
    have hp := (conj_eq_iff_map_eq f hk _ _).mp he
    rw [hl, map_one] at hp
    exact hn i hp
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite C
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_not_surjective k hki hkn

open PSL3Even.UnipotentGeometry

/-- Four distinct nonidentity square roots of any projective element of square one. -/
theorem exists_four_square_roots (t : PSL) (ht : t ^ 2 = 1) :
    ∃ s : F → PSL, Function.Injective s ∧
      (∀ i, s i ≠ 1) ∧ (∀ i, s i ^ 2 = t) := by
  obtain ⟨b, hb⟩ := InvolutionClasses.projective_conjugate_root t ht
  obtain ⟨c, hc⟩ := (mem_projectiveCenter F _).mp hb
  let d := MulAut.conj b
  let s : F → PSL := fun i => d.symm (projective F ⟨1,c,i⟩)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro i j hij
    have he : projective F ⟨1,c,i⟩ = projective F ⟨1,c,j⟩ :=
      d.symm.injective hij
    exact congrArg U.c (projective_injective F he)
  · intro i hi
    have he : projective F ⟨1,c,i⟩ = projective F 1 := by
      have h := congrArg d hi
      simpa only [s, d.apply_symm_apply, map_one] using h
    have h10 := congrArg U.x (projective_injective F he)
    exact one_ne_zero h10
  · intro i
    apply d.injective
    change d ((d.symm (projective F ⟨1,c,i⟩)) ^ 2) = d t
    rw [map_pow, d.apply_symm_apply]
    change projective F ⟨1,c,i⟩ ^ 2 = b * t * b⁻¹
    rw [← hc, ← map_pow]
    congr 1
    apply U.ext <;> simp [pow_two, CharTwo.add_self_eq_zero]

/-- The actual lifted fixed inner image has order greater than four in every
finite central cover of PSL₃(4). The center is unrestricted. -/
theorem four_lt_card_inner_fixed_image {E : Type*} [Group E] [Finite E]
    (e : (E ⧸ center E) ≃* PSL) (a : MulAut E)
    (ha : a ∈ MulAut.innerSubgroup E) (hsq : a ^ 2 = 1) :
    4 < Nat.card (a.fixedSubgroup.map (MulAut.conj : E →* MulAut E)) := by
  obtain ⟨x, rfl⟩ := ha
  let f : E →* PSL := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center E := by
    ext y
    change e (y : E ⧸ center E) = 1 ↔ y ∈ center E
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hfx : (f x) ^ 2 = 1 := by
    have he : MulAut.conj (x ^ 2) = MulAut.conj (1 : E) := by
      rw [map_pow, hsq, map_one]
    have hp := (conj_eq_iff_map_eq f hk _ _).mp he
    simpa only [map_pow, map_one] using hp
  obtain ⟨s, hi, hn, hs⟩ := exists_four_square_roots (f x) hfx
  simpa only [card_F] using
    card_lt_inner_fixed_image_of_square_roots f hf hk x s hi hn hs

end Matrix.PSL3Four.InnerFixedCoverSize
