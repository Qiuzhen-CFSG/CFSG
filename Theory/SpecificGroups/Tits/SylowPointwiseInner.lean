module

public import Theory.SpecificGroups.Tits.SharpOuterBound.Kernel
public import Theory.GroupAction.SylowPointwiseInner
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Pointwise Sylow stabilizers in the Tits group

The certified restriction kernel has order at most two. Conjugation by the
nonidentity central Sylow element `atlas1600R5` is a nontrivial member of
that kernel, since the ambient group is centerless. These two elements
therefore exhaust the kernel. Sylow conjugacy and the certified Parrott
comparison transport this calculation to every Sylow subgroup of the actual
Tits carrier. No restriction on the automorphism order is needed.

The final marking theorem also identifies every nonidentity pointwise fixer
with the concrete `r5` conjugation under an aligned model isomorphism. It
does not identify `r5` with a root of the Ree construction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma 16.1.6, printed p.1172; Parrott (1972), §5,
p.683, for the concrete Sylow presentation. The kernel and center calculations
are reused through the imported, kernel-checked certificates.
-/

public section
namespace Tits.SylowPointwiseInner
open Subgroup OuterOddSubgroups

private def toKernel (a : MulAut Atlas1600Group)
    (ha : ∀ x ∈ atlas1600SylowTwoSubgroup, a x = x) : sylowRestriction.ker := by
  have hm : atlas1600SylowTwoSubgroup.map a.toMonoidHom = atlas1600SylowTwoSubgroup := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change a y ∈ atlas1600SylowTwoSubgroup
      rw [ha y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, ha x hx⟩
  exact ⟨⟨a, hm⟩, (mem_sylowRestriction_ker_iff _).mpr ha⟩

private theorem r5_fixes (x : Atlas1600Group) (hx : x ∈ atlas1600SylowTwoSubgroup) :
    MulAut.conj atlas1600R5 x = x := by
  have hc := congrArg Subtype.val
    (mem_center_iff.mp atlas1600R5_mem_center_sylowTwo ⟨x, hx⟩)
  change x * atlas1600R5 = atlas1600R5 * x at hc
  change atlas1600R5 * x * atlas1600R5⁻¹ = x
  rw [← hc, mul_inv_cancel_right]

private def r5Kernel : sylowRestriction.ker := toKernel (MulAut.conj atlas1600R5) r5_fixes

private theorem r5Kernel_ne_one : r5Kernel ≠ 1 := by
  intro h
  have he : MulAut.conj atlas1600R5 = 1 :=
    congrArg (fun a : sylowRestriction.ker => a.val.val) h
  have hz : atlas1600R5 ∈ center Atlas1600Group := by
    rw [mem_center_iff]
    intro x
    have hx := MulEquiv.congr_fun he x
    change atlas1600R5 * x * atlas1600R5⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  rw [RelativeSylowMarking.atlas_center_eq_bot, mem_bot] at hz
  exact atlas1600R5_ne_one hz

private theorem kernel_cases (a : sylowRestriction.ker) : a = 1 ∨ a = r5Kernel := by
  let f : Bool → sylowRestriction.ker := fun b => if b then r5Kernel else 1
  have hi : Function.Injective f := by
    intro b c h
    cases b <;> cases c <;> simp_all [f, r5Kernel_ne_one, Ne.symm r5Kernel_ne_one]
  have hs : Function.Surjective f := (hi.bijective_of_nat_card_le
    (by simpa using SharpOuterBound.sylowRestriction_kernel_card_le_two)).2
  obtain ⟨b, hb⟩ := hs a
  cases b
  · exact Or.inl hb.symm
  · exact Or.inr hb.symm

/-- Exactly two automorphisms fix the certified Sylow subgroup pointwise. -/
theorem atlas_fixing_standard_cases (a : MulAut Atlas1600Group)
    (ha : ∀ x ∈ atlas1600SylowTwoSubgroup, a x = x) :
    a = 1 ∨ a = MulAut.conj atlas1600R5 := by
  rcases kernel_cases (toKernel a ha) with h | h
  · exact Or.inl (congrArg (fun b : sylowRestriction.ker => b.val.val) h)
  · exact Or.inr (congrArg (fun b : sylowRestriction.ker => b.val.val) h)

/-- Every pointwise Sylow fixer in the Atlas carrier is inner, with its
conjugating element in the specified Sylow subgroup. -/
theorem atlas_fixing_sylow_inner (P : Sylow 2 Atlas1600Group)
    (a : MulAut Atlas1600Group) (ha : ∀ x ∈ P, a x = x) :
    ∃ x ∈ P, a = MulAut.conj x := by
  apply MulAut.fixing_inner_sylow atlas1600SylowTwo P _ a ha
  intro b hb
  change ∀ x ∈ (atlas1600SylowTwo : Subgroup Atlas1600Group), b x = x at hb
  rw [atlas1600SylowTwo_coe] at hb
  change ∃ x ∈ (atlas1600SylowTwo : Subgroup Atlas1600Group), b = MulAut.conj x
  rw [atlas1600SylowTwo_coe]
  rcases atlas_fixing_standard_cases b hb with h | h
  · exact ⟨1, one_mem _, h.trans (map_one MulAut.conj).symm⟩
  · exact ⟨atlas1600R5, atlas1600R5_mem_sylowTwo, h⟩

/-- The pointwise innerness calculation on the actual Parrott carrier. -/
theorem parrott_fixing_sylow_inner (P : Sylow 2 ParrottGroup)
    (a : MulAut ParrottGroup) (ha : ∀ x ∈ P, a x = x) :
    ∃ x ∈ P, a = MulAut.conj x := by
  let e := parrottFiniteImageEquiv
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hb : ∀ y ∈ Q, MulAut.congr e a y = y := by
    rintro y ⟨x, hx, rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply, ha x hx]
  obtain ⟨y, hy, he⟩ := atlas_fixing_sylow_inner Q (MulAut.congr e a) hb
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨x, hx, (MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj]
  exact he

/-- A nonidentity pointwise Sylow fixer becomes conjugation by the
distinguished central involution under a Sylow-aligned actual model map. -/
theorem fixing_sylow_marking {G : Type*} [Group G]
    (e : G ≃* Atlas1600Group) (P : Sylow 2 G) (a : MulAut G)
    (ha : ∀ x ∈ P, a x = x) (hne : a ≠ 1) :
    ∃ f : G ≃* Atlas1600Group,
      (P : Subgroup G).map f.toMonoidHom = atlas1600SylowTwoSubgroup ∧
      MulAut.congr f a = MulAut.conj atlas1600R5 := by
  obtain ⟨f, hf⟩ := RelativeSylowMarking.exists_sylow_marking e P
  have hb : ∀ y ∈ atlas1600SylowTwoSubgroup, MulAut.congr f a y = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hf.symm ▸ hy
    change f (a (f.symm (f x))) = f x
    rw [f.symm_apply_apply, ha x hx]
  refine ⟨f, hf, ?_⟩
  rcases atlas_fixing_standard_cases (MulAut.congr f a) hb with h | h
  · exact (hne ((MulAut.congr f).injective (h.trans (map_one _).symm))).elim
  · exact h

end Tits.SylowPointwiseInner
