module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Conjugation

/-!
# A spanning outer orbit in the quintet kernel

The Q-span of a vector outside A0 = K ∩ L supplements A0, a hyperplane.
Its intersection with A0 is zero or all of A0 by irreducibility of the
actual inner conjugation action. Indecomposability of the actual action
on K excludes the complementary case, so the orbit spans K.

If an index-two subgroup misses this orbit, its binary membership character
agrees on the orbit with that of A0. The locus of agreement is a binary
subspace, so spanning forces the two subgroups to coincide. Consequently
every other hyperplane contains a Q-conjugate of the given outer element.
Only normality relative to Q is used.

Source: the involution-selection step of Aschbacher--Smith H.15.4(3),
printed p.400, using the conjugation modules of H.14.3(2), printed p.397.
Irreducibility and indecomposability remain explicit earlier inputs.
-/

public section
noncomputable section
open scoped IsMulCommutative
namespace MathieuCode.M22Quintet.CocodeTransfer

private def orbitSpan [IsElementaryAbelian 2 K] (v : Additive K) :
    Subrepresentation kernelConjugation where
  toSubmodule := Submodule.span (ZMod 2) (Set.range fun g : Q => kernelConjugation g v)
  apply_mem_toSubmodule g w hw := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a,rfl⟩ := hw
      apply Submodule.subset_span
      refine ⟨g*a, ?_⟩
      change kernelConjugation (g*a) v = kernelConjugation g (kernelConjugation a v)
      rw [map_mul, Module.End.mul_apply]
    | zero => simp
    | add x y hx hy hfx hfy => simpa using Submodule.add_mem _ hfx hfy
    | smul c x hx hfx => simpa using Submodule.smul_mem _ c hfx

private theorem inner_mem_iff [IsElementaryAbelian 2 K] (I : InnerInputs) (v : Additive K) :
    v ∈ innerSubrepresentation I ↔ v.toMul.val ∈ A0 := by
  constructor
  · rintro ⟨a,rfl⟩
    exact a.toMul.property
  · intro h
    exact ⟨Additive.ofMul ⟨v.toMul.val,h⟩, rfl⟩

/-- Every outer vector generates the actual conjugation module under Q. -/
theorem kernel_conjugation_orbit_span_eq_top [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hindecomp : ∀ U W : Subrepresentation kernelConjugation,
      IsCompl U W → U = ⊥ ∨ W = ⊥)
    (v : Additive K) (hv : v.toMul.val ∉ A0) :
    Submodule.span (ZMod 2) (Set.range fun g : Q => kernelConjugation g v) = ⊤ := by
  let U := innerSubrepresentation I
  let R := orbitSpan v
  have hvR : v ∈ R := by
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  have hdU : Module.finrank (ZMod 2) U.toSubmodule = 4 := by
    change Module.finrank (ZMod 2) innerInclusion.range = 4
    rw [LinearMap.finrank_range_of_inj innerInclusion_injective, finrank_inner D I]
  have hvU : v ∉ U := by rwa [inner_mem_iff]
  have hsup : U ⊔ R = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    have hlt : U.toSubmodule < (U ⊔ R).toSubmodule := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro he
      apply hvU
      change v ∈ U.toSubmodule
      rw [he]
      exact Submodule.mem_sup_right hvR
    have hl := Submodule.finrank_lt_finrank_of_lt hlt
    have hb := (U ⊔ R).toSubmodule.finrank_le
    rw [finrank_kernel D] at hb ⊢
    omega
  let T : Subrepresentation (innerConjugation I) :=
    { toSubmodule := R.toSubmodule.comap innerInclusion
      apply_mem_toSubmodule g a ha := by
        change innerInclusion (innerConjugation I g a) ∈ R
        rw [innerInclusion_equivariant]
        exact R.apply_mem_toSubmodule g ha }
  rcases eq_bot_or_eq_top T with ht | ht
  · have hinf : U ⊓ R = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply (Submodule.eq_bot_iff _).mpr
      intro w hw
      obtain ⟨a,rfl⟩ := hw.1
      have ha : a ∈ T := hw.2
      rw [ht] at ha
      have ha0 : a = 0 := ha
      rw [ha0, map_zero]
    rcases hindecomp U R (IsCompl.of_eq hinf hsup) with hu | hr
    · have hz : Module.finrank (ZMod 2) U.toSubmodule = 0 := by
        rw [hu]
        exact finrank_bot (ZMod 2) (Additive K)
      omega
    · rw [hr] at hvR
      have hz : v = 0 := hvR
      exact False.elim (hvU (hz ▸ U.toSubmodule.zero_mem))
  · have hUR : U ≤ R := by
      rintro w ⟨a,rfl⟩
      have ha : a ∈ T := by rw [ht]; trivial
      exact ha
    have hR : R = ⊤ := by simpa only [sup_eq_right.mpr hUR] using hsup
    exact congrArg Subrepresentation.toSubmodule hR

private def sameMembershipSpace [IsElementaryAbelian 2 K]
    (B C : Subgroup K) (hB : B.index = 2) (hC : C.index = 2) :
    Submodule (ZMod 2) (Additive K) where
  carrier := {v | v.toMul ∈ B ↔ v.toMul ∈ C}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x.toMul ∈ B ↔ x.toMul ∈ C at hx
    change y.toMul ∈ B ↔ y.toMul ∈ C at hy
    change x.toMul * y.toMul ∈ B ↔ x.toMul * y.toMul ∈ C
    rw [B.mul_mem_iff_of_index_two hB, C.mul_mem_iff_of_index_two hC, hx, hy]
  smul_mem' := by
    intro c v hv
    have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    rcases hb c with rfl | rfl
    · simp
    · simpa only [one_smul] using hv

/-- Every other hyperplane meets the Q-orbit of any specified element of K outside L. -/
theorem exists_conjugate_mem_hyperplane [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hindecomp : ∀ U W : Subrepresentation kernelConjugation,
      IsCompl U W → U = ⊥ ∨ W = ⊥)
    (i0 : m22PairStabilizer) (hi0 : i0 ∈ K) (hout : i0 ∉ L)
    (A : Subgroup m22PairStabilizer) (hA : A ≤ K) (hindex : A.relIndex K = 2)
    (hne : A ≠ A0) : ∃ g : Q, g.val * i0 * g.val⁻¹ ∈ A := by
  classical
  by_contra h
  push Not at h
  let v : Additive K := Additive.ofMul ⟨i0,hi0⟩
  have hv : v.toMul.val ∉ A0 := fun hh => hout hh.2
  let S := sameMembershipSpace (A.subgroupOf K) (A0.subgroupOf K) hindex I.index
  have hS : S = ⊤ := by
    apply top_unique
    rw [← kernel_conjugation_orbit_span_eq_top D I hindecomp v hv]
    apply Submodule.span_le.mpr
    rintro w ⟨g,rfl⟩
    change (g.val * i0 * g.val⁻¹ ∈ A) ↔ (g.val * i0 * g.val⁻¹ ∈ A0)
    have h0 : g.val * i0 * g.val⁻¹ ∉ A0 := by
      intro hh
      exact hv ((Subgroup.mem_normalizer_iff.mp (I.normalizer g.property) i0).mpr hh)
    exact iff_of_false (h g) h0
  apply hne
  ext i
  constructor
  · intro hi
    have hh : Additive.ofMul (⟨i,hA hi⟩ : K) ∈ S := by rw [hS]; trivial
    exact hh.mp hi
  · intro hi
    have hh : Additive.ofMul (⟨i,hi.1⟩ : K) ∈ S := by rw [hS]; trivial
    exact hh.mpr hi

end MathieuCode.M22Quintet.CocodeTransfer
