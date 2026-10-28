module

public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# A crossing kernel embeds in its Sylow image

If an ambient normalizer carries a subgroup C into S and its conjugate is
 disjoint from C, a homomorphism on H with kernel C restricts faithfully to
that conjugate. Pulling back by conjugation embeds the original C into the
actual image of S. This retains the given homomorphism and right-conjugation
convention used in Aschbacher--Smith 2.5.5 and 2.5.21, pp.554 and 565.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- The original kernel embeds into the image of S through its right conjugate. -/
theorem exists_conjugate_kernel_embedding (H S C : Subgroup G)
    (hSH : S ≤ H) (hCS : C ≤ S) (f : H →* Q)
    (hker : f.ker = C.subgroupOf H) (x : G)
    (hx : x ∈ normalizer (S : Set G))
    (hdis : Disjoint C (C.conjBy x⁻¹)) :
    ∃ j : C →* Q, Function.Injective j ∧ j.range ≤ (S.subgroupOf H).map f := by
  have hconj (c : C) : x⁻¹ * (c : G) * x ∈ S := by
    have hh := (mem_normalizer_iff.mp ((normalizer (S : Set G)).inv_mem hx) (c : G)).mp
      (hCS c.property)
    simpa only [inv_inv] using hh
  let a : C →* H :=
    { toFun := fun c => ⟨x⁻¹ * (c : G) * x, hSH (hconj c)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun c d => Subtype.ext (by simp [mul_assoc]) }
  refine ⟨f.comp a, ?_, ?_⟩
  · apply (injective_iff_map_eq_one _).mpr
    intro c hc
    have hk : a c ∈ f.ker := hc
    rw [hker] at hk
    have he : x⁻¹ * (c : G) * x = 1 := by
      exact Subgroup.disjoint_def.mp hdis
        (show x⁻¹ * (c : G) * x ∈ C from hk)
        ⟨c, c.property, by simp⟩
    apply Subtype.ext
    have hh := congrArg (MulAut.conj x) he
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · rintro _ ⟨c, rfl⟩
    exact ⟨a c, hconj c, rfl⟩

end Theory.GroupTheory
