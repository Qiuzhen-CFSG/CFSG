module

public import Theory.GroupTheory.PResidual.PrimeSection
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Containment from an equivariant projection

Let a p-perfect subgroup D normalize K, and let S ≤ K normalize D.
Suppose D and S map equivariantly to a group H, with p-group kernel on D,
and the two image groups generate the D-image by commutators. Then D ≤ K.
Indeed the commutators lie in D ∩ K and cover the image of D. The quotient
D/(D ∩ K) is consequently a p-group and p-perfectness makes it trivial.

Only the kernel on D is used. No bound on an ambient quotient kernel, or
containment inferred solely from equality of quotient images, is needed.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
13.6.20, printed p.931, with D = Lᵥ and S = Tᵥ ∩ K.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

/-- Commutator generation of an equivariant image lifts through the kernel on D. -/
theorem le_of_equivariant_projection
    (D K S : Subgroup G) (hD : IsPPerfect p D)
    (hSD : S ≤ normalizer (D : Set G))
    (hSK : S ≤ K) (hDK : D ≤ normalizer (K : Set G))
    (f : D →* H) (g : S →* H) (hk : IsPGroup p f.ker)
    (he : ∀ (s : S) (d : D),
      f ⟨(s : G) * d * (s : G)⁻¹,
        (mem_normalizer_iff.mp (hSD s.property) d).mp d.property⟩ =
          g s * f d * (g s)⁻¹)
    (hc : ⁅f.range, g.range⁆ = f.range) : D ≤ K := by
  let N := K.subgroupOf D
  let : N.Normal := normal_subgroupOf_of_le_normalizer hDK
  have hr : f.range ≤ N.map f := by
    rw [← hc]
    apply commutator_le.mpr
    rintro _ ⟨d, rfl⟩ _ ⟨s, rfl⟩
    let c : D := ⟨⁅(d : G), (s : G)⁆,
      le_normalizer_iff_commutator_le_left.mp hSD
        (commutator_mem_commutator d.property s.property)⟩
    have hcK : c ∈ N :=
      le_normalizer_iff_commutator_le_right.mp hDK
        (commutator_mem_commutator d.property (hSK s.property))
    refine ⟨c, hcK, ?_⟩
    have hcd : c = d * ⟨(s : G) * (d⁻¹ : D) * (s : G)⁻¹,
      (mem_normalizer_iff.mp (hSD s.property) (d⁻¹ : D)).mp (d⁻¹).property⟩ := by
      apply Subtype.ext
      simp only [c, commutatorElement_def, coe_mul, coe_inv]
      group
    rw [hcd, map_mul, he, map_inv]
    simp only [commutatorElement_def, mul_assoc]
  have hs : N ⊔ f.ker = ⊤ := by
    have hm : (⊤ : Subgroup D).map f ≤ N.map f := by
      simpa only [← MonoidHom.range_eq_map] using hr
    have hp := comap_mono (f := f) hm
    rw [comap_map_eq, top_sup_eq, comap_map_eq] at hp
    exact top_unique hp
  have hp : IsPPerfect p (⊤ : Subgroup D) :=
    hD.of_surjective Subgroup.topEquiv.symm.toMonoidHom Subgroup.topEquiv.symm.surjective
  have hn : (⊤ : Subgroup D) ≤ N :=
    le_normal_of_isPPerfect_of_le_sup_pGroup ⊤ N f.ker hp hk hs.ge
  exact fun d hd => hn (mem_top (⟨d, hd⟩ : D))
end Subgroup
