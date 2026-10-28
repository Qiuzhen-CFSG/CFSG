module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Normalizers across a normalizing prime-group kernel

If a homomorphism has p-group kernel normalizing a p-perfect subgroup A,
then A is the p-residual of A ker(f). Consequently every normalizer of
f(A) lifts to a normalizer of A. The normalization hypothesis on the kernel
is essential; normality of the kernel alone does not suffice.

Source application: Aschbacher–Smith, 13.8.25, printed p.960, lifting the
normalizer of L₀* through O₂(H) before applying 13.2.2(9).
-/

public section
namespace Subgroup
variable {G D : Type*} [Group G] [Group D] {p : ℕ}

/-- The full preimage of the image recovers the original p-perfect subgroup
as its p-residual when the kernel normalizes it. -/
theorem embedded_pResidual_sup_kernel (f : G →* D) (A : Subgroup G)
    (hA : IsPPerfect p A) (hk : IsPGroup p f.ker)
    (hn : f.ker ≤ normalizer (A : Set G)) :
    (pResidual p (A ⊔ f.ker : Subgroup G)).map (A ⊔ f.ker).subtype = A := by
  let P := A ⊔ f.ker
  let : (A.subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hp : IsPPerfect p (A.subgroupOf P) :=
    hA.of_surjective (subgroupOfEquivOfLe (show A ≤ P from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show A ≤ P from le_sup_left)).symm.surjective
  have hs : A.subgroupOf P ⊔ f.ker.subgroupOf P = ⊤ := by
    rw [← subgroupOf_sup (show A ≤ P from le_sup_left)
      (show f.ker ≤ P from le_sup_right)]
    exact subgroupOf_self P
  change (pResidual p P).map P.subtype = A
  rw [pResidual_eq_of_isPPerfect_sup (A.subgroupOf P) (f.ker.subgroupOf P)
    hp hk.comap_subtype hs, map_subgroupOf_eq_of_le (show A ≤ P from le_sup_left)]

/-- Normalizer lifting for a p-perfect subgroup through a normalizing
p-group kernel. This equality does not require surjectivity. -/
theorem comap_normalizer_map_of_pPerfect (f : G →* D) (A : Subgroup G)
    (hA : IsPPerfect p A) (hk : IsPGroup p f.ker)
    (hn : f.ker ≤ normalizer (A : Set G)) :
    (normalizer (A.map f : Set D)).comap f = normalizer (A : Set G) := by
  apply le_antisymm
  · rw [comap_normalizer_eq_of_le_range (map_le_range _ _), comap_map_eq]
    have h := normalizer_le_normalizer_characteristic_image
      (A ⊔ f.ker) (pResidual p (A ⊔ f.ker : Subgroup G))
    rwa [embedded_pResidual_sup_kernel f A hA hk hn] at h
  · exact map_le_iff_le_comap.mp (le_normalizer_map f)

/-- Under a surjection, the whole target normalizer is the image of the
original normalizer, with no extra normalizer premise on the image. -/
theorem map_normalizer_of_pPerfect (f : G →* D) (hf : Function.Surjective f)
    (A : Subgroup G) (hA : IsPPerfect p A) (hk : IsPGroup p f.ker)
    (hn : f.ker ≤ normalizer (A : Set G)) :
    (normalizer (A : Set G)).map f = normalizer (A.map f : Set D) := by
  rw [← comap_normalizer_map_of_pPerfect f A hA hk hn,
    map_comap_eq_self_of_surjective hf]

end Subgroup
end
