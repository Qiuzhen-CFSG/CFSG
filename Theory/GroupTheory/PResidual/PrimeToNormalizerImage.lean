module
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PrimeToMonotone

/-!
# Lifting normalizers through a coprime kernel

If A is its own prime-to-p residual and ker(f) has order prime to p and
normalizes A, then A is the embedded prime-to-p residual of A ker(f).
Its relative index divides the order of the kernel. Characteristicity
therefore lifts normalizers of the actual image f(A) back to normalizers
of A. No identification of the kernel with a prime-group core is needed.

Source application: Aschbacher–Smith 13.4.7, printed p.900, where the
action kernel is a 3′-group and normalizes both local residuals.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Adjoining a coprime normalizing kernel preserves the embedded residual. -/
theorem embedded_primeToResidual_sup_kernel (p : ℕ) (f : G →* H) (A : Subgroup G)
    (hA : primeToResidual p A = ⊤)
    (hk : Nat.Coprime p (Nat.card f.ker))
    (hn : f.ker ≤ normalizer (A : Set G)) :
    (primeToResidual p (A ⊔ f.ker : Subgroup G)).map (A ⊔ f.ker).subtype = A := by
  let P := A ⊔ f.ker
  let A' := A.subgroupOf P
  let : A'.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hA' : primeToResidual p A' = ⊤ := by
    let e := (subgroupOfEquivOfLe (show A ≤ P from le_sup_left)).symm
    have he := map_primeToResidual (p := p) e
    rw [hA,map_top_of_surjective _ e.surjective] at he
    exact he.symm
  have hs : A' ⊔ f.ker.subgroupOf P = ⊤ := by
    rw [←subgroupOf_sup (show A ≤ P from le_sup_left)
      (show f.ker ≤ P from le_sup_right)]
    exact subgroupOf_self P
  have hi : A'.index ∣ Nat.card f.ker := by
    have he := relIndex_sup_left (f.ker.subgroupOf P) A'
    rw [hs,relIndex_top_right] at he
    rw [he]
    exact (relIndex_dvd_card _ _).trans (by
      rw [Nat.card_congr (subgroupOfEquivOfLe (show f.ker ≤ P from le_sup_right)).toEquiv])
  have hr := primeToResidual_eq_of_subnormal_coprime_index p A'
    (inferInstance : A'.Normal).isSubnormal hA' (hk.of_dvd_right hi)
  rw [hr,map_subgroupOf_eq_of_le (show A ≤ P from le_sup_left)]

/-- The literal image normalizer has precisely the original normalizer as its preimage. -/
theorem comap_normalizer_map_of_primeToResidual (p : ℕ) (f : G →* H) (A : Subgroup G)
    (hA : primeToResidual p A = ⊤)
    (hk : Nat.Coprime p (Nat.card f.ker))
    (hn : f.ker ≤ normalizer (A : Set G)) :
    (normalizer (A.map f : Set H)).comap f = normalizer (A : Set G) := by
  apply le_antisymm
  · rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq]
    have hh := normalizer_le_normalizer_characteristic_image
      (A ⊔ f.ker) (primeToResidual p (A ⊔ f.ker : Subgroup G))
    rwa [embedded_primeToResidual_sup_kernel p f A hA hk hn] at hh
  · exact map_le_iff_le_comap.mp (le_normalizer_map f)

/-- Normalization reflects through a coprime normalizing kernel. -/
theorem map_le_normalizer_map_iff_of_primeToResidual (p : ℕ) (f : G →* H) (A B : Subgroup G)
    (hA : primeToResidual p A = ⊤)
    (hk : Nat.Coprime p (Nat.card f.ker))
    (hn : f.ker ≤ normalizer (A : Set G)) :
    B.map f ≤ normalizer (A.map f : Set H) ↔ B ≤ normalizer (A : Set G) := by
  rw [map_le_iff_le_comap,comap_normalizer_map_of_primeToResidual p f A hA hk hn]
end Subgroup
