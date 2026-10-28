module

public import Theory.GroupTheory.ComponentLocalOrbitEmbedding

/-!
# Exact intersections of local component overgroups

Let L be a component of H and K a subgroup of L invariant under N_A(L),
where A is any subgroup of H. The A-conjugates of K normalize K and L:
conjugates in L agree with K, while those in other components commute with L.
Writing an element of L intersected with <K,A> as an orbit element times an
element of A therefore shows that it normalizes K. If K is self-normalizing
relative to L, this intersection is exactly K.

The proof is carried out inside H and then embedded in the ambient group.
Neither ambient normality nor trivial component centers are assumed.
Source application: Aschbacher–Smith, 2.3.9(7), printed p.526.
-/

public section

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The component intersection normalizes the chosen invariant local seed. -/
theorem IsComponent.local_adjoin_inf_le_normalizer {L K A : Subgroup G}
    (hL : IsComponent G L) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    L ⊓ (K ⊔ A) ≤ normalizer (K : Set G) := by
  have hDK : componentOrbit K A ≤ normalizer (K : Set G) := by
    apply iSup_le
    intro a
    simpa using hL.local_conjugates_normalize hK hinv (1 : A) a
  have hDL : componentOrbit K A ≤ normalizer (L : Set G) := by
    apply iSup_le
    intro a
    by_cases he : L.map (MulAut.conj (a : G)).toMonoidHom = L
    · have ht := map_mono (f := (MulAut.conj (a : G)).toMonoidHom) hK
      rw [he] at ht
      exact ht.trans L.le_normalizer
    · exact (map_mono hK).trans
        ((commutator_eq_bot_iff_le_centralizer.mp
          ((hL.map_conj (a : G)).commutator_eq_bot_of_ne hL he)).trans
            (centralizer_le_normalizer _))
  rintro x ⟨hxL, hx⟩
  have hm : x ∈ (componentOrbit K A : Set G) * (A : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (le_normalizer_componentOrbit K A),
      componentOrbit_sup]
    exact hx
  obtain ⟨y, hy, a, ha, rfl⟩ := hm
  have haL : a ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem_cancel_left (hDL hy) |>.mp (L.le_normalizer hxL)
  exact (normalizer (K : Set G)).mul_mem (hDK hy) (hinv ⟨ha, haL⟩)

/-- A relatively self-normalizing seed is the exact component intersection after adjoining A. -/
theorem IsComponent.relative_local_adjoin_intersection {H L K A : Subgroup G}
    (hL : IsComponent H (L.subgroupOf H)) (hLH : L ≤ H)
    (hKL : K ≤ L) (hAH : A ≤ H)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hself : L ⊓ normalizer (K : Set G) ≤ K) :
    L ⊓ (K ⊔ A) = K := by
  have hKH : K ≤ H := hKL.trans hLH
  have hinvH : A.subgroupOf H ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (K.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH, ← subgroupOf_normalizer_eq hKH]
    exact fun x hx => hinv hx
  have hbound := hL.local_adjoin_inf_le_normalizer (subgroupOf_mono H hKL) hinvH
  have hm : (K.subgroupOf H ⊔ A.subgroupOf H).map H.subtype = K ⊔ A := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hAH]
  apply le_antisymm
  · intro x hx
    let y : H := ⟨x, hLH hx.1⟩
    have hy : y ∈ K.subgroupOf H ⊔ A.subgroupOf H := by
      apply (mem_map_iff_mem H.subtype_injective).mp
      rw [hm]
      exact hx.2
    have hn := hbound ⟨hx.1, hy⟩
    rw [← subgroupOf_normalizer_eq hKH] at hn
    exact hself ⟨hx.1, hn⟩
  · exact le_inf hKL le_sup_left

end Theory.GroupTheory

end
