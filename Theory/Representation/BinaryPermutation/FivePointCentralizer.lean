module
public import Theory.Representation.BinaryPermutation.FivePointCore

/-!
The literal centralizer of a weight-two module vector maps into its
five-point stabilizer and contains a lift of the complement cubic. Hence
any normal two-subgroup of that centralizer acts inside the support
transposition. This is the source centralizer step of5.1.7(1).
-/
public section
open Subgroup
namespace BinaryPermutation.FivePointCore
open FiveCentralizerGeometry
variable {G : Type*} [Group G] (N : Subgroup G)
  (q : N →* Equiv.Perm (Fin 5))
  (hq : Function.Surjective q)
  (m : Multiplicative (core (Fin 5)) →* G) (hm : Function.Injective m)
  (he : ∀ (g : N) (x : core (Fin 5)),
    (g : G) * m (Multiplicative.ofAdd x) * (g : G)⁻¹ =
      m (Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g) x)))

include hq hm he

theorem normal_two_point_image (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPN : P ≤ N)
    (hPx : P ≤ centralizer ({m (Multiplicative.ofAdd v)} : Set G))
    (hCx : centralizer ({m (Multiplicative.ofAdd v)} : Set G) ≤ normalizer (P : Set G)) :
    (P.subgroupOf N).map q ≤ zpowers (Equiv.swap 0 1) := by
  let C := N ⊓ centralizer ({m (Multiplicative.ofAdd v)} : Set G)
  let p := q.comp (inclusion (show C ≤ N from inf_le_left))
  have hPC : P ≤ C := le_inf hPN hPx
  let : (P.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (inf_le_right.trans hCx)
  have hfix : ∀ g, coreRepresentation (Fin 5) (p g) v = v := by
    intro g
    apply Multiplicative.ofAdd.injective
    apply hm
    change m (Multiplicative.ofAdd (coreRepresentation (Fin 5) (q (inclusion inf_le_left g)) v)) = _
    rw [←he]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property.2)
  have hc : Equiv.swap 2 3 * Equiv.swap 3 4 ∈ p.range := by
    obtain ⟨g,hg⟩ := hq (Equiv.swap 2 3 * Equiv.swap 3 4)
    have hcv : coreRepresentation (Fin 5) (Equiv.swap 2 3 * Equiv.swap 3 4) v = v := by
      decide +kernel
    have hx : (g:G) ∈ centralizer ({m (Multiplicative.ofAdd v)} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      rw [he,hg,hcv]
    exact ⟨⟨g,g.property,hx⟩,hg⟩
  have hb := normal_two_image_le_transposition p (P.subgroupOf C) hP.comap_subtype hfix hc
  have hmap : (P.subgroupOf C).map p = (P.subgroupOf N).map q := by
    change (P.subgroupOf C).map (q.comp (inclusion (show C ≤ N from inf_le_left))) = _
    rw [←Subgroup.map_map]
    congr 1
    ext g
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ha
    · intro hg
      exact ⟨⟨g,hPC hg⟩,hg,rfl⟩
  exact hmap ▸ hb

theorem normal_two_second_point_image (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPN : P ≤ N)
    (hPx : P ≤ centralizer ({m (Multiplicative.ofAdd second)} : Set G))
    (hCx : centralizer ({m (Multiplicative.ofAdd second)} : Set G) ≤ normalizer (P : Set G)) :
    (P.subgroupOf N).map q ≤ zpowers (Equiv.swap 2 3) := by
  let C := N ⊓ centralizer ({m (Multiplicative.ofAdd second)} : Set G)
  let p := q.comp (inclusion (show C ≤ N from inf_le_left))
  have hPC : P ≤ C := le_inf hPN hPx
  let : (P.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (inf_le_right.trans hCx)
  have hfix : ∀ g, coreRepresentation (Fin 5) (p g) second = second := by
    intro g
    apply Multiplicative.ofAdd.injective
    apply hm
    change m (Multiplicative.ofAdd (coreRepresentation (Fin 5) (q (inclusion inf_le_left g)) second)) = _
    rw [←he]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property.2)
  have hc : Equiv.swap 0 1 * Equiv.swap 1 4 ∈ p.range := by
    obtain ⟨g,hg⟩ := hq (Equiv.swap 0 1 * Equiv.swap 1 4)
    have hcv : coreRepresentation (Fin 5) (Equiv.swap 0 1 * Equiv.swap 1 4) second = second := by
      decide +kernel
    have hx : (g:G) ∈ centralizer ({m (Multiplicative.ofAdd second)} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      rw [he,hg,hcv]
    exact ⟨⟨g,g.property,hx⟩,hg⟩
  have hb := normal_two_second_image_le_transposition p (P.subgroupOf C) hP.comap_subtype hfix hc
  have hmap : (P.subgroupOf C).map p = (P.subgroupOf N).map q := by
    change (P.subgroupOf C).map (q.comp (inclusion (show C ≤ N from inf_le_left))) = _
    rw [←Subgroup.map_map]
    congr 1
    ext g
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ha
    · intro hg
      exact ⟨⟨g,hPC hg⟩,hg,rfl⟩
  exact hmap ▸ hb
end BinaryPermutation.FivePointCore
