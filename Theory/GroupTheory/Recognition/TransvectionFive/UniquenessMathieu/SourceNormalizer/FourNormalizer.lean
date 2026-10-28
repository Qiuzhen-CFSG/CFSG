module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.CubicLift
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Centralizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.KernelOrbit

/-!
# The actual exceptional four-subgroup normalizer

The cubic lift acts transitively on the three nonidentity elements of each
literal four-subgroup. If an element normalizes that four-subgroup, a cubic
factor can match its image of t, leaving a factor in C_{N_G(A)}(t). Thus the
normalizer is exactly XI, both as a subgroup join and as a set product.
Every action and lift uses the original rectangle quotient map.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2), p.218.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code)
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

private theorem sextet_kernel_card (hc : (F.fusion F.plane).ncard = 45) :
    Nat.card Sextet.action.ker = 3 := by
  let lift : (planeSextetAction F hc).ker → Sextet.action.ker := fun q =>
    ⟨planeSextetRepresentation F hc q.val, by
      change Sextet.action (planeSextetRepresentation F hc q.val) = 1
      rw [← planeSextetAction_apply]
      exact q.property⟩
  have hi : Function.Injective lift := by
    intro a b h
    exact Subtype.ext (planeSextetRepresentation_injective F hc (congrArg Subtype.val h))
  have hl := Nat.card_le_card_of_injective lift hi
  rw [(planeSextetAction_structure F hc).1] at hl
  exact Nat.le_antisymm Sextet.kernel_card_le hl

/-- Every cubic lift of the kernel is transitive on the three nonidentity
elements of each original four-subgroup. -/
theorem plane_cubic_transitive (hc : (F.fusion F.plane).ncard = 45)
    (X : Subgroup (planeNormalizer F))
    (hX : X.map (QuotientGroup.mk' (F.plane.subgroupOf (planeNormalizer F))) =
      (planeSextetAction F hc).ker)
    (i : Fin 6) (a b : G) (ha : a ∈ planeFour F i) (hb : b ∈ planeFour F i)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ n : X, (n.val : G) * a * (n.val : G)⁻¹ = b := by
  obtain ⟨x,hx,hxa⟩ := (mem_planeFour F i a).mp ha
  obtain ⟨y,hy,hyb⟩ := (mem_planeFour F i b).mp hb
  have hx0 : x ≠ 0 := fun h => ha1 (hxa.symm.trans (h ▸ element_zero F))
  have hy0 : y ≠ 0 := fun h => hb1 (hyb.symm.trans (h ▸ element_zero F))
  obtain ⟨k,hk⟩ := Sextet.kernel_transitive_line (sextet_kernel_card F hc) i x hx hx0 y hy hy0
  obtain ⟨q,hq⟩ := planeSextetRepresentation_surjective F hc k.val
  have hqK : q ∈ (planeSextetAction F hc).ker := by
    change planeSextetAction F hc q = 1
    rw [planeSextetAction_apply, hq]
    exact k.property
  rw [← hX] at hqK
  obtain ⟨n, hn, hnq⟩ := hqK
  refine ⟨⟨n,hn⟩, ?_⟩
  have he : element F ((planeSextetRepresentation F hc (QuotientGroup.mk n)).val x) = b := by
    rw [show QuotientGroup.mk n = q from hnq, hq, hk, hyb]
  rw [planeSextetRepresentation_val, quotientCodeAction_mk, normalizerAction_element, hxa] at he
  exact he

private theorem cubic_le_four_normalizer (hc : (F.fusion F.plane).ncard = 45)
    (X : Subgroup (planeNormalizer F))
    (hX : X.map (QuotientGroup.mk' (F.plane.subgroupOf (planeNormalizer F))) =
      (planeSextetAction F hc).ker) (i : Fin 6) :
    X ≤ (normalizer (planeFour F i : Set G)).subgroupOf (planeNormalizer F) := by
  intro n hn
  have hk : QuotientGroup.mk n ∈ (planeSextetAction F hc).ker :=
    hX ▸ mem_map_of_mem _ hn
  have he : planeSextetAction F hc (QuotientGroup.mk n) = 1 := hk
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (planeFour F i).map (MulAut.conj (n : G)).toMonoidHom = _
  rw [planeSextetAction_conjugation F hc, he, Equiv.Perm.one_apply]

private theorem point_centralizer_le_four_normalizer (hc : (F.fusion F.plane).ncard = 45)
    (i : Fin 6) (t : G) (ht : t ∈ planeFour F i) (ht1 : t ≠ 1) :
    (planeCentralizer F t).subgroupOf (planeNormalizer F) ≤
      (normalizer (planeFour F i : Set G)).subgroupOf (planeNormalizer F) := by
  intro n hn
  have hnt : (n : G) * t * (n : G)⁻¹ = t := by
    have he : (n : G) * t = t * (n : G) := mem_centralizer_singleton_iff.mp hn.2
    rw [he, mul_inv_cancel_right]
  have hm : t ∈ (planeFour F i).map (MulAut.conj (n : G)).toMonoidHom :=
    ⟨t, ht, hnt⟩
  rw [planeSextetAction_conjugation F hc n] at hm
  obtain ⟨j, _, hu⟩ := exists_unique_planeFour F hc t (planeFour_le F i ht) ht1
    (planeFour_not_fused F hc i t ht ht1)
  have he : planeSextetAction F hc (QuotientGroup.mk n) i = i :=
    (hu _ hm).trans (hu i ht).symm
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (planeFour F i).map (MulAut.conj (n : G)).toMonoidHom = _
  rw [planeSextetAction_conjugation F hc, he]

/-- The normalizer of an exceptional four-subgroup is the literal set
product of a cubic lift and the centralizer of any of its nonidentity elements. -/
theorem plane_four_normalizer_product (hc : (F.fusion F.plane).ncard = 45)
    (X : Subgroup (planeNormalizer F))
    (hX : X.map (QuotientGroup.mk' (F.plane.subgroupOf (planeNormalizer F))) =
      (planeSextetAction F hc).ker)
    (i : Fin 6) (t : G) (ht : t ∈ planeFour F i) (ht1 : t ≠ 1) :
    ((normalizer (planeFour F i : Set G)).subgroupOf (planeNormalizer F) : Set (planeNormalizer F)) =
      (X : Set (planeNormalizer F)) *
        ((planeCentralizer F t).subgroupOf (planeNormalizer F) : Set (planeNormalizer F)) := by
  let D := (normalizer (planeFour F i : Set G)).subgroupOf (planeNormalizer F)
  let I := (planeCentralizer F t).subgroupOf (planeNormalizer F)
  have hXD : X ≤ D := cubic_le_four_normalizer F hc X hX i
  have hID : I ≤ D := point_centralizer_le_four_normalizer F hc i t ht ht1
  apply Set.ext
  intro n
  constructor
  · intro hn
    have hb : (n : G) * t * (n : G)⁻¹ ∈ planeFour F i :=
      (mem_normalizer_iff.mp hn t).mp ht
    have hb1 : (n : G) * t * (n : G)⁻¹ ≠ 1 := by
      intro h
      apply ht1
      exact (MulAut.conj (n : G)).injective (h.trans (map_one _).symm)
    obtain ⟨v,hv⟩ := plane_cubic_transitive F hc X hX i t _ ht hb ht1 hb1
    have hI : v.val⁻¹ * n ∈ I := by
      refine ⟨(v.val⁻¹ * n).property, ?_⟩
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      change ((v.val : G)⁻¹ * (n : G)) * t * (((v.val : G)⁻¹ * (n : G))⁻¹) = t
      calc
        _ = (v.val : G)⁻¹ * ((n : G) * t * (n : G)⁻¹) * (v.val : G) := by group
        _ = (v.val : G)⁻¹ * ((v.val : G) * t * (v.val : G)⁻¹) * (v.val : G) := by rw [hv]
        _ = t := by group
    exact ⟨v.val, v.property, v.val⁻¹ * n, hI, mul_inv_cancel_left _ _⟩
  · rintro ⟨v,hv,w,hw,rfl⟩
    exact D.mul_mem (hXD hv) (hID hw)

/-- The same source product is also the join of the literal subgroups. -/
theorem plane_four_normalizer_join (hc : (F.fusion F.plane).ncard = 45)
    (X : Subgroup (planeNormalizer F))
    (hX : X.map (QuotientGroup.mk' (F.plane.subgroupOf (planeNormalizer F))) =
      (planeSextetAction F hc).ker)
    (i : Fin 6) (t : G) (ht : t ∈ planeFour F i) (ht1 : t ≠ 1) :
    (normalizer (planeFour F i : Set G)).subgroupOf (planeNormalizer F) =
      X ⊔ (planeCentralizer F t).subgroupOf (planeNormalizer F) := by
  apply le_antisymm
  · intro n hn
    have he := plane_four_normalizer_product F hc X hX i t ht ht1
    have hm := (Set.ext_iff.mp he n).mp hn
    obtain ⟨v,hv,w,hw,rfl⟩ := hm
    exact mul_mem_sup hv hw
  · exact sup_le (cubic_le_four_normalizer F hc X hX i)
      (point_centralizer_le_four_normalizer F hc i t ht ht1)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
