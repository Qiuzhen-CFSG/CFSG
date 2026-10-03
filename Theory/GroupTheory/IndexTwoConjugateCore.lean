module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.IndexNormal

/-!
# The conjugate core of an index-two subgroup

Let F normalize K and let N have index two in K. The intersection C of
all F-conjugates of N is contained in N and normalized by both F and K.
Every square in K lies in C; consequently the literal quotient K/C is
an elementary abelian two-group. No finiteness or containment F≤K is
required.

An index-two subgroup is normal and contains every square. Conjugating
these two properties proves K-invariance of every conjugate and puts
all squares in their intersection. Left multiplication permutes the
F-indexed conjugates, which proves F-invariance. The quotient has
exponent dividing two, hence is commutative.

This is the elementary quotient construction for Q_next/Qstar in the
all-central case of Stellmacher (9.4), printed pp.51–52. The graph
specialization and its action are kept outside Theory.
-/

namespace Subgroup
universe u

public theorem index_two_conjugate_core_data
    {G : Type u} [Group G] (F K N : Subgroup G)
    (hFK : F ≤ Subgroup.normalizer K)
    (hNK : N ≤ K) (hindex : N.relIndex K = 2) :
    let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
    C ≤ N ∧ F ≤ Subgroup.normalizer C ∧
      K ≤ Subgroup.normalizer C ∧ (∀ x : G, x ∈ K → x ^ 2 ∈ C) := by
  let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
  have hCN : C ≤ N := by
    intro point hpoint
    have h := Subgroup.mem_map_equiv.mp (Subgroup.mem_iInf.mp hpoint (1 : F))
    change (1 : G)⁻¹ * point * 1 ∈ N at h
    simpa using h
  have hNnormal : (N.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hindex
  have hKN : K ≤ Subgroup.normalizer N :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hNnormal
  have hFC : F ≤ Subgroup.normalizer C := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor point hpoint
    apply Subgroup.mem_iInf.mpr
    intro mover
    apply Subgroup.mem_map_equiv.mpr
    let combined : F := ⟨actor⁻¹ * (mover : G), F.mul_mem (F.inv_mem hactor) mover.property⟩
    have h := Subgroup.mem_map_equiv.mp (Subgroup.mem_iInf.mp hpoint combined)
    change ((actor⁻¹ * (mover : G))⁻¹ * point * (actor⁻¹ * (mover : G))) ∈ N at h
    change (mover : G)⁻¹ * (actor * point * actor⁻¹) * (mover : G) ∈ N
    convert h using 1
    simp only [mul_inv_rev, inv_inv]
    group
  have hKC : K ≤ Subgroup.normalizer C := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor point hpoint
    apply Subgroup.mem_iInf.mpr
    intro mover
    apply Subgroup.mem_map_equiv.mpr
    have hp := Subgroup.mem_map_equiv.mp (Subgroup.mem_iInf.mp hpoint mover)
    change (mover : G)⁻¹ * point * (mover : G) ∈ N at hp
    have ha : (mover : G)⁻¹ * actor * (mover : G) ∈ K := by
      have ha := (Subgroup.mem_normalizer_iff.mp (hFK (F.inv_mem mover.property)) actor).mp hactor
      simpa only [inv_inv] using ha
    have hh := (Subgroup.mem_normalizer_iff.mp (hKN ha) _).mp hp
    change (mover : G)⁻¹ * (actor * point * actor⁻¹) * (mover : G) ∈ N
    convert hh using 1
    group
  have hsquare : ∀ x : G, x ∈ K → x ^ 2 ∈ C := by
    intro point hpoint
    apply Subgroup.mem_iInf.mpr
    intro mover
    apply Subgroup.mem_map_equiv.mpr
    have hp : (mover : G)⁻¹ * point * (mover : G) ∈ K := by
      have hp := (Subgroup.mem_normalizer_iff.mp (hFK (F.inv_mem mover.property)) point).mp hpoint
      simpa only [inv_inv] using hp
    have hh := (N.subgroupOf K).sq_mem_of_index_two hindex
      ⟨(mover : G)⁻¹ * point * (mover : G), hp⟩
    change ((mover : G)⁻¹ * point * (mover : G)) ^ 2 ∈ N at hh
    change (mover : G)⁻¹ * point ^ 2 * (mover : G) ∈ N
    convert hh using 1
    simp only [pow_two]
    group
  exact ⟨hCN,hFC,hKC,hsquare⟩

public theorem index_two_conjugate_core_quotient_elementary
    {G : Type u} [Group G] (F K N : Subgroup G)
    (hFK : F ≤ Subgroup.normalizer K)
    (hNK : N ≤ K) (hindex : N.relIndex K = 2) :
    let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
    ∃ hC : (C.subgroupOf K).Normal,
      let _ := hC
      IsElementaryAbelian 2 (K ⧸ C.subgroupOf K) := by
  let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
  have hdata := index_two_conjugate_core_data F K N hFK hNK hindex
  have hC : (C.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hdata.1.trans hNK)).mpr hdata.2.2.1
  let _ := hC
  have hsq : ∀ z : K ⧸ C.subgroupOf K, z ^ 2 = 1 := by
    intro z
    obtain ⟨point, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf K) z
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (point ^ 2)).mpr
    exact hdata.2.2.2 point point.property
  have hinv (z : K ⧸ C.subgroupOf K) : z⁻¹ = z := by
    exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq z)
  have hW : IsElementaryAbelian 2 (K ⧸ C.subgroupOf K) := {
    toIsMulCommutative := ⟨⟨fun a b => by
      calc
        a * b = (a * b)⁻¹ := (hinv _).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
        _ = b * a := by rw [hinv,hinv]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  exact ⟨hC, hW⟩

end Subgroup
