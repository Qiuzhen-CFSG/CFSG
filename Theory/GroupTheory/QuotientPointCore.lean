module
public import Theory.GroupTheory.PCoreImage
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Prime cores in quotient point stabilizers

Suppose J acts by conjugation on U/Z and centralizes Z. The preimage of
any quotient point stabilizer has a commutator homomorphism to Z; its
kernel is the actual point centralizer in J. A prime subgroup normalized
by the ambient point centralizer is therefore subnormal in this preimage.
Its image lies in the quotient stabilizer's prime core. Only relative
normality is used, and no movement of the point by the actor kernel is
required.

Source application: Aschbacher--Smith, proof of 13.8.33, printed p.967,
for the returned image of O₂(H) in the opposite point stabilizer.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G A : Type*} [Group G] [Group A] [Finite G] [Finite A]

/-- A prime subgroup of the ambient point centralizer maps into the prime
core of the literal quotient point stabilizer. -/
theorem point_core_image_le_stabilizer_core (p : ℕ) [Fact p.Prime]
    (J U Z Y : Subgroup G) [(Z.subgroupOf U).Normal]
    (hZJ : Z ≤ J) (hz : J ≤ centralizer (Z : Set G))
    (π : J →* A) (hπ : Function.Surjective π) (hk : IsPGroup p π.ker)
    (ρ : A →* MulAut (U ⧸ Z.subgroupOf U))
    (hn : J ≤ normalizer (U : Set G))
    (hρ : ∀ j : J, ∀ u : U, ρ (π j) (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' (Z.subgroupOf U)
        ⟨(j : G) * (u : G) * (j : G)⁻¹,
          (mem_normalizer_iff.mp (hn j.property) u).mp u.property⟩)
    (u : U) (hp : IsPGroup p Y)
    (hy : Y ≤ centralizer ({(u : G)} : Set G))
    (hny : centralizer ({(u : G)} : Set G) ≤ normalizer (Y : Set G)) :
    (Y.subgroupOf J).map π ≤
      ((MulAction.stabilizer (MulAut (U ⧸ Z.subgroupOf U))
        (QuotientGroup.mk' (Z.subgroupOf U) u)).comap ρ).pCoreIn p := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let S := (MulAction.stabilizer (MulAut (U ⧸ Z.subgroupOf U)) (q u)).comap ρ
  let P := S.comap π
  let C := (centralizer ({(u : G)} : Set G)).subgroupOf J
  have hCP : C ≤ P := by
    intro j hj
    change ρ (π j) (q u) = q u
    rw [hρ]
    congr 1
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hj)
  have hc (j : P) : ⁅((j : J) : G),(u : G)⁆ ∈ Z := by
    let v : U := ⟨((j : J) : G) * (u : G) * ((j : J) : G)⁻¹,
      (mem_normalizer_iff.mp (hn (j : J).property) u).mp u.property⟩
    have he : q v = q u := (hρ (j : J) u).symm.trans j.property
    have hh : q (v * u⁻¹) = 1 := by rw [map_mul,map_inv,he,mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (v * u⁻¹)).mp hh
  let f : P →* Z := {
    toFun j := ⟨⁅((j : J) : G),(u : G)⁆,hc j⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro j k
      apply Subtype.ext
      change ⁅((j : J) : G) * ((k : J) : G),(u : G)⁆ =
        ⁅((j : J) : G),(u : G)⁆ * ⁅((k : J) : G),(u : G)⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have he := mem_centralizer_iff.mp (hz (j : J).property) _ (hc k)
      rw [← he]
      simp only [mul_inv_cancel_right]
      exact mem_centralizer_iff.mp (hz (hZJ (hc j))) _ (hc k) }
  have hker : f.ker = C.subgroupOf P := by
    ext j
    change (⟨⁅((j : J) : G),(u : G)⁆,_⟩ : Z) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm.trans mem_centralizer_singleton_iff.symm
  have hnC : P ≤ normalizer (C : Set J) := by
    apply (normal_subgroupOf_iff_le_normalizer hCP).mp
    rw [← hker]
    infer_instance
  have hYC : Y.subgroupOf J ≤ C := subgroupOf_mono J hy
  have hnY : C ≤ normalizer (Y.subgroupOf J : Set J) := by
    intro j hj
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hny hj) (y : G)
  have hYP : Y.subgroupOf J ≤ P.pCoreIn p :=
    (le_pCoreIn_of_normalizes hp.comap_subtype hYC hnY).trans
      (pCoreIn_mono_of_normalizes hCP hnC)
  have hh := map_mono (f := π) hYP
  rw [map_pCoreIn_of_ker_isPGroup π hk P, map_comap_eq_self_of_surjective hπ S] at hh
  exact hh
end Subgroup
