module
public import Theory.GroupTheory.ElementSubgroupIncidence
public import Mathlib.GroupTheory.Sylow
public import Theory.ElementaryAbelian.Quotient
/-!
# Sylow-local incidence implies ambient fusion control

Suppose elementary subgroups of a fixed order in one Sylow subgroup are
conjugate by the centralizer of each point in their intersection. The same
holds in the ambient group: first move both subgroups into a common Sylow
of the point centralizer, then into the chosen ambient Sylow. Correcting
the conjugator gives normalizer control of element fusion.

Source application: Aschbacher, *Sporadic Groups* (1994), 46.14(4), p.258.
The local incidence hypothesis is discharged there by the two root planes
and their explicit point-fixing interchange.
-/

public noncomputable section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]

private theorem exists_map_le (S : Sylow p G) (A : Subgroup G) (hA : IsPGroup p A) :
    ∃ g : G, A.conjBy g ≤ (S : Subgroup G) := by
  obtain ⟨Q,hQ⟩ := hA.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨g,?_⟩
  rw [←hg]
  exact map_mono hQ

/-- Centralizer conjugacy of elementary subgroups can be checked in one ambient Sylow. -/
theorem elementary_centralizer_conjugacy_of_local (S : Sylow p G)
    (hlocal : ∀ A B : Subgroup G, IsElementaryAbelian p A → IsElementaryAbelian p B →
      A ≤ (S : Subgroup G) → B ≤ (S : Subgroup G) → Nat.card A = n → Nat.card B = n →
      ∀ z : G, z ∈ A → z ∈ B →
        ∃ c ∈ centralizer ({z} : Set G), A.conjBy c = B)
    (A B : Subgroup G) [IsElementaryAbelian p A] [IsElementaryAbelian p B]
    (hA : Nat.card A = n) (hB : Nat.card B = n) (z : G) (hzA : z ∈ A) (hzB : z ∈ B) :
    ∃ c ∈ centralizer ({z} : Set G), A.conjBy c = B := by
  let C := centralizer ({z} : Set G)
  have hAC : A ≤ C := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a,ha⟩ : A) ⟨z,hzA⟩)
  have hBC : B ≤ C := by
    intro b hb
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨b,hb⟩ : B) ⟨z,hzB⟩)
  obtain ⟨Q,hAQ⟩ := ((IsElementaryAbelian.isPGroup p A).comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c,hcQ⟩ := exists_map_le Q (B.subgroupOf C)
    ((IsElementaryAbelian.isPGroup p B).comap_subtype)
  obtain ⟨k,hk⟩ := exists_map_le S ((Q : Subgroup C).map C.subtype)
    (Q.isPGroup'.map C.subtype)
  have hcfix : MulAut.conj (c : G) z = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property)
  have hAS : A.conjBy k ≤ (S : Subgroup G) := by
    rintro _ ⟨a,ha,rfl⟩
    exact hk (mem_map_of_mem _ (mem_map_of_mem C.subtype
      (hAQ (show (⟨a,hAC ha⟩ : C) ∈ A.subgroupOf C from ha))))
  have hBS : B.conjBy (k * (c : G)) ≤ (S : Subgroup G) := by
    rintro _ ⟨b,hb,rfl⟩
    have hq := hcQ (mem_map_of_mem (MulAut.conj c).toMonoidHom
      (show (⟨b,hBC hb⟩ : C) ∈ B.subgroupOf C from hb))
    have ht := hk (mem_map_of_mem (MulAut.conj k).toMonoidHom
      (mem_map_of_mem C.subtype hq))
    change k * ((c : G) * b * (c : G)⁻¹) * k⁻¹ ∈ (S : Subgroup G) at ht
    change (k * (c : G)) * b * (k * (c : G))⁻¹ ∈ (S : Subgroup G)
    simpa only [mul_inv_rev,mul_assoc] using ht
  have hAc : Nat.card (A.conjBy k) = n :=
    (card_map_of_injective (MulAut.conj k).injective).trans hA
  have hBc : Nat.card (B.conjBy (k * (c : G))) = n :=
    (card_map_of_injective (MulAut.conj (k * (c : G))).injective).trans hB
  have hzB' : MulAut.conj k z ∈ B.conjBy (k * (c : G)) := by
    refine mem_map.mpr ⟨z,hzB,?_⟩
    calc
      _ = MulAut.conj k (MulAut.conj (c : G) z) := by simp [MulAut.conj_apply,mul_assoc]
      _ = _ := by rw [hcfix]
  let : IsElementaryAbelian p (A.conjBy k) := IsElementaryAbelian.map _
  let : IsElementaryAbelian p (B.conjBy (k * (c : G))) := IsElementaryAbelian.map _
  obtain ⟨d,hd,he⟩ := hlocal (A.conjBy k) (B.conjBy (k * (c : G)))
    inferInstance inferInstance hAS hBS hAc hBc (MulAut.conj k z)
    (mem_map_of_mem _ hzA) hzB'
  have hdfix : MulAut.conj d (MulAut.conj k z) = MulAut.conj k z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hd)
  refine ⟨(c : G)⁻¹ * k⁻¹ * d * k,?_,?_⟩
  · apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    change MulAut.conj ((c : G)⁻¹ * k⁻¹ * d * k) z = z
    calc
      _ = MulAut.conj (c : G)⁻¹ (MulAut.conj k⁻¹
          (MulAut.conj d (MulAut.conj k z))) := by simp [MulAut.conj_apply,mul_assoc]
      _ = MulAut.conj (c : G)⁻¹ z := by rw [hdfix]; simp [MulAut.conj_apply,mul_assoc]
      _ = z := by
        apply (MulAut.conj (c : G)).injective
        simpa [MulAut.conj_apply,mul_assoc] using hcfix.symm
  · have hh := congrArg (fun W : Subgroup G => (W.conjBy k⁻¹).conjBy (c : G)⁻¹) he
    rw [conjBy_mul B,conjBy_inv,conjBy_inv] at hh
    simpa only [conjBy_mul] using hh

/-- The normalizer controls element fusion once the local incidence condition is proved. -/
theorem elementary_normalizer_controls_fusion_of_local (S : Sylow p G)
    (hlocal : ∀ A B : Subgroup G, IsElementaryAbelian p A → IsElementaryAbelian p B →
      A ≤ (S : Subgroup G) → B ≤ (S : Subgroup G) → Nat.card A = n → Nat.card B = n →
      ∀ z : G, z ∈ A → z ∈ B →
        ∃ c ∈ centralizer ({z} : Set G), A.conjBy c = B)
    (A : Subgroup G) [IsElementaryAbelian p A] (hA : Nat.card A = n)
    (x y : G) (hx : x ∈ A) (hy : y ∈ A) (hxy : IsConj x y) :
    ∃ c ∈ normalizer (A : Set G), MulAut.conj c x = y := by
  apply (element_fusion_iff_centralizer_incidence A x).mpr ?_ y hy hxy
  intro g hg
  let : IsElementaryAbelian p (A.conjBy g) := IsElementaryAbelian.map _
  apply S.elementary_centralizer_conjugacy_of_local hlocal A (A.conjBy g) hA
    ((card_map_of_injective (MulAut.conj g).injective).trans hA) x hx hg
end Sylow
