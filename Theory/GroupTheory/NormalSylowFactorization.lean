module
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CharacteristicNormalizerClosure

/-!
# Sylow factors inside a normal Sylow supplement

A factorization M = AD with D normal and a Sylow p-subgroup contained in A
restricts to C whenever M = CT and C is normal. Replace D by its p-residual,
which lies in C, before intersecting the product. This avoids incorrectly
distributing intersection over an arbitrary join.

For a normal supplement N B = G, a chosen Sylow subgroup of B extends to
an ambient Sylow P with P = (P ∩ N) Q. Surjectivity onto G/N proves the
exact product. These two arguments give the full quotient-centralizer
Sylow arrangement in Aschbacher–Smith 5.1.17, printed p.640.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Restrict a factorization to a normal subgroup with p-group quotient. -/
theorem factorization_in_normal_sylow_supplement
    {p : ℕ} [Fact p.Prime] (T : Sylow p G) (C A D : Subgroup G)
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hTA : (T : Subgroup G) ≤ A)
    (hgen : C ⊔ (T : Subgroup G) = A ⊔ D)
    (hMD : C ⊔ (T : Subgroup G) ≤ normalizer (D : Set G)) :
    C = (C ⊓ D) ⊔ (C ⊓ A) := by
  let M := C ⊔ (T : Subgroup G)
  have hCM : C ≤ M := le_sup_left
  have hTM : (T : Subgroup G) ≤ M := le_sup_right
  have hDM : D ≤ M := (show D ≤ A ⊔ D from le_sup_right).trans hgen.ge
  let CN := C.subgroupOf M
  let : CN.Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hTC)
  have hcover : CN ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    rw [← subgroupOf_sup hCM hTM,subgroupOf_self]
  have hq : IsPGroup p (M ⧸ CN) :=
    isPGroup_quotient_of_sup_eq_top CN ((T : Subgroup G).subgroupOf M)
      T.isPGroup'.comap_subtype hcover
  have hresM : pResidual p M ≤ CN := (pResidual_le_iff_isPGroup_quotient p CN).mpr hq
  let R := (pResidual p D).map D.subtype
  have hRC : R ≤ C := by
    rintro x ⟨d,hd,rfl⟩
    have hh := hresM (map_pResidual_le p (inclusion hDM)
      (mem_map_of_mem (inclusion hDM) hd))
    exact hh
  have hDR : D ≤ R ⊔ (T : Subgroup G) :=
    le_embedded_pResidual_sup_sylow_of_normalizes T D (hTM.trans hMD)
  have hRD : R ≤ D := map_subtype_le _
  have hMR : M ≤ A ⊔ R := by
    change C ⊔ (T : Subgroup G) ≤ A ⊔ R
    rw [hgen]
    exact sup_le le_sup_left (hDR.trans (sup_le le_sup_right (hTA.trans le_sup_left)))
  have hAR : A ≤ normalizer (R : Set G) :=
    (((show A ≤ A ⊔ D from le_sup_left).trans hgen.ge).trans hMD).trans
      (normalizer_le_normalizer_characteristic_image D (pResidual p D))
  apply le_antisymm _ (sup_le inf_le_left inf_le_left)
  intro c hc
  have hm : c ∈ (A : Set G) * (R : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right A R hAR]
    exact hMR (hCM hc)
  obtain ⟨a,ha,r,hr,har⟩ := hm
  have haC : a ∈ C := by
    simpa only [←har,mul_inv_cancel_right] using C.mul_mem hc (C.inv_mem (hRC hr))
  rw [←har]
  exact ((C ⊓ D) ⊔ (C ⊓ A)).mul_mem (mem_sup_right ⟨haC,ha⟩)
    (mem_sup_left ⟨hRC hr,hRD hr⟩)

/-- A chosen Sylow of a normal supplement extends with the exact kernel product. -/
theorem Sylow.exists_extension_eq_inf_sup
    {p : ℕ} [Fact p.Prime] (N B : Subgroup G) [N.Normal]
    (hgen : N ⊔ B = ⊤) (Q : Sylow p B) :
    ∃ P : Sylow p G,
      (Q : Subgroup B).map B.subtype ≤ (P : Subgroup G) ∧
      (P : Subgroup G) = (P : Subgroup G) ⊓ N ⊔ (Q : Subgroup B).map B.subtype := by
  let q := QuotientGroup.mk' N
  let f := q.comp B.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have hh := congrArg (map q) hgen
    simpa only [f,q,map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N),
      MonoidHom.range_comp,range_subtype] using hh
  obtain ⟨P,hQP⟩ := (Q.isPGroup'.map B.subtype).exists_le_sylow
  have himage : (P : Subgroup G).map q = (Q : Subgroup B).map f := by
    have hle : (Q : Subgroup B).map f ≤ (P : Subgroup G).map q := by
      rw [← map_map]
      exact map_mono hQP
    exact (Q.mapSurjective hf).is_maximal' (P.isPGroup'.map q) hle
  have hPN : (P : Subgroup G) ≤ N ⊔ (Q : Subgroup B).map B.subtype := by
    have hh := le_comap_map q (P : Subgroup G)
    rw [himage,←map_map,comap_map_eq,QuotientGroup.ker_mk',sup_comm] at hh
    exact hh
  refine ⟨P,hQP,le_antisymm ?_ (sup_le inf_le_left hQP)⟩
  intro x hx
  obtain ⟨a,ha,b,hb,hab⟩ := mem_sup_of_normal_left.mp (hPN hx)
  have haP : a ∈ (P : Subgroup G) := by
    simpa only [←hab,mul_inv_cancel_right] using P.mul_mem hx (P.inv_mem (hQP hb))
  rw [←hab]
  exact mul_mem_sup ⟨haP,ha⟩ hb
end Subgroup
