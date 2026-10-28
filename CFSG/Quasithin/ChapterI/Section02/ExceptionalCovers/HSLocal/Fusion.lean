module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Setup
public import Theory.GroupTheory.ElementaryInvolutionCosetFusion

/-!
# The involution-coset deduction in the actual HS cover

The elementary coset theorem applies to Qbar inside the literal quotient
M/E. Its conjugator lifts to Q. Consequently, if j lies in the centralizer
core and E lies in that same core, any involution in jQ is conjugate in K
into that core. This preserves the inclusions and both quotient maps in
the last HS paragraph of Aschbacher–Smith I.2.2(5), p.412 / PDF p.423.

The fixed-subgroup condition is the conclusion needed from B.4.8(2).
Proving the nonsplit module alternative that licenses that application,
the core incidence, and fusion in M/Q remains with the local-cover assembly.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Subgroup Theory.GroupTheory
variable {K : Type*} [Group K] [Finite K]

/-- B.4.8's fixed-point conclusion yields fusion in the actual quotient M/E. -/
theorem coset_fusion_mod_frattini
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (j : M e) (hj : orderOf (QuotientGroup.mk' (E e) j) = 2)
    (hfixed : Qbar e ⊓ centralizer ({QuotientGroup.mk' (E e) j} : Set _) ≤
      ⁅Qbar e, zpowers (QuotientGroup.mk' (E e) j)⁆)
    (x : M e) (hx : x ^ 2 = 1)
    (hcoset : QuotientGroup.mk' (Q e) x = QuotientGroup.mk' (Q e) j) :
    ∃ q : Q e, QuotientGroup.mk' (E e) ((q : M e) * j * (q : M e)⁻¹) =
      QuotientGroup.mk' (E e) x := by
  have hdiff : x * j⁻¹ ∈ Q e := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hcoset
  have hbar : QuotientGroup.mk' (E e) x * (QuotientGroup.mk' (E e) j)⁻¹ ∈
      Qbar e := by
    change _ ∈ (Q e).map (QuotientGroup.mk' (E e))
    simpa only [map_mul, map_inv] using mem_map_of_mem (QuotientGroup.mk' (E e)) hdiff
  obtain ⟨a, ha⟩ := elementary_involution_coset_fusion (Qbar e)
    (QuotientGroup.mk' (E e) j) hj hfixed (QuotientGroup.mk' (E e) x)
    (by rw [← map_pow, hx, map_one]) hbar
  obtain ⟨q, rfl⟩ := coreMap_surjective e a
  change QuotientGroup.mk' (E e) (q : M e) * QuotientGroup.mk' (E e) j *
    (QuotientGroup.mk' (E e) (q : M e))⁻¹ = QuotientGroup.mk' (E e) x at ha
  exact ⟨q, by simpa only [map_mul, map_inv] using ha⟩

/-- Lift quotient fusion to a conjugate lying in the literal centralizer core. -/
theorem conjugate_into_centralizerCore
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (u : K) (j : M e) (hjR : (j : K) ∈ centralizerCore u)
    (hER : E e ≤ (centralizerCore u).subgroupOf (M e))
    (hj : orderOf (QuotientGroup.mk' (E e) j) = 2)
    (hfixed : Qbar e ⊓ centralizer ({QuotientGroup.mk' (E e) j} : Set _) ≤
      ⁅Qbar e, zpowers (QuotientGroup.mk' (E e) j)⁆)
    (x : M e) (hx : x ^ 2 = 1)
    (hcoset : QuotientGroup.mk' (Q e) x = QuotientGroup.mk' (Q e) j) :
    ∃ y ∈ centralizerCore u, IsConj (x : K) y := by
  obtain ⟨q, hq⟩ := coset_fusion_mod_frattini e j hj hfixed x hx hcoset
  let y : M e := (q : M e)⁻¹ * x * q
  have hy : QuotientGroup.mk' (E e) y = QuotientGroup.mk' (E e) j := by
    change QuotientGroup.mk' (E e) ((q : M e)⁻¹ * x * q) = _
    rw [map_mul, map_mul, map_inv, ← hq, map_mul, map_mul, map_inv]
    group
  have hdiff : j⁻¹ * y ∈ E e := QuotientGroup.eq.mp hy.symm
  have hyr : (y : K) ∈ centralizerCore u := by
    have hprod := (centralizerCore u).mul_mem hjR (hER hdiff)
    change (j : K) * ((j : K)⁻¹ * (y : K)) ∈ centralizerCore u at hprod
    simpa only [mul_inv_cancel_left] using hprod
  refine ⟨y, hyr, isConj_iff.mpr ⟨((q : M e) : K)⁻¹, ?_⟩⟩
  simp only [y, coe_mul, coe_inv, inv_inv]

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
