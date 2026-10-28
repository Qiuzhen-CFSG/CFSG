module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.Control

/-!
# Centralizers of involutions commuting with the actor a

Once C(a) lies in C(z), its involutions can be classified in the actual
local coordinates. Its vector involutions are precisely printed z₁, z₃
and their product, all fused to z₁. Its remaining involutions have local
class a or d. Therefore, if C(d) ≤ N(E), the full centralizer of each
involution in C(a) also lies in N(E).

The omitted printed-z₂ class is crucial: this neighborhood of a suffices
for the dihedral common-involution argument in the assembly module. It
requires no recognition or centralizer bound for printed z₂.
Source: the C(a) coordinates in Z. Janko, *A characterization of the
Mathieu simple groups, I*, J. Algebra 9 (1968), Section 2, printed p.6.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The centralizers of involutions in C(a) are already contained in N(E).
No information about the full centralizer of printed z₂ is required. -/
public theorem l27_a_involution_centralizers_le_normalizer
    (hz3 : IsConj D.z (into D k (z 2)))
    (ha : centralizer ({into D k a} : Set G) ≤ D.centralizer)
    (hd : centralizer ({into D k d} : Set G) ≤ normalizer (E D k : Set G))
    (t : G) (ht : t ∈ centralizer ({into D k a} : Set G)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) ≤ normalizer (E D k : Set G) := by
  let N := normalizer (E D k : Set G)
  let v := k.symm ⟨t, ha ht⟩
  have hv : into D k v = t := congrArg Subtype.val (k.apply_symm_apply _)
  have hvC : v ∈ centralizer ({a} : Set TwistedModel) := by
    apply mem_centralizer_singleton_iff.mpr
    apply into_injective D k
    simpa only [map_mul, hv] using mem_centralizer_singleton_iff.mp ht
  have hv2 : orderOf v = 2 := by
    rw [← orderOf_injective (into D k) (into_injective D k), hv, ht2]
  have transport (r : TwistedModel) (hc : IsConj v r)
      (hCr : centralizer ({into D k r} : Set G) ≤ N) :
      centralizer ({t} : Set G) ≤ N := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    let n : N := ⟨into D k c, centralizer_le_normalizer_E D k (k c).property⟩
    have hnt : (n : G) * t * (n : G)⁻¹ = into D k r := by
      rw [← hv]
      simpa only [n, map_mul, map_inv] using congrArg (into D k) hc
    intro x hx
    have hxc : (n : G) * x * (n : G)⁻¹ ∈ centralizer ({into D k r} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      rw [← hnt]
      simpa only [map_mul, MulAut.conj_apply] using congrArg (MulAut.conj (n : G))
        (mem_centralizer_singleton_iff.mp hx)
    have hmem := N.mul_mem (N.mul_mem (N.inv_mem n.property) (hCr hxc)) n.property
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hmem
  have hvector (r : TwistedModel) (hrE : r ∈ modelE) (hr : IsConj D.z (into D k r))
      (he : v = r) : centralizer ({t} : Set G) ≤ N := by
    rw [he] at hv
    rw [← hv]
    exact l27_marked_conjugate_centralizer_le_normalizer D k
      ⟨into D k r, modelE_map D k ▸ mem_map_of_mem _ hrE⟩ hr
  rcases l27_model_a_involution_classes v hvC hv2 with he | he | he | he | he
  · exact hvector _ (z_mem_modelE 0) (by rw [into_z_zero D k]) he
  · exact hvector _ (z_mem_modelE 2) hz3 he
  · apply hvector _ (modelE.mul_mem (z_mem_modelE 0) (z_mem_modelE 2)) _ he
    apply hz3.trans ((into D k).map_isConj ?_)
    exact isConj_iff.mpr ⟨b⁻¹, by simpa using conjugation_b 2⟩
  · exact transport _ he (ha.trans (centralizer_le_normalizer_E D k))
  · exact transport _ he hd

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
