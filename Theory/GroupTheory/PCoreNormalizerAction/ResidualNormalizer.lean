module
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Mathlib.GroupTheory.Index


/-!
# Residual normalizers under a core-quotient action

An element acting trivially on K/O_p(K) sends each subgroup A of K into
A O_p(K). If A is p-perfect and normalized by O_p(K), the p-group supplement
is absorbed and the element normalizes A. This proves normalizer control
without turning quotient commutation into ordinary centralization.

If a subgroup S supplies an entire action image, a normalizer containing
the action kernel has the same index in the whole group and in S. Together
these facts transfer the signed Sylow calculation to the original residual
normalizer in Aschbacher–Smith 14.6.15, printed p.1034.
-/

public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- Triviality on the core quotient normalizes every core-normalized p-perfect subgroup. -/
theorem pCoreNormalizerAction_kernel_normalizes (K A : Subgroup G)
    (hAK : A ≤ K) (hp : IsPPerfect p A)
    (hn : K.pCoreIn p ≤ normalizer (A : Set G)) :
    ((pCoreNormalizerAction p K).ker).map (normalizer (K : Set G)).subtype ≤
      normalizer (A : Set G) := by
  apply le_normalizer_iff.mpr
  rintro x ⟨k,hk,rfl⟩ a ha
  let e := MulAut.conj (k : G)
  have hbound : A.map e.toMonoidHom ≤ A ⊔ K.pCoreIn p := by
    rintro y ⟨b,hb,rfl⟩
    have hc := (pCoreNormalizerAction_eq_one_iff p K k).mp hk ⟨b,hAK hb⟩
    have hc' : (k:G)*b*(k:G)⁻¹/b ∈ K.pCoreIn p := mem_map_of_mem K.subtype hc
    have hh := (A ⊔ K.pCoreIn p).mul_mem (mem_sup_right hc') (mem_sup_left hb)
    change (k:G)*b*(k:G)⁻¹ ∈ A ⊔ K.pCoreIn p
    simpa only [div_mul_cancel] using hh
  have hm : A.map e.toMonoidHom ≤ A :=
    le_of_isPPerfect_of_le_sup_of_normalizes _ _ _
      (hp.of_surjective (e.toMonoidHom.subgroupMap A) (e.toMonoidHom.subgroupMap_surjective A))
      (isPGroup_pCoreIn p K) hn hbound
  exact hm (mem_map_of_mem e.toMonoidHom ha)

/-- If a subgroup already supplies the entire action image, every stabilizer
containing the action kernel has the same index in that subgroup. -/
theorem index_eq_relIndex_of_image_eq_range {D : Type*} [Group D]
    (f : G →* D) (S N : Subgroup G) (hker : f.ker ≤ N)
    (himage : S.map f = f.range) : N.index = N.relIndex S := by
  calc
    N.index = (N.map f).relIndex f.range := by
      rw [←index_comap,comap_map_eq_self hker]
    _ = (N.map f).relIndex (S.map f) := by rw [himage]
    _ = N.relIndex S := by rw [←relIndex_comap,comap_map_eq_self hker]
end Subgroup
