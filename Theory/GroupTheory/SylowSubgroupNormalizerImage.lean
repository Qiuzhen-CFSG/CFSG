module
public import Theory.GroupTheory.SylowNormalSupplementProduct
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# Normalizers above a Sylow kernel intersection

Let P lie in a full Sylow S and contain S∩ker(f). Then P is Sylow in
P ker(f). The relative Frattini argument consequently lifts every normalizer
of f(P) to a normalizer of P, up to ker(f). No central or coprime kernel
hypothesis is needed.
Source application: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup
namespace Sylow
variable {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ} [Fact p.Prime]
theorem normalizer_map_of_contains_kernel_intersection (S : Sylow p G)
    (P : Subgroup G) (hPS : P ≤ S) (f : G →* H) (hf : Function.Surjective f)
    (hk : (S : Subgroup G) ⊓ f.ker ≤ P) :
    (normalizer (P : Set G)).map f = normalizer (P.map f : Set H) := by
  let D := f.ker ⊔ P
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal f.ker
  obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := P)
  obtain ⟨A,hA⟩ := IsPGroup.exists_sylow_sup_of_normal_sylow_images
    f.ker P P (S.isPGroup'.to_le hPS) le_sup_right R Q (by
      rw [hR,subgroupOf_map_subtype]
      exact hk) (map_subtype_le _)
  have hfr := le_normalizer_sylow_sup D (normalizer (D : Set G))
    D.le_normalizer le_rfl A
  rw [hA] at hfr
  have hDmap : D.map f = P.map f := by
    rw [Subgroup.map_sup,map_ker_self,bot_sup_eq]
  have hcomap : (P.map f).comap f = D := by rw [comap_map_eq,sup_comm]
  have hn : (normalizer (P.map f : Set H)).comap f = normalizer (D : Set G) := by
    rw [comap_normalizer_eq_of_surjective _ hf,hcomap]
  apply le_antisymm (P.le_normalizer_map f)
  rw [← map_comap_eq_self_of_surjective hf (normalizer (P.map f : Set H)),hn]
  apply (map_mono hfr).trans
  rw [Subgroup.map_sup,hDmap]
  exact sup_le le_rfl (map_mono P.le_normalizer)
end Sylow
