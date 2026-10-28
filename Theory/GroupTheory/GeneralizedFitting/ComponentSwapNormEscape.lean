module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormAction

/-!
# A simple norm diagonal escapes a proper component intersection

If the norm image of two distinct conjugate components lies in M, each
norm element normalizes M and acts on the first component exactly as its
first coordinate. Thus M intersected with that component is normal there.
For an ordinary simple component, a proper nontrivial intersection excludes
containment of the norm diagonal. No solvability hypothesis on M is used.

Source: the norm-diagonal construction in Aschbacher–Smith E.1.11, p.213,
applied to the original maximal overgroup in the paired E.2.2 reduction.
-/

public section
open Subgroup
namespace Theory.GroupTheory.NormPair
variable {G : Type*} [Group G] {K : Subgroup G} {a : G}

lemma intersection_normal_of_norm_le (hK : IsComponent G K)
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    (M : Subgroup G) (hM : normRange hK hm ≤ M) :
    (M.subgroupOf K).Normal := by
  have hc : K.map (MulAut.conj a).toMonoidHom ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      ((hK.map_conj a).commutator_eq_bot_of_ne hK hm)
  refine ⟨?_⟩
  intro x hx k
  have hn : componentSwapNorm hK hm k ∈ M := hM ⟨k,rfl⟩
  have hcomm : (a*k*a⁻¹)*(x:G) = (x:G)*(a*k*a⁻¹) :=
    (hc (mem_map_of_mem _ k.property) x x.property).symm
  have he : componentSwapNorm hK hm k * (x:G) * (componentSwapNorm hK hm k)⁻¹ =
      (k:G)*x*(k:G)⁻¹ := by
    change ((k:G)*(a*k*a⁻¹)) * x * ((k:G)*(a*k*a⁻¹))⁻¹ = _
    calc
      _ = (k:G)*((a*k*a⁻¹)*x*(a*k*a⁻¹)⁻¹)*(k:G)⁻¹ := by group
      _ = _ := by rw [mul_inv_eq_iff_eq_mul.mpr hcomm]
  change (k:G)*x*(k:G)⁻¹ ∈ M
  rw [← he]
  exact mul_mem (mul_mem hn hx) (inv_mem hn)

lemma norm_not_le_of_proper_nontrivial_intersection
    (hK : IsComponent G K) [IsSimpleGroup K]
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    (M : Subgroup G) (hnb : K ⊓ M ≠ ⊥) (hne : K ⊓ M ≠ K) :
    ¬ normRange hK hm ≤ M := by
  intro hM
  let := intersection_normal_of_norm_le hK hm M hM
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf K) inferInstance with hb | ht
  · apply hnb
    have hh := congrArg (Subgroup.map K.subtype) hb
    simpa only [subgroupOf_map_subtype, Subgroup.map_bot, inf_comm] using hh
  · apply hne
    have hh := congrArg (Subgroup.map K.subtype) ht
    simpa only [subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype, inf_comm] using hh

end Theory.GroupTheory.NormPair
