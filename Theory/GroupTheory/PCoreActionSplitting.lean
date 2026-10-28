module
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Sylow factorization through an action with p-group kernel

If an action has p-group kernel and its actual image has trivial p-core,
its kernel is the p-core. If a Sylow p-subgroup acts through the image of a
subgroup L, each Sylow element can then be written as a core element times
an element of S ∩ L. All subgroups are in the same ambient group.

This is the elementary factorization step in Aschbacher–Smith F.1.12,
printed p.264. Applications must establish the kernel and image conditions
for their actual local action; the lemma is not an automorphism classification.
-/

public section
namespace MonoidHom

/-- Determine the kernel from a p-group kernel and p-core-free actual image. -/
theorem ker_eq_pCore_of_range_core_eq_bot {G A : Type*} [Group G] [Group A]
    (p : ℕ) (f : G →* A) (hk : IsPGroup p f.ker)
    (hi : pCore p f.range = ⊥) : f.ker = pCore p G := by
  have hkle : f.ker ≤ pCore p G := le_sSup ⟨inferInstance, hk⟩
  apply le_antisymm hkle
  have hn : ((pCore p G).map f.rangeRestrict).Normal :=
    (inferInstance : (pCore p G).Normal).map _ f.rangeRestrict_surjective
  have hm : (pCore p G).map f.rangeRestrict ≤ pCore p f.range :=
    le_sSup ⟨hn, pCore_isPGroup.map f.rangeRestrict⟩
  intro g hg
  have hh := hm (Subgroup.mem_map_of_mem f.rangeRestrict hg)
  rw [hi] at hh
  exact congrArg Subtype.val (show f.rangeRestrict g = 1 from hh)

/-- Inner-image containment yields the Sylow/core factorization, once the
actual action has p-group kernel and p-core-free image. -/
theorem sylow_eq_pCore_sup_inf_of_image_le {G A : Type*} [Group G] [Group A]
    [Finite G] {p : ℕ} [Fact p.Prime] (f : G →* A) (S : Sylow p G)
    (L : Subgroup G) (hk : IsPGroup p f.ker) (hi : pCore p f.range = ⊥)
    (himage : (S : Subgroup G).map f ≤ L.map f) :
    (S : Subgroup G) = pCore p G ⊔ ((S : Subgroup G) ⊓ L) := by
  have hker := f.ker_eq_pCore_of_range_core_eq_bot p hk hi
  have hcoreS : pCore p G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  apply le_antisymm
  · intro s hs
    obtain ⟨l, hl, he⟩ := himage (Subgroup.mem_map_of_mem f hs)
    have hc : s * l⁻¹ ∈ pCore p G := by
      rw [← hker]
      change f (s * l⁻¹) = 1
      simp only [map_mul, map_inv, he, mul_inv_cancel]
    have hlS : l ∈ (S : Subgroup G) := by
      have hh := (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hcoreS hc)) hs
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
    have hh := (pCore p G ⊔ ((S : Subgroup G) ⊓ L)).mul_mem
      (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right ⟨hlS, hl⟩)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  · exact sup_le hcoreS inf_le_left

end MonoidHom

namespace Subgroup

/-- The core of an injectively embedded group, viewed in its ambient group. -/
theorem pCoreIn_range_of_injective {G E : Type*} [Group G] [Group E]
    (p : ℕ) (f : G →* E) (hf : Function.Injective f) :
    f.range.pCoreIn p = (pCore p G).map f := by
  let e := MonoidHom.ofInjective hf
  have he : f.range.subtype.comp e.toMonoidHom = f := by
    ext g
    exact MonoidHom.ofInjective_apply hf
  rw [pCoreIn, ← pCore_map_iso p e, map_map, he]

/-- A core contained in a normal subgroup equals that subgroup's embedded core. -/
theorem pCore_eq_map_of_normal_of_le {G : Type*} [Group G] (p : ℕ)
    (L : Subgroup G) [L.Normal] (h : pCore p G ≤ L) :
    pCore p G = L.pCoreIn p := by
  apply le_antisymm
  · have hp : IsPGroup p ((pCore p G).subgroupOf L) := pCore_isPGroup.comap_subtype
    have hc : (pCore p G).subgroupOf L ≤ pCore p L := le_sSup ⟨inferInstance, hp⟩
    have hm := map_mono (f := L.subtype) hc
    rwa [map_subgroupOf_eq_of_le h] at hm
  · change (pCore p L).map L.subtype ≤ pCore p G
    exact le_sSup ⟨inferInstance, pCore_isPGroup.map L.subtype⟩

/-- An actual action whose kernel lies in L identifies both cores in the
ambient group. The core-free image and p-group kernel are separate inputs. -/
theorem pCore_eq_map_of_action_kernel_le {G A : Type*} [Group G] [Group A]
    (p : ℕ) (L : Subgroup G) [L.Normal] (f : G →* A)
    (hk : IsPGroup p f.ker) (hi : pCore p f.range = ⊥) (hL : f.ker ≤ L) :
    pCore p G = L.pCoreIn p :=
  pCore_eq_map_of_normal_of_le p L
    ((f.ker_eq_pCore_of_range_core_eq_bot p hk hi) ▸ hL)

/-- Relative normality and both literal embeddings into E are retained. -/
theorem pCoreIn_eq_of_action_kernel_le {E A : Type*} [Group E] [Group A]
    (p : ℕ) (L H : Subgroup E) (hLH : L ≤ H) [(L.subgroupOf H).Normal]
    (f : H →* A) (hk : IsPGroup p f.ker) (hi : pCore p f.range = ⊥)
    (hL : f.ker ≤ L.subgroupOf H) : H.pCoreIn p = L.pCoreIn p := by
  let e : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  have hc : H.subtype.comp (L.subgroupOf H).subtype =
      L.subtype.comp e.toMonoidHom := rfl
  have hh := congrArg (fun K : Subgroup H => K.map H.subtype)
    (pCore_eq_map_of_action_kernel_le p (L.subgroupOf H) f hk hi hL)
  change H.pCoreIn p = ((pCore p (L.subgroupOf H)).map
    (L.subgroupOf H).subtype).map H.subtype at hh
  rw [map_map, hc, ← map_map, pCore_map_iso] at hh
  exact hh

end Subgroup
