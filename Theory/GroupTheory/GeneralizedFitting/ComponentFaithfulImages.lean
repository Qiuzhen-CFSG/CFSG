module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Recovering components from a faithful family of images

If the restrictions of a separating family of homomorphisms to a subgroup
all have centerless images, that subgroup is centerless. For a component,
every proper normal subgroup is central. Consequently every nontrivial
image in the family is faithful; at least one such image exists. Surjective
ambient maps preserve relative subnormality and give an actual component
isomorphism.

This kernel-control argument uses the component calculus of GLS, volume 2,
Theorem 3.5. The orbit-image application is in the nonprimitive reduction
for Aschbacher–Smith B.1.13, printed p.74 (PDF p.85).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G ι : Type*} [Group G] {H : ι → Type*} [∀ i, Group (H i)]

theorem center_eq_bot_of_separating_homs
    (D : Subgroup G)
    (f : ∀ i, G →* H i)
    (hfaith : ∀ g : G, (∀ i, f i g = 1) → g = 1)
    (hcenter : ∀ i, center (D.map (f i)) = ⊥) : center D = ⊥ := by
  apply bot_unique
  intro z hz
  apply mem_bot.mpr
  apply Subtype.ext
  apply hfaith
  intro i
  let r := (f i).subgroupMap D
  have hr : r z ∈ center (D.map (f i)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := (f i).subgroupMap_surjective D y
    exact (map_mul r y z).symm.trans ((congrArg r (mem_center_iff.mp hz y)).trans
      (map_mul r z y))
  have hr1 : r z = 1 := mem_bot.mp ((hcenter i) ▸ hr)
  exact congrArg Subtype.val hr1

theorem IsComponent.exists_equiv_image_of_separating_homs
    {D : Subgroup G} (hD : IsComponent G D)
    (f : ∀ i, G →* H i) (hf : ∀ i, Function.Surjective (f i))
    (hfaith : ∀ g : G, (∀ i, f i g = 1) → g = 1)
    (hcenter : ∀ i, center (D.map (f i)) = ⊥) :
    ∃ i, IsComponent (H i) (D.map (f i)) ∧ Nonempty (D ≃* D.map (f i)) := by
  let := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  obtain ⟨d, hd⟩ := exists_ne (1 : D)
  obtain ⟨i, hi⟩ : ∃ i, f i (d : G) ≠ 1 := by
    by_contra! hh
    exact hd (Subtype.ext (hfaith d hh))
  have hne : D.map (f i) ≠ ⊥ := by
    intro hb
    exact hi (mem_bot.mp (hb ▸ mem_map_of_mem (f i) d.property))
  have hcomp := (hD.map_surjective (f i) (hf i)).resolve_left hne
  let r := (f i).subgroupMap D
  have hker : r.ker ≤ center D := by
    rcases IsQuasisimple.normal_le_center_or_eq_top r.ker with hc | ht
    · exact hc
    · have hdker : d ∈ r.ker := ht ▸ mem_top d
      exact (hi (congrArg Subtype.val (MonoidHom.mem_ker.mp hdker))).elim
  have hbot : r.ker = ⊥ := bot_unique
    (hker.trans_eq (center_eq_bot_of_separating_homs D f hfaith hcenter))
  exact ⟨i, hcomp, ⟨MulEquiv.ofBijective r
    ⟨(MonoidHom.ker_eq_bot_iff r).mp hbot, (f i).subgroupMap_surjective D⟩⟩⟩
end Theory.GroupTheory
