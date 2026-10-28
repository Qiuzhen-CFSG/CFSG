module

public import Theory.GroupTheory.ComponentLocalTwelveExclusion.CentralOrbit
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.Coordinates

/-!
# Order-twelve exclusion through central component orbits

Let L be a component of H, K ≤ L, and A ≤ H a two-group whose stabilizer
of L normalizes K. Suppose K surjects onto a finite characteristic-two group
B with kernel exactly the preimage of Z(L). An intrinsic exclusion of
subnormal two-perfect groups of order twelve in B then excludes centerless
two-perfect subnormal groups of order twelve in K ⊔ A.

Two-perfection puts the tested group in the orbit of K. The orbit has a
surjection onto a finite direct power of B with central kernel, so its
restriction to the centerless tested group is injective. The coordinate
order argument completes the exclusion. All component calculations take
place inside H; neither H nor the tested subgroup is assumed normal in G.
The proof allows A to permute components and allows a trivial covering center.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
E.6.7–8, printed pp.246–248, particularly the Borel paragraph on p.248.
The intrinsic exclusion in B remains an explicit premise for the model owner.
-/

public section

open Subgroup
namespace Theory.GroupTheory.ComponentLocalTwelveExclusion
variable {G : Type*} [Group G] [Finite G]

private theorem injective_comp_of_central_kernel
    {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (hX : center X = ⊥) (j : X →* Y) (hj : Function.Injective j)
    (q : Y →* Z) (hq : q.ker ≤ center Y) : Function.Injective (q.comp j) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hz : x ∈ center X := by
    apply mem_center_iff.mpr
    intro y
    apply hj
    simpa only [map_mul] using mem_center_iff.mp (hq hx) (j y)
  simpa only [hX, mem_bot] using hz

/-- The central orbit quotient transfers an intrinsic order-twelve exclusion
through a local overgroup with two-group actor. -/
theorem no_twelve_in_local_adjoin
    {L K A : Subgroup G} {B X : Type*} [Group B] [Finite B] [Group X]
    (hL : IsComponent G L) (hKL : K ≤ L) (hA : IsPGroup 2 A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (f : K →* B) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center K)
    (hkill : ∀ k : K, inclusion hKL k ∈ center L → f k = 1)
    (hB : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (hex : ∀ E : Subgroup B, E.IsSubnormal → IsPPerfect 2 E → Nat.card E ≠ 12)
    (hX : IsPPerfect 2 X) (hZ : center X = ⊥) (hc : Nat.card X = 12)
    (g : X →* (K ⊔ A : Subgroup G)) (hg : Function.Injective g)
    (hs : g.range.IsSubnormal) : False := by
  obtain ⟨n, q, hq, hqc⟩ := central_power_of_component_orbit hL hKL hinv f hf hcentral hkill
  let P := K ⊔ A
  let N := (componentOrbit K A).subgroupOf P
  have hgr : g.range ≤ N := le_local_orbit_of_isPPerfect K A hA g.range
    (hX.of_surjective g.rangeRestrict g.rangeRestrict_surjective)
  let r : X →* N := g.codRestrict N (fun x => hgr ⟨x, rfl⟩)
  have hr : Function.Injective r := fun x y h => hg (congrArg Subtype.val h)
  have hrs : r.range.IsSubnormal := by
    rw [← MonoidHom.subgroupOf_range_eq_of_le g hgr]
    exact hs.subgroupOf
  let e : N ≃* componentOrbit K A := subgroupOfEquivOfLe (componentOrbit_le_sup K A)
  let j : X →* componentOrbit K A := e.toMonoidHom.comp r
  have hj : Function.Injective j := e.injective.comp hr
  have hjs : j.range.IsSubnormal := by
    rw [MonoidHom.range_comp]
    exact hrs.map e.surjective
  have hqs : (q.comp j).range.IsSubnormal := by
    rw [MonoidHom.range_comp]
    exact hjs.map hq
  exact no_subnormal_embedding_power hB hex hX hZ hc (q.comp j)
    (injective_comp_of_central_kernel hZ j hj q hqc) hqs

end Theory.GroupTheory.ComponentLocalTwelveExclusion

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Transfer the order-twelve exclusion through the central component orbit.
All subnormality is relative to the displayed overgroup; the two-group actor
may permute components, and trivial covering centers are permitted. -/
theorem IsComponent.relative_local_adjoin_no_twelve
    {H L K A : Subgroup G} (hLH : L ≤ H)
    (hL : IsComponent H (L.subgroupOf H)) (hKL : K ≤ L) (hAH : A ≤ H)
    (hA : IsPGroup 2 A) (_hZ : IsPGroup 2 (center L))
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    {B : Type*} [Group B] [Finite B] (f : K →* B) (hf : Function.Surjective f)
    (hker : f.ker = (center L).comap (inclusion hKL))
    (hB : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (hex : ∀ E : Subgroup B, E.IsSubnormal → IsPPerfect 2 E → Nat.card E ≠ 12)
    (D : Subgroup G) (hD : D ≤ K ⊔ A) (hs : (D.subgroupOf (K ⊔ A)).IsSubnormal)
    (hp : IsPPerfect 2 D) (hz : center D = ⊥) (hc : Nat.card D = 12) : False := by
  let F := K.subgroupOf H
  let C := A.subgroupOf H
  have hKH : K ≤ H := hKL.trans hLH
  have hFL : F ≤ L.subgroupOf H := subgroupOf_mono H hKL
  have hinvH : C ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv hx
  let eF : F ≃* K := subgroupOfEquivOfLe hKH
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  let fH : F →* B := f.comp eF.toMonoidHom
  have hcentral : f.ker ≤ center K := by
    intro x hx
    have hxl : inclusion hKL x ∈ center L := by
      rw [hker] at hx
      exact hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact congrArg (fun z : L => (z : G)) (mem_center_iff.mp hxl (inclusion hKL y))
  have hcentralH : fH.ker ≤ center F := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply eF.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      mem_center_iff.mp (hcentral hx) (eF y)
  have hkillH (x : F) (hx : inclusion hFL x ∈ center (L.subgroupOf H)) : fH x = 1 := by
    have hxL : eL (inclusion hFL x) ∈ center L := (centerCongr eL ⟨_, hx⟩).property
    change f (eF x) = 1
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact hxL
  let eP : (F ⊔ C : Subgroup H) ≃* (K ⊔ A : Subgroup G) :=
    (MulEquiv.subgroupCongr (subgroupOf_sup hKH hAH).symm).trans
      (subgroupOfEquivOfLe (sup_le hKH hAH))
  let g : D →* (F ⊔ C : Subgroup H) := eP.symm.toMonoidHom.comp (inclusion hD)
  have hg : Function.Injective g := eP.symm.injective.comp (inclusion_injective hD)
  have hgs : g.range.IsSubnormal := by
    rw [MonoidHom.range_comp, inclusion_range]
    exact hs.map eP.symm.surjective
  exact ComponentLocalTwelveExclusion.no_twelve_in_local_adjoin hL hFL hA.comap_subtype
    hinvH fH (hf.comp eF.surjective) hcentralH hkillH hB hex hp hz hc g hg hgs

end Theory.GroupTheory
