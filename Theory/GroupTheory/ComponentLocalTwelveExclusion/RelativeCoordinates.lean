module
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.SubnormalCoordinates
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.PowerCover

/-!
# Subnormal central coordinates inside a component overgroup

Restrict the component, local subgroup and two-group to the overgroup in
which the component is actually subnormal. The existing component-orbit
coordinates then transport back through the literal subgroup inclusions.
The kernel remains central and the image remains relatively subnormal.
This supplies the full-kernel block transport in Aschbacher–Smith E.6.8.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem IsComponent.relative_subnormal_central_coordinates
    {H L K A : Subgroup G} {P B : Type*} [Group P] [Group B]
    (hL : IsComponent H (L.subgroupOf H)) (hLH : L ≤ H) (hKL : K ≤ L)
    (hAH : A ≤ H) (hA : IsPGroup 2 A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (f : K →* P) (hf : Function.Surjective f) (hcentral : f.ker ≤ center K)
    (hkill : ∀ k : K, inclusion hKL k ∈ center L → f k = 1)
    (hp : IsPPerfect 2 B) (g : B →* (K ⊔ A : Subgroup G))
    (hg : Function.Injective g) (hs : g.range.IsSubnormal) :
    ∃ n : ℕ, ∃ q : B →* (Fin n → P), q.ker ≤ center B ∧ q.range.IsSubnormal := by
  let F := K.subgroupOf H
  let D := A.subgroupOf H
  have hKH : K ≤ H := hKL.trans hLH
  have hFL : F ≤ L.subgroupOf H := subgroupOf_mono H hKL
  have hinvH : D ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv hx
  let eF : F ≃* K := subgroupOfEquivOfLe hKH
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  let fH := f.comp eF.toMonoidHom
  have hcentralH : fH.ker ≤ center F := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply eF.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      mem_center_iff.mp (hcentral hx) (eF y)
  have hkillH (x : F) (hx : inclusion hFL x ∈ center (L.subgroupOf H)) : fH x = 1 := by
    have hxL : eL (inclusion hFL x) ∈ center L := (centerCongr eL ⟨_, hx⟩).property
    exact hkill (eF x) hxL
  let eX : (F ⊔ D : Subgroup H) ≃* (K ⊔ A : Subgroup G) :=
    (MulEquiv.subgroupCongr (subgroupOf_sup hKH hAH).symm).trans
      (subgroupOfEquivOfLe (sup_le hKH hAH))
  let j := eX.symm.toMonoidHom.comp g
  have hjs : j.range.IsSubnormal := by
    rw [MonoidHom.range_comp]
    exact hs.map eX.symm.surjective
  exact ComponentLocalTwelveExclusion.subnormal_central_coordinates hL hFL
    hA.comap_subtype hinvH fH (hf.comp eF.surjective) hcentralH hkillH
    hp j (eX.symm.injective.comp hg) hjs
end Theory.GroupTheory
