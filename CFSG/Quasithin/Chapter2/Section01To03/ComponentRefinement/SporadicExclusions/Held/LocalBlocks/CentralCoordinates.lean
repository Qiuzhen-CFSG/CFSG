module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.LocalGeometry
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.SubnormalCoordinates
public import Theory.SpecificGroups.Held.LocalPairs.Faithfulness

/-!
# Central coordinates for blocks in the actual Held locals

Restrict the published component map, retaining its central two-kernel.
The checked degree-2058 carrier is centerless, so this map kills the entire
component center. The component-orbit quotient then maps every short
subnormal block into a finite power of the corresponding native local,
with central kernel and subnormal image.

All component normality is relative to H. Only the stabilizer in S acts on
the chosen component; S may permute its conjugates. No simplicity or order
certification for Held is needed. Source: Aschbacher–Smith 2.3.9(7), printed
p.526, and C.1.7, printed p.123.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The kernel of the published component projection is central, with its
whole two-core retained. -/
theorem heldComponentMap_ker_central (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (heldComponentMap h d i).ker ≤ center (heldComponentLocal h d i) := by
  intro x hx
  have hk : (⟨x.val, heldComponentLocal_le h d i x.property⟩ : L) ∈ (modelMap d).ker :=
    congrArg (fun p : heldModelLocal h d i => (p : Held.He)) hx
  rw [modelMap_ker] at hk
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (congrArg (fun l : L => (l : G))
    (mem_center_iff.mp (twoCore_le_center h d hk)
      ⟨y.val, heldComponentLocal_le h d i y.property⟩))

/-- The actual centerless Held quotient kills the whole component center. -/
theorem heldComponentMap_kills_center (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool)
    (x : heldComponentLocal h d i)
    (hx : inclusion (heldComponentLocal_le h d i) x ∈ center L) :
    heldComponentMap h d i x = 1 := by
  have hc : modelMap d (inclusion (heldComponentLocal_le h d i) x) ∈
      center Held.He := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨l, rfl⟩ := modelMap_surjective d y
    simpa only [map_mul] using congrArg (modelMap d) (mem_center_iff.mp hx l)
  apply Subtype.ext
  exact mem_bot.mp (Held.LocalPairs.center_eq_bot ▸ hc)

/-- Every actual block has central-kernel coordinates in the named native
local, with relative subnormality preserved in the full direct power. -/
theorem held_block_central_coordinates (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool)
    (B : Subgroup (heldLocal h d i))
    (hB : ChapterC.IsBlock B) :
    ∃ n : ℕ, ∃ q : B →* (Fin n → heldModelLocal h d i), q.ker ≤ center B ∧ q.range.IsSubnormal := by
  let := h.finite
  let K := heldComponentLocal h d i
  let A := (S : Subgroup H).map H.subtype
  have hKL : K ≤ L := heldComponentLocal_le h d i
  have hKH : K ≤ H := hKL.trans h.component_le
  have hAH : A ≤ H := map_subtype_le _
  let F := K.subgroupOf H
  let C := A.subgroupOf H
  have hFL : F ≤ L.subgroupOf H := subgroupOf_mono H hKL
  have hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G) :=
    heldComponentLocal_normalized h d i
  have hinvH : C ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv hx
  let eF : F ≃* K := subgroupOfEquivOfLe hKH
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe h.component_le
  let fH := (heldComponentMap h d i).comp eF.toMonoidHom
  have hcentralH : fH.ker ≤ center F := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply eF.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      mem_center_iff.mp (heldComponentMap_ker_central h d i hx) (eF y)
  have hkillH (x : F) (hx : inclusion hFL x ∈ center (L.subgroupOf H)) : fH x = 1 := by
    have hxL : eL (inclusion hFL x) ∈ center L := (centerCongr eL ⟨_, hx⟩).property
    exact heldComponentMap_kills_center h d i (eF x) hxL
  let eX : (F ⊔ C : Subgroup H) ≃*
      heldLocal h d i :=
    (MulEquiv.subgroupCongr (subgroupOf_sup hKH hAH).symm).trans
      (subgroupOfEquivOfLe (sup_le hKH hAH))
  let g : B →* (F ⊔ C : Subgroup H) := eX.symm.toMonoidHom.comp B.subtype
  have hgs : g.range.IsSubnormal := by
    change (eX.symm.toMonoidHom.comp B.subtype).range.IsSubnormal
    rw [MonoidHom.range_comp, B.range_subtype]
    exact hB.subnormal.map eX.symm.surjective
  have hpA : IsPGroup 2 A := S.isPGroup'.map H.subtype
  exact ComponentLocalTwelveExclusion.subnormal_central_coordinates h.component hFL hpA.comap_subtype hinvH fH
    ((heldComponentMap_surjective h d i).comp eF.surjective) hcentralH hkillH
    hB.short.twoPerfect g (eX.symm.injective.comp B.subtype_injective) hgs
end CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

end
