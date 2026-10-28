module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HallJanko.Transport
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.SubnormalCoordinates

/-!
# Subnormal block coordinates in the Hall–Janko local

The full preimage of the invariant second parabolic surjects onto the native
local with central kernel and kills the component center. The general
component-orbit construction therefore sends each actual subnormal short
block into a finite power of the native parabolic, preserving subnormality
and retaining a central kernel. Only the stabilizer of the component acts
on it; the entire supplied Sylow subgroup may permute components.

An actual model equivalence carries all coordinates into the marked full
normalizer of the order-64 radical. These maps allow its native calculation
to be applied to the source blocks without replacing their conjugation modules.
Source: Aschbacher–Smith, 2.3.9(7), printed p.526, and C.1.7, p.123.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HallJanko
open Subgroup Theory.GroupTheory Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Restrict the actual component quotient to the full preimage of P. -/
noncomputable def liftProjection (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) : componentPreimage d P →* P :=
  ((quotientMap d).comp (inclusion (componentPreimage_le d P))).codRestrict P (by
    intro x
    rcases x.property with ⟨y, hy, he⟩
    change (y : G) = x.val at he
    have he' : y = inclusion (componentPreimage_le d P) x := Subtype.ext he
    change quotientMap d y ∈ P at hy
    change quotientMap d (inclusion (componentPreimage_le d P) x) ∈ P
    rw [← he']
    exact hy)

/-- The full preimage maps onto the prescribed native subgroup. -/
theorem liftProjection_surjective (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) : Function.Surjective (liftProjection d P) := by
  intro p
  obtain ⟨l, hl⟩ := quotientMap_surjective d p.val
  refine ⟨⟨l, ⟨l, ?_, rfl⟩⟩, ?_⟩
  · change quotientMap d l ∈ P
    rw [hl]
    exact p.property
  · apply Subtype.ext
    change quotientMap d l = p.val
    exact hl

/-- The covering two-kernel is retained and is central in the lifted local. -/
theorem liftProjection_ker_central (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j2) (P : Subgroup Carrier) :
    (liftProjection d P).ker ≤ center (componentPreimage d P) := by
  intro x hx
  have hk : (⟨x.val, componentPreimage_le d P x.property⟩ : L) ∈ (quotientMap d).ker :=
    by
      change quotientMap d (inclusion (componentPreimage_le d P) x) = 1
      exact congrArg (fun p : P => (p : Carrier)) hx
  rw [quotientMap_ker] at hk
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (congrArg (fun l : L => (l : G))
    (mem_center_iff.mp (twoCore_le_center h hk) ⟨y.val, componentPreimage_le d P y.property⟩))

/-- The full component center is killed by the specified quotient map,
because it is precisely the retained two-core. -/
theorem liftProjection_kills_center (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) (x : componentPreimage d P)
    (hx : inclusion (componentPreimage_le d P) x ∈ center L) :
    liftProjection d P x = 1 := by
  rw [center_eq_twoCore h d, ← quotientMap_ker d] at hx
  apply Subtype.ext
  exact hx

/-- The order-64 radical is retained in the actual native local factor. -/
theorem localGeometry_core_card (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j2) :
    Nat.card (pCore 2 (localGeometry h d).localSubgroup) = 64 := by
  let e := (localGeometry h d).modelIso
  exact (Nat.card_congr (LocalCoreTransport.coreEquiv 2 e).toEquiv).trans BlockGeometry.p₂_core_card

/-- Every source block has central-kernel, relatively subnormal coordinates
in the literal second normalizer, even when S permutes components. -/
theorem block_central_coordinates (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j2)
    (g : LocalGeometry ((S : Subgroup H).map H.subtype) d)
    (B : Subgroup (localOvergroup ((S : Subgroup H).map H.subtype) d g.localSubgroup))
    (hB : ChapterC.IsBlock B) :
    ∃ n : ℕ, ∃ q : B →* (Fin n → Seed.p₂), q.ker ≤ center B ∧ q.range.IsSubnormal := by
  let := h.finite
  let K := componentPreimage d g.localSubgroup
  let A := (S : Subgroup H).map H.subtype
  have hKL : K ≤ L := componentPreimage_le d g.localSubgroup
  have hKH : K ≤ H := hKL.trans h.component_le
  have hAH : A ≤ H := map_subtype_le _
  let f := g.modelIso.toMonoidHom.comp (liftProjection d g.localSubgroup)
  have hf : Function.Surjective f :=
    g.modelIso.surjective.comp (liftProjection_surjective d g.localSubgroup)
  have hcentral : f.ker ≤ center K := by
    intro x hx
    apply liftProjection_ker_central h d g.localSubgroup
    apply g.modelIso.injective
    exact hx.trans (map_one g.modelIso).symm
  have hkill (x : K) (hx : inclusion hKL x ∈ center L) : f x = 1 := by
    change g.modelIso (liftProjection d g.localSubgroup x) = 1
    rw [liftProjection_kills_center h d g.localSubgroup x hx, map_one]
  let F := K.subgroupOf H
  let C := A.subgroupOf H
  have hFL : F ≤ L.subgroupOf H := subgroupOf_mono H hKL
  have hinvH : C ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact g.normalized hx
  let eF : F ≃* K := subgroupOfEquivOfLe hKH
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe h.component_le
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
  let eX : (F ⊔ C : Subgroup H) ≃*
      localOvergroup A d g.localSubgroup :=
    (MulEquiv.subgroupCongr (subgroupOf_sup hKH hAH).symm).trans
      (subgroupOfEquivOfLe (sup_le hKH hAH))
  let j : B →* (F ⊔ C : Subgroup H) := eX.symm.toMonoidHom.comp B.subtype
  have hjs : j.range.IsSubnormal := by
    change (eX.symm.toMonoidHom.comp B.subtype).range.IsSubnormal
    rw [MonoidHom.range_comp, B.range_subtype]
    exact hB.subnormal.map eX.symm.surjective
  have hpA : IsPGroup 2 A := S.isPGroup'.map H.subtype
  exact ComponentLocalTwelveExclusion.subnormal_central_coordinates h.component hFL
    hpA.comap_subtype hinvH fH (hf.comp eF.surjective) hcentralH hkillH
    hB.short.twoPerfect j (eX.symm.injective.comp B.subtype_injective) hjs

end CFSG.Quasithin.Chapter2.ComponentRefinement.HallJanko
