module

public import Stellmacher.Recognition.LargeTerminalFiveFixedFour
public import Stellmacher.SectionTen.TenOneLargeCommonIntersectionPlaneImage
public import Theory.GroupTheory.ElementaryEightPlaneFusion

/-!
# Derived involutions and the common elementary eight

The intersection of the first and terminal modules, included in the ambient
group, is an elementary eight inside the first residual's derived subgroup.
Its middle-center plane contains the omega-central involution. The actual
middle-stabilizer image is the full plane stabilizer of order twenty-four.
Thus nonidentity plane points fuse to the omega-central involution, and
points outside the plane have centralizer order divisible by three.

The exported subgroup and its involution alternative provide the local input
to the remaining fusion into the intersection. No orbit census for a different
core order is used. Source: Thompson VI, printed pp.627--630,
the common subgroup containing Z, Z*, K and the three local orbits.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
universe u

/-- The actual common elementary subgroup in the first derived residual. -/
@[expose] public def LargeTerminalContext.derivedIntersection
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) : Subgroup G :=
  (VAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep ⊓
    VAt ctx.terminal.Γ ctx.terminal.criticalPath.a').map
      (ctx.first ⊔ ctx.second).subtype

public theorem LargeTerminalContext.derivedIntersection_le_derived
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ctx.derivedIntersection ≤ DerivedAmbient ctx.firstResidual := by
  rw [ctx.first_residual_structure.2.2.1]
  exact map_mono inf_le_left

private theorem centralizer_card_dvd_of_injective
    {K G : Type*} [Group K] [Group G] (f : K →* G)
    (hf : Function.Injective f) (x : K) :
    Nat.card (centralizer ({x} : Set K)) ∣
      Nat.card (centralizer ({f x} : Set G)) := by
  let j : centralizer ({x} : Set K) →* centralizer ({f x} : Set G) := {
    toFun a := ⟨f a, mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp a.property))⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' a b := Subtype.ext (map_mul f (a : K) (b : K)) }
  exact card_dvd_of_injective j (by
    intro a b h
    exact Subtype.ext (hf (congrArg (fun c : centralizer ({f x} : Set G) => (c : G)) h)))

/-- On the common intersection the desired alternative follows entirely
from the native middle plane action. No order-five or simplicity assumptions
are needed. -/
public theorem LargeTerminalContext.derived_intersection_involution_alternative
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (t : G) (ht : t ∈ ctx.derivedIntersection) (htorder : orderOf t = 2) :
    IsConj z t ∨ 3 ∣ Nat.card (centralizer ({t} : Set G)) := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  let I := VAt Γ cp.firstStep ⊓ VAt Γ cp.a'
  let Z := ZAt Γ middle
  let W := Z.subgroupOf I
  let hnorm := ten_one_common_intersection_normalized tenCtx middle hpath
  let f : GAt Γ middle →* MulAut I :=
    I.normalizerMonoidHom.comp (inclusion hnorm)
  obtain ⟨hElem, hIcard, hfcard, hstable⟩ :=
    ten_one_large_common_intersection_plane_image tenCtx middle hpath ctx.noTransvections
  let _ : IsElementaryAbelian 2 I := hElem
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  have hZI : Z ≤ I := le_inf
    (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hfirst))
    (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hterminal))
  have hWcard : Nat.card W = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZI).toEquiv).trans
      (sectionTenOpeningData tenCtx middle hpath).center_card
  let plane : ElementaryEightPlaneImage I := {
    W := W
    plane_card := hWcard
    J := f.range
    image_card := hfcard
    le_range := by
      rintro j ⟨g, rfl⟩
      exact ⟨inclusion hnorm g, rfl⟩
    stable := by
      intro j x
      have hmap : W.map j.val.toMonoidHom = W := hstable j.val j.property
      constructor
      · intro hx
        have hm : j.val x ∈ W.map j.val.toMonoidHom := hmap.symm ▸ hx
        obtain ⟨y, hy, heq⟩ := hm
        exact j.val.injective heq ▸ hy
      · intro hx
        rw [← hmap]
        exact mem_map_of_mem j.val.toMonoidHom hx }
  have hzmap : z ∈ (ZAt Γ cp.firstStep).map K.subtype := by
    rw [← ctx.first_residual_structure.2.1, ctx.first_residual_center_eq_omegaOneCenter, ← hgen]
    exact mem_zpowers z
  obtain ⟨z0, hz0, rfl⟩ := hzmap
  obtain ⟨t0, ht0, rfl⟩ := ht
  have hzZ : z0 ∈ Z := by
    have hsplit : Z = ZAt Γ cp.firstStep ⊔ ZAt Γ cp.a' :=
      (sectionTenOpeningData tenCtx middle hpath).center_direct_product.1
    rw [hsplit]
    exact mem_sup_left hz0
  let zz : I := ⟨z0, hZI hzZ⟩
  let tt : I := ⟨t0, ht0⟩
  have hz1 : zz ≠ 1 := by
    intro h
    have hh : K.subtype z0 = 1 := congrArg (fun x : I => K.subtype x) h
    rw [hh, orderOf_one] at hz
    norm_num at hz
  have ht1 : tt ≠ 1 := by
    intro h
    have hh : K.subtype t0 = 1 := congrArg (fun x : I => K.subtype x) h
    rw [hh, orderOf_one] at htorder
    norm_num at htorder
  rcases elementaryEight_plane_involution_alternative I hIcard plane zz hzZ hz1 tt ht1 with hc | hd
  · left
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    exact isConj_iff.mpr ⟨(g : G), congrArg K.subtype hg⟩
  · exact Or.inr (hd.trans (centralizer_card_dvd_of_injective K.subtype K.subtype_injective t0))

end Stellmacher.Recognition
