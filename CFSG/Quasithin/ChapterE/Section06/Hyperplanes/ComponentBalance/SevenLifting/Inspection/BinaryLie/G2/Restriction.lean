module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Restricting the full actor in the G₂ inspection

Transport the embedded ordinary component through the actual common-fixed-group
isomorphism. A central member of the actor defines an action on its own fixed
group; restriction preserves the common fixed subgroup and its component.
No component membership in the larger fixed group is asserted.

Source: the Theorem C inspection in Aschbacher–Smith E.6.18, printed p.252.
These elementary transfers support the induction through smaller G₂ fields.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2

/-- Absence of seven components, allowing also the trivial actor. -/
def NoSevenFixedComponent (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup (MulAut X), IsPGroup 2 P → ∀ L : Subgroup X,
    L ≤ FixedPoints.subgroup P X →
    IsComponent (FixedPoints.subgroup P X) (L.subgroupOf (FixedPoints.subgroup P X)) →
    ¬ IsSeven L

variable {G H : Type*} [Group G] [Group H]

theorem NoSevenFixedComponent.inspection (h : NoSevenFixedComponent G) :
    SevenActionInspection G := by
  intro P hp L hLF hc hs
  exact (h P hp L hLF hc hs).elim

theorem NoSevenFixedComponent.of_equiv (e : G ≃* H) (hi : NoSevenFixedComponent H) :
    NoSevenFixedComponent G := by
  intro P hp L hLF hL hs
  let R := P.map (MulAut.congr e).toMonoidHom
  let C := FixedPoints.subgroup P G
  let D := FixedPoints.subgroup R H
  have fixed_iff (x : G) : e x ∈ D ↔ x ∈ C := by
    constructor
    · intro hx a
      apply e.injective
      change e (a.val x) = e x
      have he := hx ⟨MulAut.congr e a, mem_map_of_mem _ a.property⟩
      change e (a.val (e.symm (e x))) = e x at he
      simpa only [e.symm_apply_apply] using he
    · intro hx r
      obtain ⟨a, ha, he⟩ := r.property
      change r.val (e x) = e x
      rw [← he]
      change e (a (e.symm (e x))) = e x
      rw [e.symm_apply_apply]
      exact congrArg e (hx ⟨a, ha⟩)
  let f : C ≃* D :=
    { toFun := fun x => ⟨e x, (fixed_iff x).mpr x.property⟩
      invFun := fun y => ⟨e.symm y, (fixed_iff (e.symm y)).mp (by
        simpa only [e.apply_symm_apply] using y.property)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y)
      map_mul' := fun x y => Subtype.ext (e.map_mul x y) }
  let J := L.map e.toMonoidHom
  have hJD : J ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact (fixed_iff x).mpr (hLF hx)
  have heq : (L.subgroupOf C).map f.toMonoidHom = J.subgroupOf D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_map_of_mem e.toMonoidHom hx
    · intro hy
      obtain ⟨x, hx, he⟩ := hy
      exact ⟨⟨x, hLF hx⟩, hx, Subtype.ext he⟩
  exact hi R (hp.map _) J hJD (heq ▸ hL.map_equiv f)
    (hs.of_equiv (e.subgroupMap L))

/-- Restrict the whole actor to an invariant overgroup of its common fixed group.
The component is transported through the resulting fixed-group equivalence. -/
theorem not_seven_of_restriction (P : Subgroup (MulAut G)) (hp : IsPGroup 2 P)
    (L H : Subgroup G) (hLH : L ≤ FixedPoints.subgroup P G)
    (hc : IsComponent (FixedPoints.subgroup P G) (L.subgroupOf (FixedPoints.subgroup P G)))
    (hH : FixedPoints.subgroup P G ≤ H)
    (ρ : P →* MulAut H) (hρ : ∀ (a : P) (x : H), (ρ a x : G) = a.val x)
    (hi : NoSevenFixedComponent H) : ¬ IsSeven L := by
  intro hs
  let R := ρ.range
  let C := FixedPoints.subgroup P G
  let D := FixedPoints.subgroup R H
  have fixed_iff (x : H) : x ∈ D ↔ x.val ∈ C := by
    constructor
    · intro hx a
      have he := congrArg Subtype.val (hx ⟨ρ a, a, rfl⟩)
      change (ρ a x : G) = x.val at he
      change a.val x = x.val
      rwa [hρ] at he
    · intro hx r
      obtain ⟨a, he⟩ := r.property
      apply Subtype.ext
      change (r.val x : G) = x.val
      rw [← he, hρ]
      exact hx a
  let e : C ≃* D :=
    { toFun := fun x => ⟨⟨x.val, hH x.property⟩, (fixed_iff _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val, (fixed_iff _).mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let J := L.subgroupOf H
  have hJD : J ≤ D := fun _ hx => (fixed_iff _).mpr (hLH hx)
  have heq : (L.subgroupOf C).map e.toMonoidHom = J.subgroupOf D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  exact hi R (hp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective) J hJD (heq ▸ hc.map_equiv e)
    (hs.of_equiv (subgroupOfEquivOfLe (hLH.trans hH)).symm)

/-- The entire actor preserves the fixed group of each of its central members. -/
def centralFixedRestriction (P : Subgroup (MulAut G)) (a : P)
    (ha : a ∈ center P) : P →* MulAut a.val.fixedSubgroup := by
  have preserves (b : P) (x : a.val.fixedSubgroup) : b.val x ∈ a.val.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    have he := congrArg (fun c : P => c.val x.val) (mem_center_iff.mp ha b)
    change b.val (a.val x.val) = a.val (b.val x.val) at he
    rw [(MulAut.mem_fixedSubgroup _ _).mp x.property] at he
    exact he.symm
  exact {
    toFun := fun b => {
      toFun := fun x => ⟨b.val x, preserves b x⟩
      invFun := fun x => ⟨b⁻¹.val x, preserves b⁻¹ x⟩
      left_inv := fun x => Subtype.ext (b.val.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (b.val.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (b.val.map_mul x y) }
    map_one' := by ext x; rfl
    map_mul' := by intro b c; ext x; rfl }

@[simp] theorem centralFixedRestriction_apply (P : Subgroup (MulAut G)) (a : P)
    (ha : a ∈ center P) (b : P) (x : a.val.fixedSubgroup) :
    (centralFixedRestriction P a ha b x : G) = b.val x := rfl

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2
