module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import Theory.GroupAction.AutomorphismFixedResidualTransport

/-!
# Descent of the entire two-actor through a central involution

A central involution of the actor preserves its own fixed subgroup under
every remaining actor element. Restrict the whole action, form its actual
image, and identify its common fixed subgroup with the original common fixed
subgroup. This transports the embedded ordinary component exactly.

The inner branch needs only a three-rank bound on the derived fixed group:
perfectness embeds the given component there. The outer branch can therefore
use induction on a smaller field, together with the ordinary-component check
to handle a trivial restricted action. These are group-theoretic reductions;
no triality centralizer classification is asserted here.

Source: Aschbacher–Smith, E.6.18, printed p.252, `refs/quasithin.pdf`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.TrialityCase
variable {X : Type*} [Group X]

/-- The actual restriction to the fixed group of a central actor. -/
private noncomputable def restrictedAction (P : Subgroup (MulAut X)) (r : P)
    (hc : ∀ p : P, Commute (p : MulAut X) (r : MulAut X)) :
    P →* MulAut (r : MulAut X).fixedSubgroup where
  toFun p := MulAut.fixedSubgroupEquivOfCompatible (p : MulAut X) r r
    (fun x => DFunLike.congr_fun (hc p).eq x)
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact MulAut.fixedSubgroupEquivOfCompatible_apply _ _ _ _ x
  map_mul' p q := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have hp := MulAut.fixedSubgroupEquivOfCompatible_apply (p : MulAut X) r r
      (fun y => DFunLike.congr_fun (hc p).eq y)
    have hq := MulAut.fixedSubgroupEquivOfCompatible_apply (q : MulAut X) r r
      (fun y => DFunLike.congr_fun (hc q).eq y) x
    have hpq := MulAut.fixedSubgroupEquivOfCompatible_apply ((p * q : P) : MulAut X) r r
      (fun y => DFunLike.congr_fun (hc (p * q)).eq y) x
    exact hpq.trans ((congrArg (p : MulAut X) hq).symm.trans (hp _).symm)

private theorem restrictedAction_apply (P : Subgroup (MulAut X)) (r : P)
    (hc : ∀ p : P, Commute (p : MulAut X) (r : MulAut X))
    (p : P) (x : (r : MulAut X).fixedSubgroup) :
    (restrictedAction P r hc p x : X) = (p : MulAut X) x :=
  MulAut.fixedSubgroupEquivOfCompatible_apply _ _ _ _ x

/-- A component is transported between the two common fixed groups, with its
literal embedding. It is not promoted to a component of the single fixed group. -/
theorem descend_seven_component (P : Subgroup (MulAut X)) (hp : IsPGroup 2 P)
    (r : P) (hc : ∀ p : P, Commute (p : MulAut X) (r : MulAut X))
    (L : Subgroup X) (hLF : L ≤ FixedPoints.subgroup P X)
    (hL : IsComponent (FixedPoints.subgroup P X) (L.subgroupOf (FixedPoints.subgroup P X)))
    (hs : IsSeven L) :
    ∃ (Q : Subgroup (MulAut (r : MulAut X).fixedSubgroup)), IsPGroup 2 Q ∧
      ∃ D : Subgroup (r : MulAut X).fixedSubgroup,
        D ≤ FixedPoints.subgroup Q (r : MulAut X).fixedSubgroup ∧
        IsComponent (FixedPoints.subgroup Q (r : MulAut X).fixedSubgroup)
          (D.subgroupOf (FixedPoints.subgroup Q (r : MulAut X).fixedSubgroup)) ∧
        IsSeven D := by
  let F := (r : MulAut X).fixedSubgroup
  let ρ := restrictedAction P r hc
  let Q := ρ.range
  let C := FixedPoints.subgroup P X
  let D := L.subgroupOf F
  have hCF : C ≤ F := fun x hx => (MulAut.mem_fixedSubgroup _ _).mpr (hx r)
  have hLF' : L ≤ F := hLF.trans hCF
  have fixed_iff (x : F) : x ∈ FixedPoints.subgroup Q F ↔ (x : X) ∈ C := by
    constructor
    · intro hx p
      have h := congrArg Subtype.val (hx ⟨ρ p, ⟨p, rfl⟩⟩)
      change (ρ p x : X) = x at h
      rwa [restrictedAction_apply] at h
    · intro hx q
      obtain ⟨p, hpq⟩ := q.property
      apply Subtype.ext
      change (q.val x : X) = x
      rw [← hpq, restrictedAction_apply]
      exact hx p
  let e : C ≃* FixedPoints.subgroup Q F :=
    { toFun := fun x => ⟨⟨x, hCF x.property⟩, (fixed_iff _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val, (fixed_iff _).mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hD : D ≤ FixedPoints.subgroup Q F := fun x hx => (fixed_iff x).mpr (hLF hx)
  have he : (L.subgroupOf C).map e.toMonoidHom =
      D.subgroupOf (FixedPoints.subgroup Q F) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  exact ⟨Q, hp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective,
    D, hD, he ▸ hL.map_equiv e, hs.of_equiv (subgroupOfEquivOfLe hLF').symm⟩

/-- Combining an inspection with the ordinary-component check also excludes
the trivial actor. This is used after restriction to the smaller field group. -/
theorem no_seven_fixed_of_inspection (hi : SevenActionInspection X)
    (hcomp : ∀ L : Subgroup X, IsComponent X L → ¬ IsSeven L)
    (P : Subgroup (MulAut X)) (hp : IsPGroup 2 P) (L : Subgroup X)
    (hLF : L ≤ FixedPoints.subgroup P X)
    (hL : IsComponent (FixedPoints.subgroup P X) (L.subgroupOf (FixedPoints.subgroup P X)))
    (hs : IsSeven L) : False := by
  have hP := hi P hp L hLF hL hs
  have hF : FixedPoints.subgroup P X = ⊤ := by
    subst P
    apply top_unique
    intro x _ a
    have ha : a.val = 1 := a.property
    change a.val x = x
    rw [ha]
    rfl
  let e : FixedPoints.subgroup P X ≃* X := (MulEquiv.subgroupCongr hF).trans topEquiv
  have he : (L.subgroupOf (FixedPoints.subgroup P X)).map e.toMonoidHom = L := by
    change (L.subgroupOf (FixedPoints.subgroup P X)).map
      (FixedPoints.subgroup P X).subtype = L
    exact map_subgroupOf_eq_of_le hLF
  exact hcomp L (he ▸ hL.map_equiv e) hs

/-- Every nontrivial finite two-actor has an involution central in the actor. -/
theorem exists_central_involution [Finite X] (P : Subgroup (MulAut X))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ r : P, orderOf (r : MulAut X) = 2 ∧
      ∀ p : P, Commute (p : MulAut X) (r : MulAut X) := by
  let : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hne
  let : Nontrivial (center P) := hp.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : center P)
  have hd : 2 ∣ Nat.card (center P) :=
    ((hp.to_subgroup (center P)).dvd_orderOf hz).trans (orderOf_dvd_natCard z)
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2 hd
  refine ⟨r.val, (orderOf_injective (P.subtype.comp (center P).subtype)
    (P.subtype_injective.comp (center P).subtype_injective) r).trans hr, ?_⟩
  intro p
  exact congrArg Subtype.val ((mem_center_iff.mp r.property) p)

/-- Perfectness places the component in the derived group of each individual
fixed subgroup; only this inclusion, not component membership there, is used. -/
theorem no_seven_of_derived_fixed_rank [Finite X]
    (P : Subgroup (MulAut X)) (r : P)
    (hr : primeRank 3 (commutator (r : MulAut X).fixedSubgroup) ≤ 1)
    (L : Subgroup X) (hLF : L ≤ FixedPoints.subgroup P X)
    (hL : IsComponent (FixedPoints.subgroup P X) (L.subgroupOf (FixedPoints.subgroup P X)))
    (hs : IsSeven L) : False := by
  let := hL.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLF).toMonoidHom) (subgroupOfEquivOfLe hLF).surjective
  let f : L →* (r : MulAut X).fixedSubgroup :=
    { toFun := fun x => ⟨x, (MulAut.mem_fixedSubgroup _ _).mpr (hLF x.property r)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hfc : f.range ≤ commutator (r : MulAut X).fixedSubgroup := by
    rw [← Subgroup.commutator_eq_self (H := f.range)]
    exact commutator_mono le_top le_top
  let g := f.codRestrict _ (fun x => hfc ⟨x, rfl⟩)
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (congrArg (fun z => z.val.val) h)
  have hu := (Theory.GroupTheory.primeRank_le_of_injective 3 g hg).trans hr
  have hl := hs.two_le_primeRank
  omega

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.TrialityCase
