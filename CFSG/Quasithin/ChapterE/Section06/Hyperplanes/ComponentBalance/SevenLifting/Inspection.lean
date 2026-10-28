module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Rank

/-!
# The outstanding Theorem C inspection in E.6.18

For a normal quasisimple subgroup J, conjugation by P gives its actual induced
two-subgroup of Aut(J). The inspection must show that this action is trivial
if a component of C_G(P) contained in J is A₇ or its perfect central three-cover.
Restriction makes that component an ordinary component of C_J(P).
The final theorem below constructs the action image, identifies its fixed
subgroup with C_J(P), and transports the intrinsic component through it.

This interface retains the embedded subgroup, intrinsic component membership,
and the entire two-subgroup P. It assumes neither that P centralizes J nor
that the component equals J. `SevenModelInspection` is an outstanding proof
obligation, not a source theorem. Its model proofs must supply the concrete
Theorem C quotient isomorphisms, relative normality and quasisimplicity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252, the inspection following I.3.1(3); Theorem C, printed p.33.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
variable {G : Type*} [Group G]

/-- Triviality of the induced two-action in the presence of a seven component.
The model-specific theorems supply normality and the actual model of J/Z(J). -/
def SevenModelInspection (J : Subgroup G) : Prop :=
  ∀ P L : Subgroup G, IsPGroup 2 P →
    CentralizerComponent P L → L ≤ J → IsSeven L →
      J ≤ centralizer (P : Set G)

/-- The intrinsic model obligation for the actual two-subgroup of Aut(X).
The ordinary component is computed inside the common fixed subgroup. -/
def SevenActionInspection (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup (MulAut X), IsPGroup 2 P → ∀ L : Subgroup X,
    L ≤ FixedPoints.subgroup P X →
    IsComponent (FixedPoints.subgroup P X) (L.subgroupOf (FixedPoints.subgroup P X)) →
    IsSeven L → P = ⊥

/-- Transfer the intrinsic automorphism inspection to a relatively normal
subgroup. The action image and both centralizer-component identifications are
constructed explicitly; no ambient normality beyond J's stated normality is used. -/
theorem SevenActionInspection.modelInspection (J : Subgroup G) [J.Normal] (hi : SevenActionInspection J) :
    SevenModelInspection J := by
  intro P L hp hL hLJ hs
  let f : G →* MulAut J := MulAut.conjNormal
  let R := P.map f
  let C := centralizer (P : Set G)
  let F := FixedPoints.subgroup R J
  let D := L.subgroupOf J
  have fixed_iff (j : J) : j ∈ F ↔ (j : G) ∈ C := by
    constructor
    · intro hj p hp
      have he := congrArg Subtype.val (hj ⟨f p, mem_map_of_mem f hp⟩)
      change p * (j : G) * p⁻¹ = (j : G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hj r
      obtain ⟨p, hp, he⟩ := r.property
      apply Subtype.ext
      change (r.val j : G) = j
      rw [← he]
      change p * (j : G) * p⁻¹ = (j : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hj p hp)
  let e : (J.subgroupOf C) ≃* F :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩,
        (fixed_iff ⟨x.val.val, x.property⟩).mpr x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, (fixed_iff x.val).mp x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hDF : D ≤ F := fun _ hx => (fixed_iff _).mpr (hL.1 hx)
  have hc := hL.2.subgroupOf (show L.subgroupOf C ≤ J.subgroupOf C from fun _ hx => hLJ hx)
  have he : ((L.subgroupOf C).subgroupOf (J.subgroupOf C)).map e.toMonoidHom =
      D.subgroupOf F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  have hr : R = ⊥ := hi R (hp.map f) D hDF (he ▸ hc.map_equiv e)
    (hs.of_equiv (subgroupOfEquivOfLe hLJ).symm)
  intro j hj p hp
  have hf : f p = 1 := by
    have hm : f p ∈ R := mem_map_of_mem f hp
    rwa [hr, mem_bot] at hm
  have he := congrArg (fun a : MulAut J => (a ⟨j, hj⟩ : G)) hf
  change p * j * p⁻¹ = j at he
  exact mul_inv_eq_iff_eq_mul.mp he


end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
