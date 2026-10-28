module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Sieve
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import Theory.GroupTheory.PCoreCentralQuotient
public import Theory.GroupAction.CentralQuotientFusionGap.SylowFixed
public import Theory.GroupAction.CentralKernelFixedResidual
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Descending the fixed action and recovering an original carrier

A two-group center lies in the fixed Sylow subgroup. An involution fixing
that Sylow subgroup has no central displacement, so fixed points lift from
the central quotient. The induced map on fixed groups has central kernel;
characteristic two therefore descends. Perfectness preserves faithfulness.

Once the quotient sieve yields A₆, the faithful four-group of Sylow fixers
has an outer actor. For that same actor the full six alternatives of 1.1.5
leave A₆, A₇, or their triple covers as actual models of the original group.
The existing original-carrier sieve handles all of these, without assuming
that a central quotient is isomorphic to its covering group.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 1.1.5(3),
printed pp.501–503, and the component paragraph of 15.4.18, pp.1162–1163.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting

variable {L A : Type*} [Group L] [Finite L] [Group.IsPerfect L]
  [Group A] [IsElementaryAbelian 2 A]

/-- Descend the actual action, Sylow subgroup, and characteristic-two fixed groups together. -/
noncomputable def quotientFixedAction (d : FixedAction L A)
    (hZ : center L = pCore 2 L) : FixedAction (L ⧸ center L) A := by
  let q := QuotientGroup.mk' (center L)
  let ρ := (Subgroup.quotientAut (center L)).comp d.action
  refine ⟨d.sylow.mapSurjective (f := q) (QuotientGroup.mk'_surjective _),
    ρ, MulAut.quotient_center_injective.comp d.faithful, ?_, ?_⟩
  · rintro a x ⟨y, hy, rfl⟩
    change (center L).quotientAut (d.action a) (q y) = q y
    rw [Subgroup.quotientAut_apply_mk, d.fixes a y hy]
  · intro a ha
    let α := d.action a
    let β := ρ a
    have heq (x : L) : q (α x) = β (q x) :=
      ((center L).quotientAut_apply_mk α x).symm
    let f := MulAut.fixedSubgroupMap α β q heq
    have hfix : center L ≤ α.fixedSubgroup := by
      intro x hx
      apply (MulAut.mem_fixedSubgroup α x).mpr
      exact d.fixes a x (pCore_isPGroup.le_sylow_of_normal d.sylow (hZ ▸ hx))
    have hsq : α ^ 2 = 1 := by
      rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a, map_one]
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center L) (y : L ⧸ center L)
      have hd : α x * x⁻¹ ∈ center L := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q (α x * x⁻¹) = 1
        rw [map_mul, map_inv, heq, hx, (MulAut.mem_fixedSubgroup β _).mp y.property,
          mul_inv_cancel]
      have hfx := MulAut.CentralQuotientFusionGap.eq_of_central_displacement_of_fixed_sylow
        α d.sylow hsq hfix
        (fun x hx => (MulAut.mem_fixedSubgroup α x).mpr (d.fixes a x hx)) x hd
      exact ⟨⟨x, (MulAut.mem_fixedSubgroup α x).mpr hfx⟩, Subtype.ext hx⟩
    have hk : f.ker ≤ center α.fixedSubgroup := by
      intro x hx
      have hqx : q (x : L) = 1 := congrArg Subtype.val hx
      have hxc : (x : L) ∈ center L := (QuotientGroup.eq_one_iff _).mp hqx
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_center_iff.mp hxc (y : L))
    exact f.centralizer_pCore_le_of_surjective_centralKernel hf hk (d.characteristicTwo a ha)

omit [Finite L] [Group.IsPerfect L] in
/-- The outer alternatives of full 1.1.5 give actual original-component models. -/
theorem model_of_outer_action (α : MulAut L)
    (ha : ModelAction115 L α) (hout : α ∉ (MulAut.conj (G := L)).range) :
    IntrinsicComponentModel L := by
  cases ha with
  | lie _ _ hi => exact (hout hi).elim
  | two_cover _ _ _ hi => exact (hout hi).elim
  | six σ _ h =>
    rcases h with ⟨e, _⟩ | ⟨_, ⟨e⟩, _⟩
    · exact .alternatingSix e
    · exact .tripleCover ((Nat.card_congr e.toEquiv).trans (by simp))
  | seven σ _ h =>
    rcases h with ⟨e, _⟩ | ⟨_, ⟨e⟩, _⟩
    · exact .alternatingSeven e
    · exact .tripleCover ((Nat.card_congr e.toEquiv).trans (by simp))
  | odd _ hi => exact (hout hi).elim
  | sporadic _ _ _ hi => exact (hout hi.1).elim

/-- An A₆ central quotient supplies an outer actor; full 1.1.5 then identifies the original carrier. -/
theorem model_of_quotient_alternating [Finite A]
    (d : FixedAction L A) (hA : Nat.card A = 4)
    (h115 : ∀ a : A, a ≠ 1 → ModelAction115 L (d.action a))
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) : IntrinsicComponentModel L := by
  classical
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  let ρ := (MulAut.centralQuotientAction e).comp d.action
  let P := d.sylow.mapSurjective (f := f)
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hρ : Function.Injective ρ := MulAut.centralQuotientAction_comp_injective e _ d.faithful
  have hfix (a : A) (x : alternatingGroup (Fin 6))
      (hx : x ∈ (P : Subgroup (alternatingGroup (Fin 6)))) : ρ a x = x := by
    obtain ⟨y, hy, rfl⟩ := hx
    change MulAut.centralQuotientAction e (d.action a) (e (QuotientGroup.mk' _ y)) = _
    rw [MulAut.centralQuotientAction_apply, d.fixes a y hy]
    rfl
  have hout := AlternatingSix.ShadowLocal.range_not_le_inner_of_fixes_sylow
    P ρ hρ hA hfix
  have hex : ∃ a : A, ρ a ∉ AlternatingSix.ShadowLocal.inner := by
    by_contra! hn
    apply hout
    rintro _ ⟨a, rfl⟩
    exact hn a
  obtain ⟨a, ha⟩ := hex
  have ha1 : a ≠ 1 := by
    intro he
    apply ha
    simp [he]
  apply model_of_outer_action _ (h115 a ha1)
  rintro ⟨x, hx⟩
  apply ha
  change MulAut.centralQuotientAction e (d.action a) ∈ _
  rw [← hx, MulAut.centralQuotientAction_conj]
  exact ⟨_, rfl⟩

/-- Sieve on the central quotient followed by the original-carrier lifting argument. -/
theorem model_of_quotient_model [Finite A]
    (d : FixedAction L A) (hA : Nat.card A = 4)
    (hZ : center L = pCore 2 L)
    (h115 : ∀ a : A, a ≠ 1 → ModelAction115 L (d.action a))
    (model : IntrinsicComponentModel (L ⧸ center L)) : IntrinsicComponentModel L := by
  obtain ⟨⟨e⟩, _⟩ := (quotientFixedAction d hZ).select_alternatingSix hA model
  exact model_of_quotient_alternating d hA h115 e

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting
