module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.QuotientAction.Center
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The intrinsic cubic quotient and the actual outer action

The published inclusion-induced quotient-center equivalence identifies
Y₀/O₂(Y₀) with Z(Y/O₂(Y)), so the extraspecial configuration gives order three.
This is transported to Y₀ viewed inside H. It is not an assertion about |Y₀*|.

A homomorphism from a theta-generated group to a 3′-group is trivial.
Apply this to conjugation followed by the actual outer quotient of L₀*.
It supplies pointwise inner conjugators without assuming any projection.
Relative C-component membership separately proves nontriviality of L₀*.
The Borel-control theorem combines the earlier cubic quotient with the local
Sylow and solvable-overgroup argument.

The 3′ order of Out(L₀*) remains a model obligation for the whole closure;
no component orbit is discarded. These lemmas do not prove the model reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1122 and 1143–1144.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private lemma theta_hom_eq_one {D : Type*} [Group D] [Finite D]
    (Y : Subgroup G) (hY : theta Y = Y) (hD : ¬ 3 ∣ Nat.card D) (f : Y →* D) : f = 1 := by
  have hy : Y ≤ f.ker.map Y.subtype := by
    conv_lhs => rw [← hY]
    apply (closure_le _).mpr
    intro y hy
    refine ⟨⟨y, (hY ▸ subset_closure hy : y ∈ Y)⟩, ?_, rfl⟩
    apply orderOf_eq_one_iff.mp
    have hd : orderOf (f ⟨y, hY ▸ subset_closure hy⟩) ∣ 3 :=
      (orderOf_map_dvd f _).trans (by simpa only [Subgroup.orderOf_mk] using hy.2.dvd)
    exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_right
      (fun he => hD (he ▸ orderOf_dvd_natCard _))
  ext y
  obtain ⟨z, hz, he⟩ := hy y.property
  have he' : z = y := Subtype.ext he
  exact MonoidHom.mem_ker.mp (he' ▸ hz)

omit [Finite G] in
/-- Every action of a theta-generated group on a group with 3′ outer group is inner. -/
lemma inner_of_outer_three_free {D : Type*} [Group D] [Finite D]
    (Y : Subgroup G) (hY : theta Y = Y) (α : Y →* MulAut D)
    (hout : ¬ 3 ∣ Nat.card (MulAut.Outer D)) :
    ∀ y : Y, ∃ d : D, MulAut.conj d = α y := by
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup D)).comp α
  have hf := theta_hom_eq_one Y hY hout f
  intro y
  exact (QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup D) (α y)).mp
    (DFunLike.congr_fun hf y)

/-- The earlier extraspecial configuration gives the intrinsic cubic quotient of Y₀. -/
lemma residual_quotient_card (M Y V : Subgroup G) (h : ExtraspecialCase M Y V) :
    let Y0 := Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    Nat.card (Y0 ⧸ pCore 2 Y0) = 3 := by
  let _ := h.extraspecial
  exact (Nat.card_congr (residualCenterEquiv Y V h.centralizer_eq).toEquiv).trans
    (IsExtraspecial.center_order_p 3 _)

/-- Transport the intrinsic cubic quotient into H, preserving the two-core convention. -/
lemma residual_quotient_card_in (H M Y V Y0 : Subgroup G)
    (h : ExtraspecialCase M Y V)
    (hY0 : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)))
    (hYH : Y0 ≤ H) :
    Nat.card ((Y0.subgroupOf H) ⧸ pCore 2 (Y0.subgroupOf H)) = 3 := by
  let e := subgroupOfEquivOfLe hYH
  calc
    Nat.card ((Y0.subgroupOf H) ⧸ pCore 2 (Y0.subgroupOf H)) =
        Nat.card (Y0 ⧸ pCore 2 Y0) :=
      Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv
    _ = 3 := hY0 ▸ residual_quotient_card M Y V h

/-- A relative C-component cannot be killed by the two-core quotient. -/
lemma component_star_nontrivial (H L A : Subgroup G)
    (hc : (L.subgroupOf H).IsCComponent) (hLA : L ≤ A) :
    starImage H A ≠ ⊥ := by
  intro hb
  have hLcore : L.subgroupOf H ≤ pCore 2 H := by
    have hmap : starImage H L ≤ starImage H A := map_mono (comap_mono hLA)
    have he : starImage H L = ⊥ := le_bot_iff.mp (hmap.trans_eq hb)
    simpa only [starImage, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using he
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  exact hc.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hLcore))

omit [Finite G] in
/-- The actual component-closure image is normal in H/O₂(H). -/
lemma closure_star_normal (H L Y0 T : Subgroup G)
    (hgen : H = reducedOvergroup L Y0 T)
    (hcomm : L = ⁅L, Y0⁆) (hTY : T ≤ normalizer (Y0 : Set G)) :
    (starImage H (localSpan L T)).Normal := by
  have hn := componentClosure_normal_in_replacement L Y0 T
    (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) hTY
  rw [← hgen] at hn
  exact hn.map _ (QuotientGroup.mk'_surjective _)

/-- Theta generation kills the action on the actual 3′ outer quotient of L₀*. -/
lemma inner_star_of_outer_three_free (H M Y0 L T : Subgroup G)
    (hgen : H = reducedOvergroup L Y0 T)
    (hθ : theta (M ⊓ H) = Y0)
    (hcomm : L = ⁅L, Y0⁆) (hTY : T ≤ normalizer (Y0 : Set G))
    (hout : ¬ 3 ∣ Nat.card (MulAut.Outer (starImage H (localSpan L T)))) :
    ∀ y : starImage H Y0, ∃ l : starImage H (localSpan L T),
      ∀ x : starImage H (localSpan L T),
        (l : H ⧸ pCore 2 H) * x * l⁻¹ = y * x * y⁻¹ := by
  let _ := closure_star_normal H L Y0 T hgen hcomm hTY
  let Y' := Y0.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hYH : Y0 ≤ H := (hθ ▸ theta_le _).trans inf_le_right
  have ht : theta Y' = Y' := by
    apply map_injective H.subtype_injective
    rw [theta_map_of_injective _ H.subtype_injective,
      map_subgroupOf_eq_of_le hYH, ← hθ, theta_idempotent]
  let α : Y' →* MulAut (starImage H (localSpan L T)) :=
    (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut _).comp (q.comp Y'.subtype)
  intro y
  obtain ⟨a, ha, he⟩ := y.property
  obtain ⟨l, hl⟩ := inner_of_outer_three_free Y' ht α hout ⟨a, ha⟩
  refine ⟨l, fun x => ?_⟩
  have heq := congrArg (fun e : MulAut (starImage H (localSpan L T)) => (e x).val) hl
  change (l : H ⧸ pCore 2 H) * x * l⁻¹ = q a * x * (q a)⁻¹ at heq
  rwa [he] at heq

/-- Borel control with the cubic quotient derived from the earlier extraspecial configuration. -/
lemma borel_control_of_extraspecial (H M Y V Y0 L B : Subgroup G) (T : Sylow 2 G)
    [Group.IsSolvable (M ⊓ H : Subgroup G)] [Group.IsSolvable B]
    (hsource : ExtraspecialCase M Y V)
    (hY0 : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)))
    (hgen : H = reducedOvergroup L Y0 T) (hTM : (T : Subgroup G) ≤ M)
    (hθ : theta (M ⊓ H) = Y0) (hN : normalizer (Y0 : Set G) = M)
    (hcomm : L = ⁅L, Y0⁆) (hout : ¬ Y0 ≤ localSpan L T)
    (hB : B = localSpan L T ⊓ normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G))
    (hj : ∀ K : Subgroup G, Group.IsSolvable K → Y0 ⊔ (T : Subgroup G) ≤ K → K ≤ H → K ≤ M ⊓ H) :
    (Y0 ⊔ (T : Subgroup G)) ⊓ localSpan L T = (T : Subgroup G) ⊓ localSpan L T ∧
    Y0 ⊔ (T : Subgroup G) ≤ normalizer (B : Set G) ∧
    B ≤ M ⊓ H ∧ ¬ 3 ∣ Nat.card B ∧ B ≤ normalizer (Y0 : Set G) :=
  replacement_borel_control H M Y0 L B T hgen hTM hθ hN hcomm
    (residual_quotient_card_in H M Y V Y0 hsource hY0 ((hθ ▸ theta_le _).trans inf_le_right))
    hout hB hj

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
