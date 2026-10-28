module
public import Stellmacher.SectionTen.TenOneDihedralConfiguration
public import Theory.GroupAction.InvertedOddQuadraticCoatomSupport

/-!
# The actual dihedral action and its fixed coatom displacement

For the supplied action of the terminal stabilizer on its literal quotient
module V/Z, the prescribed dihedral extraction yields an odd nontrivial
rotation image and an involutory reflection inverting it. Every retained
coatom actor has displacement fixed pointwise by that rotation image. The
normality and elementary-module instances are exactly the supplied ones.

Descend the action through its exact two-core kernel. The resulting faithful
quotient action preserves the raw rotation order and the reflection. The
coatom centralizes the rotation, so its displacement is rotation invariant;
mutual quadraticity from (7.5) makes the reflection fix that displacement.
Odd inversion then forces the whole rotation to fix it.

This is the action packet used in the order-four support comparison in
Stellmacher (10.1), printed p.63, after assertions (i)--(iii).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionThree
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_dihedral_action_support_data
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (data : TenOneDihedralConfigurationData ctx middle (actor : G) hactor)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [_hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
      QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
        ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
              point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))
    :
    let W := VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')
    let R := (data.raw.F₀.subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map action
    Odd (Nat.card R) ∧ R ≠ ⊥ ∧ _root_.IsInvolution (action actor) ∧
      (∀ r ∈ R, action actor * r * (action actor)⁻¹ = r⁻¹) ∧
      ∀ other : GAt ctx.Γ ctx.criticalPath.a', (other : G) ∈ data.raw.A₀ →
        commutatorAction (Subgroup.zpowers (action other)) W ≤ FixedPoints.subgroup R W := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let U := VAt ctx.Γ ctx.criticalPath.firstStep
  let W := V ⧸ Z.subgroupOf V
  let q : P →* P ⧸ pCore 2 P := QuotientGroup.mk' (pCore 2 P)
  let barAction : P ⧸ pCore 2 P →* MulAut W :=
    QuotientGroup.lift (pCore 2 P) action hkernel.ge
  let rotation := (data.raw.F₀.subgroupOf P).map q
  let R := rotation.map barAction
  have hR : R = (data.raw.F₀.subgroupOf P).map action := by
    rw [show R = rotation.map barAction from rfl, Subgroup.map_map]
    congr 1
  have hodd : Odd (Nat.card R) := by
    have hrotation : Odd (Nat.card rotation) := by
      rw [data.raw.rotation_card]
      exact data.raw.odd_p.pow
    exact hrotation.of_dvd_nat (rotation.card_map_dvd barAction)
  have hinverts : ∀ r ∈ R, action actor * r * (action actor)⁻¹ = r⁻¹ := by
    rintro r ⟨rotationP, hrotation, rfl⟩
    have hh := congrArg barAction (data.raw.reflected rotationP hrotation)
    simp only [map_mul, map_inv] at hh
    change action actor * barAction rotationP * (action actor)⁻¹ = (barAction rotationP)⁻¹ at hh
    exact hh
  have hinjective : Function.Injective barAction :=
    (QuotientGroup.injective_lift_iff (pCore 2 P) action hkernel.ge).mpr hkernel.symm
  have hRne : R ≠ ⊥ := by
    apply (Subgroup.one_lt_card_iff_ne_bot R).mp
    rw [show R = rotation.map barAction from rfl,
      Subgroup.card_map_of_injective hinjective, data.raw.rotation_card]
    exact Nat.one_lt_pow (Nat.ne_of_gt data.raw.n_pos) data.raw.prime_p.one_lt
  have hinvolution : _root_.IsInvolution (action actor) := by
    refine ⟨?_, ?_⟩
    · intro hh
      have heq : barAction (q actor) = barAction 1 := by
        rw [map_one]
        change action actor = 1
        exact hh
      exact data.raw.reflection_involution.1 (hinjective heq)
    · have hh := congrArg barAction data.raw.reflection_involution.2
      simp only [map_pow, map_one] at hh
      change action actor ^ 2 = 1 at hh
      exact hh
  change Odd (Nat.card ((data.raw.F₀.subgroupOf P).map action)) ∧ _
  rw [← hR]
  refine ⟨hodd, hRne, hinvolution, hinverts, ?_⟩
  intro other hother
  have hcommutes : ∀ r ∈ R, Commute (action other) r := by
    rintro r ⟨rotationP, hrotation, rfl⟩
    have hh := congrArg barAction
      (data.raw.A₀_centralizes_rotation (other : G) hother rotationP hrotation)
    simp only [map_mul] at hh
    change action other * barAction rotationP = barAction rotationP * action other at hh
    exact hh
  let Uimage := (U.subgroupOf P).map action
  have hquadratic : commutatorAction₂ Uimage W = ⊥ := by
    apply Subgroup.quotient_conjugation_quadratic_of_double_commutator_le
      P V Z U (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a') data.module_le hN ?_
      action hformula
    have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
    exact (((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb).2.1).le.trans bot_le
  have hotherU : (other : G) ∈ U := data.raw.A₀_le hother
  have hcyclic : Subgroup.zpowers (action other) ≤ Uimage :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem action hotherU)
  have hdisp : commutatorAction (Subgroup.zpowers (action other)) W ≤
      commutatorAction Uimage W := by
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro point ⟨element, vector, rfl⟩
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨element, hcyclic element.property⟩, vector, rfl⟩
  have hfixed : ∀ point ∈ commutatorAction (Subgroup.zpowers (action other)) W,
      action actor • point = point := by
    intro point hpoint
    exact (commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquadratic
      (hdisp hpoint)) ⟨action actor, Subgroup.mem_map_of_mem action hactor⟩
  have hnormal : R ≤ Subgroup.normalizer (Subgroup.zpowers (action other) : Set (MulAut W)) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro r hr
    apply Subgroup.mem_centralizer_iff.mpr
    intro power hpower
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hpower
    exact ((hcommutes r hr).zpow_left n).eq
  have hstable := commutatorAction_isInvariant_of_normalizing_actor
    (V := W) R (Subgroup.zpowers (action other)) hnormal
  have hRfixed := inverted_odd_fixes_invariant_subgroup R hodd (action actor) hinverts
    (commutatorAction (Subgroup.zpowers (action other)) W)
    (fun r hr point hp => (hstable.invariant ⟨r, hr⟩ point).mp hp) hfixed
  intro point hpoint r
  exact hRfixed r r.property point hpoint

end Stellmacher.SectionTen
