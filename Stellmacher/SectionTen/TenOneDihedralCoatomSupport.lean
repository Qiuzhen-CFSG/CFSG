module
public import Stellmacher.SectionTen.TenOneDihedralConfiguration
public import Theory.GroupAction.InvertedOddQuadraticCoatomSupport

/-!
# The prescribed dihedral coatom fixes the terminal odd support

Retain the actual Section Ten prescribed dihedral data and a supplied action
on the literal terminal module modulo its center, with its exact two-core
kernel. Every element of the retained coatom fixes the action support of the
extracted residual pointwise. All quotient and elementary-module instances
are the supplied ones.

Descend the action through the two-core quotient. The raw extraction makes
the rotation image odd, inverted by the selected actor, and centralized by
all coatom actors. Mutual quadraticity from (7.5) says the selected actor
fixes their displacement. The generic inverted-odd support theorem therefore
makes each coatom actor fix the whole rotation support. Mapping the rotation
back identifies exactly the literal image of the recorded residual.

This is the equality-of-actions step in Stellmacher (10.1), printed p.63,
after exclusion of coatom membership for the middle-core conjugates. It does
not assert the later actor-line normality or either support-case exclusion.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionThree
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_dihedral_coatom_fixes_support
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (data : TenOneDihedralConfigurationData ctx middle (actor : G) hactor)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
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
    (other : GAt ctx.Γ ctx.criticalPath.a')
    (hother : (other : G) ∈ data.raw.A₀) :
    ∀ point ∈ commutatorAction
      ((data.raw.F₀.subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map action)
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')),
      action other point = point := by
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
  have hh := inverted_odd_quadratic_centralizer_fixes_support R hodd
    (action actor) (action other) hinverts hcommutes hfixed
  rwa [hR] at hh

end Stellmacher.SectionTen
