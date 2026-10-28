module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.Outside
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.MarkedGeometry

/-!
# The extraspecial branch of the residual involution calculation

The coordinates module proves the actual H-transitivity of the pure and
mixed singular classes in U/Z and lifts both classes into U. The outside
module moves involutions of the literal two-residual K into a*fixedLift.
The conditional assembly here identifies the two noncentral H-orbits and
includes the central involution once the square map and local markings
have been established.

The source-facing assembly at the end takes the genuine conclusions through
15.3.59, the earlier V-geometry, and the actual natural/dual recognition as
explicit inputs. It then constructs the marked square geometry, chooses an
actual involution in `V − U`, and discharges the inside, outside, fixed-lift,
and local-product premises used by the parent residual assembly. The final
residual cover belongs to the parent `ResidualOrbits` module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.58–59 and the first paragraph proving 15.3.61(2), pp.1148–1150.
-/

public section

open Subgroup BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open CFSG.Quasithin.Chapter15.Section03.FusionCore
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial
variable {G : Type*} [Group G] {T Z ZS V M V₁ : Subgroup G} {t z v : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

variable (d : RecognizedAction T Z ZS V t)

private theorem involution_coordinates (m : MarkedGeometry d z v)
    (x : closureU Z ZS) (hx : orderOf (x : G) = 2) (hxZ : (x : G) ∉ Z) :
    IsPure (d.coordinates (QuotientGroup.mk' _ x)).toAdd ∨
      IsSingularDiagonal (d.coordinates (QuotientGroup.mk' _ x)).toAdd := by
  have hq := (m.square_zero x).mp (hx ▸ pow_orderOf_eq_one (x : G))
  have hn : (d.coordinates (QuotientGroup.mk' _ x)).toAdd ≠ 0 := by
    intro he
    have hh : QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x = 1 :=
      d.coordinates.injective (he.trans (map_one d.coordinates).symm)
    exact hxZ ((QuotientGroup.eq_one_iff x).mp hh)
  by_cases h₁ : (d.coordinates (QuotientGroup.mk' _ x)).toAdd.1 = 0
  · exact Or.inl (Or.inr ⟨h₁, fun h₂ => hn (Prod.ext h₁ h₂)⟩)
  by_cases h₂ : (d.coordinates (QuotientGroup.mk' _ x)).toAdd.2 = 0
  · exact Or.inl (Or.inl ⟨h₁, h₂⟩)
  exact Or.inr ⟨h₁, h₂, hq⟩

variable [IsExtraspecial 2 (closureU Z ZS)]
variable (hZS : ZS ≤ centralizerH Z)
variable (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
include hZS hcenter

/-- A single geometrically marked pure lift identifies the entire pure orbit. -/
theorem pure_fusion (m : MarkedGeometry d z v) (x : closureU Z ZS)
    (hx : IsPure (d.coordinates (QuotientGroup.mk' _ x)).toAdd) : IsConj (x : G) z :=
  (conjugateBy_of_isPure d hZS hcenter x m.pureSeed hx m.pureSeed_pure).isConj.trans
    m.pureSeed_fusion

/-- The union of the two punctured natural-summand preimages fuses to z. -/
theorem preimages_fusion (m : MarkedGeometry d z v) (x : G)
    (hx : x ∈ naturalPreimage d ∨ x ∈ dualPreimage d) (hxZ : x ∉ Z) : IsConj x z := by
  have hxU : x ∈ closureU Z ZS := hx.elim (fun h => naturalPreimage_le d h)
    (fun h => dualPreimage_le d h)
  exact pure_fusion d hZS hcenter m ⟨x, hxU⟩
    ((isPure_iff_mem_preimages d ⟨x, hxU⟩ hxZ).mpr hx)

/-- The other singular class is the actual H-orbit of the marked v. -/
theorem mixed_fusion (m : MarkedGeometry d z v) (x : closureU Z ZS)
    (hx : IsSingularDiagonal (d.coordinates (QuotientGroup.mk' _ x)).toAdd) :
    ConjugateBy (centralizerH Z) (x : G) v :=
  conjugateBy_of_singularDiagonal d hZS hcenter x ⟨v, m.v_mem⟩ hx m.v_mixed

/-- Exact two-orbit classification, conditional on the separately owned square
and marking calculation and the earlier ambient separation of z and v. -/
theorem noncentral_involution_orbit_iff (m : MarkedGeometry d z v) (hsep : ¬ IsConj z v)
    (x y : closureU Z ZS) (hx : orderOf (x : G) = 2) (hy : orderOf (y : G) = 2)
    (hxZ : (x : G) ∉ Z) (hyZ : (y : G) ∉ Z) :
    ConjugateBy (centralizerH Z) (x : G) (y : G) ↔
      (IsPure (d.coordinates (QuotientGroup.mk' _ x)).toAdd ∧
        IsPure (d.coordinates (QuotientGroup.mk' _ y)).toAdd) ∨
      (IsSingularDiagonal (d.coordinates (QuotientGroup.mk' _ x)).toAdd ∧
        IsSingularDiagonal (d.coordinates (QuotientGroup.mk' _ y)).toAdd) := by
  constructor
  · intro h
    rcases involution_coordinates d m x hx hxZ with hx | hx <;>
      rcases involution_coordinates d m y hy hyZ with hy | hy
    · exact Or.inl ⟨hx, hy⟩
    · exact (hsep ((pure_fusion d hZS hcenter m x hx).symm.trans
        (h.isConj.trans (mixed_fusion d hZS hcenter m y hy).isConj))).elim
    · exact (hsep ((pure_fusion d hZS hcenter m y hy).symm.trans
        (h.isConj.symm.trans (mixed_fusion d hZS hcenter m x hx).isConj))).elim
    · exact Or.inr ⟨hx, hy⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact conjugateBy_of_isPure d hZS hcenter x y hx hy
    · exact conjugateBy_of_singularDiagonal d hZS hcenter x y hx hy

/-- Include the central involution, using the actual marking Z=⟨z⟩. -/
theorem inside_cover_of_markedGeometry (m : MarkedGeometry d z v)
    (hz : orderOf z = 2) (hZ : zpowers z = Z) :
    ∀ x ∈ closureU Z ZS, orderOf x = 2 → IsConj x z ∨ IsConj x v := by
  intro x hx hx2
  by_cases hxZ : x ∈ Z
  · have hc : Nat.card Z = 2 := by rw [← hZ, Nat.card_zpowers, hz]
    have hzZ : z ∈ Z := hZ ▸ mem_zpowers z
    obtain ⟨_, _, hall⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hc
    have hx1 : (⟨x, hxZ⟩ : Z) ≠ 1 := by
      intro h
      have he : x = 1 := congrArg Subtype.val h
      simp [he] at hx2
    have hz1 : (⟨z, hzZ⟩ : Z) ≠ 1 := by
      intro h
      have he : z = 1 := congrArg Subtype.val h
      simp [he] at hz
    have he : x = z := congrArg Subtype.val ((hall _ hx1).trans (hall _ hz1).symm)
    exact Or.inl (he ▸ IsConj.refl x)
  · rcases involution_coordinates d m ⟨x, hx⟩ hx2 hxZ with hp | hm
    · exact Or.inl (pure_fusion d hZS hcenter m ⟨x, hx⟩ hp)
    · exact Or.inr (mixed_fusion d hZS hcenter m ⟨x, hx⟩ hm).isConj

/-! The following theorem is the source-facing boundary of this branch.  The
first block of hypotheses is exactly the earlier geometry through 15.3.59;
the remaining numerical and containment clauses are the local facts used in
the first paragraph proving 15.3.61(2).  They are kept explicit so that no
later involution-orbit conclusion is hidden in an input record. -/

set_option linter.style.haveILetI false in
omit [IsExtraspecial 2 (closureU Z ZS)] hZS hcenter in
theorem exists_source_premises [Finite G] [IsElementaryAbelian 2 V]
    [((closureU Z ZS).subgroupOf (residualK Z)).Normal]
    (d : RecognizedAction T Z ZS V t) (h : EarlierGeometry d M V₁ z v)
    (hZV : Z ≤ V) (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8)
    (hV : Nat.card V = 16)
    (hUV : closureU Z ZS ≤ normalizer (V : Set G))
    (himage : Nat.card (FixedLift.actionOnV hUV).range = 4)
    (hVK : V ≤ residualK Z) (hVU : ¬ V ≤ closureU Z ZS)
    (hz : orderOf z = 2) (hZ : zpowers z = Z)
    (hsep : ¬ IsConj z v) :
    ∃ a : centralizerH Z,
      (a : G) ∈ V ∧ (a : G) ∉ closureU Z ZS ∧ orderOf (a : G) = 2 ∧
      ∃ _m : MarkedGeometry d z v,
        (∀ x ∈ closureU Z ZS, orderOf x = 2 → IsConj x z ∨ IsConj x v) ∧
        (∀ x y : closureU Z ZS, orderOf (x : G) = 2 → orderOf (y : G) = 2 →
          (x : G) ∉ Z → (y : G) ∉ Z →
          (ConjugateBy (centralizerH Z) (x : G) (y : G) ↔
            (IsPure (d.coordinates (QuotientGroup.mk' _ x)).toAdd ∧
              IsPure (d.coordinates (QuotientGroup.mk' _ y)).toAdd) ∨
            (IsSingularDiagonal (d.coordinates (QuotientGroup.mk' _ x)).toAdd ∧
              IsSingularDiagonal (d.coordinates (QuotientGroup.mk' _ y)).toAdd))) ∧
        (∀ x : G, (x ∈ naturalPreimage d ∨ x ∈ dualPreimage d) → x ∉ Z →
          IsConj x z) ∧
        (∀ x : closureU Z ZS,
          IsSingularDiagonal (d.coordinates (QuotientGroup.mk' _ x)).toAdd →
            ConjugateBy (centralizerH Z) (x : G) v) ∧
        (∀ x ∈ residualK Z, x ∉ closureU Z ZS → orderOf x = 2 →
          ∃ y ∈ fixedLift Z ZS a ⊔ V,
            ConjugateBy (centralizerH Z) x y) ∧
        fixedLift Z ZS a = closureU Z ZS ⊓ centralizer (V : Set G) ∧
        fixedLift Z ZS a = closureU Z ZS ⊓
          centralizer ((closureU Z ZS ⊓ V : Subgroup G) : Set G) ∧
        (a : G) ∈ centralizer (fixedLift Z ZS a : Set G) ∧
        Nat.card (fixedLift Z ZS a) = 32 ∧
        (fixedLift Z ZS a).relIndex (closureU Z ZS) = 4 ∧
        Nat.card V = 2 * Nat.card (fixedLift Z ZS a ⊓ V : Subgroup G) ∧
        Nonempty (fixedLift Z ZS a ≃* FixedLiftModel) ∧
        Nonempty ((fixedLift Z ZS a ⊔ V : Subgroup G) ≃* CentralProductModel) := by
  letI : IsExtraspecial 2 (closureU Z ZS) := h.extraspecial
  obtain ⟨m⟩ := nonempty_markedGeometry d h
  obtain ⟨a, haV, haU, ha, hout⟩ :=
    exists_outside_representative (residual_le_H Z) h.center_eq h.residualEquiv V
      hVK hVU
  have haK : (a : G) ∈ residualK Z := hVK haV
  have hinside : ∀ x ∈ closureU Z ZS, orderOf x = 2 → IsConj x z ∨ IsConj x v :=
    inside_cover_of_markedGeometry d h.ZS_le_H h.center_eq m hz hZ
  have horbit := fun x y hx hy hxZ hyZ =>
    noncentral_involution_orbit_iff d h.ZS_le_H h.center_eq m hsep x y hx hy hxZ hyZ
  have hpure := preimages_fusion d h.ZS_le_H h.center_eq m
  have hmixed := mixed_fusion d h.ZS_le_H h.center_eq m
  have heq := FixedLift.eq_centralizers d h.core_eq h.center_eq hZV h.order128 hW
    hUV himage a haV haK haU ha
  have hcentralizes := FixedLift.centralizes d h.core_eq h.center_eq hZV h.order128 hW
    hUV himage a haV haK haU ha
  have hcard := FixedLift.card_and_index d h.core_eq h.center_eq h.order128 a haK haU ha
  have hhyperplane := FixedLift.hyperplane_card d h.core_eq h.center_eq hZV h.order128 hW hV
    hUV himage a haV haK haU ha
  have hmodel := FixedLift.fixedLiftEquiv_of_square_zero d h.core_eq h.center_eq
    m.square_zero a haK haU ha
  have hproduct := FixedLift.localProductEquiv_of_square_zero d h.core_eq h.center_eq
    hZV h.order128 hW hV hUV himage m.square_zero a haV haK haU ha
  refine ⟨a, haV, haU, ha, m, hinside, horbit, hpure, hmixed, ?_, heq.1, heq.2, hcentralizes,
    hcard.1, hcard.2, hhyperplane, ⟨hmodel⟩, ⟨hproduct⟩⟩
  intro x hxK hxU hx2
  obtain ⟨u, hu, hconj⟩ := hout x hxK hxU hx2
  exact ⟨(a : G) * u,
    (fixedLift Z ZS a ⊔ V).mul_mem
      ((show V ≤ fixedLift Z ZS a ⊔ V from le_sup_right) haV)
      ((show fixedLift Z ZS a ≤ fixedLift Z ZS a ⊔ V from le_sup_left) hu), hconj⟩
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial
