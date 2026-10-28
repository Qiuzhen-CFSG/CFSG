module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Constructions
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ElementFusion
public import Theory.GroupTheory.PGroup.ExtraspecialInvolutionCosetAction

/-!
# Lifting the quotient orbits in 15.3.61

For the extraspecial group `U`, two elements of one noncentral central coset
are inner conjugate. An orbit of the actual `H`-action on `U/Z` therefore
lifts to conjugacy by `H`: the remaining correction lies in `U ≤ H`.
The center equality is relative to `U`, and no ambient normality is imposed.

These lemmas reduce the source involution-orbit calculation to its genuine
natural/dual quotient action. They do not assume that calculation is proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1150.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.FusionCore
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- Conjugacy on the literal `U/Z` lifts to conjugacy by `H`. The inner
correction belongs to the extraspecial group `U ≤ H`. -/
theorem conjugateBy_of_quotient_orbit [IsExtraspecial 2 (closureU Z ZS)]
    (hZS : ZS ≤ centralizerH Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (x y : closureU Z ZS) (hy : (y : G) ∉ Z)
    (h : centralizerH Z)
    (horbit : quotientAction Z ZS h (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) y) :
    ConjugateBy (centralizerH Z) (x : G) (y : G) := by
  let x' : closureU Z ZS := ⟨(h : G) * (x : G) * (h : G)⁻¹,
    (mem_normalizer_iff.mp (H_normalizes_closureU Z ZS h.property) x).mp x.property⟩
  have hq : QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x' =
      QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) y :=
    (quotientAction_mk Z ZS h x).symm.trans horbit
  have hyc : y ∉ center (closureU Z ZS) := by
    rw [← hcenter]
    exact hy
  have hq' : QuotientGroup.mk' (center (closureU Z ZS)) y =
      QuotientGroup.mk' (center (closureU Z ZS)) x' := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [← hcenter]
    exact QuotientGroup.eq_iff_div_mem.mp hq.symm
  obtain ⟨u, hu⟩ := isConj_iff.mp
    (IsExtraspecial.isConj_of_center_quotient_eq hyc hq').symm
  have hxx' : ConjugateBy (centralizerH Z) (x : G) (x' : G) :=
    ⟨h, h.property, rfl⟩
  apply hxx'.trans
  refine ⟨u, closureU_le_H hZS u.property, ?_⟩
  exact congrArg Subtype.val hu

/-- The noncentral `H`-orbits in `U` are exactly the orbits of its actual
quotient action. This does not postulate a coordinate orbit classification. -/
theorem conjugateBy_iff_quotient_orbit [IsExtraspecial 2 (closureU Z ZS)]
    (hZS : ZS ≤ centralizerH Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (x y : closureU Z ZS) (hy : (y : G) ∉ Z) :
    ConjugateBy (centralizerH Z) (x : G) (y : G) ↔
      ∃ h : centralizerH Z, quotientAction Z ZS h (QuotientGroup.mk' _ x) =
        QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) y := by
  constructor
  · rintro ⟨h, hh, he⟩
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [quotientAction_mk]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext he)
  · rintro ⟨h, hh⟩
    exact conjugateBy_of_quotient_orbit Z ZS hZS hcenter x y hy h hh

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
