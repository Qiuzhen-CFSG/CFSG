module
public import Theory.SpecificGroups.Triality.ArmsFixedQuotient
public import Theory.SpecificGroups.Triality.ConcreteBruhat.RootData

/-!
# Second-parabolic conjugators for Sylow-fixed core vectors

The fixed-space theorem leaves the two highest long-root coordinates. A
long-root shear removes the highest coordinate, and the central reflection
sends the remaining root to the highest root. Both factors belong to the
central parabolic, so the actual conjugator can be transported through a
marked inclusion amalgam. No ambient recognition is used.

Source: Aschbacher--Smith F.4.35, printed p.292. The original application is
Chapter14/Section02/EightLargeParabolic/FusionControl.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
open Parabolics RadicalCoordinates RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators
private theorem long_pair_conjugate_in_second (P : Parameters) (hp : P.prime=2)
    (e f : fixedField P) (he : e≠0) :
    ∃ g : parabolic P .central, g.val*(long P hp 1 e*long P hp 2 f)*g.val⁻¹ = long P hp 2 e := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let t := f/e
  have ht : t*e=f := div_mul_cancel₀ f he
  have hh : long P hp 0 t*long P hp 1 e*(long P hp 0 t)⁻¹ =
      long P hp 1 e*long P hp 2 (t*e) := by
    rw [long_zero_one_exchange P hp t e,mul_assoc (long P hp 1 e),
      ←(highest_commute_long P hp (t*e) 0 t).eq]
    group
  have hc : long P hp 0 t*(long P hp 1 e*long P hp 2 f)*(long P hp 0 t)⁻¹ = long P hp 1 e := by
    rw [show long P hp 0 t*(long P hp 1 e*long P hp 2 f)*(long P hp 0 t)⁻¹ =
        (long P hp 0 t*long P hp 1 e*(long P hp 0 t)⁻¹)*
        (long P hp 0 t*long P hp 2 f*(long P hp 0 t)⁻¹) by group,
      hh,←(highest_commute_long P hp f 0 t).eq,mul_inv_cancel_right,ht,
      mul_assoc,←long_add,CharTwo.add_self_eq_zero,long_zero,mul_one]
  have hlong : long P hp 0 t∈parabolic P .central :=
    (unipotent_le_borel P).trans (borel_le_parabolic P .central)
      (descendSubgroup_mono P (RadicalCoordinates.rootSubgroup_le_positiveSubgroup P hp .arms)
        (long_mem P hp .arms 0 trivial t))
  have hw : ConcreteBruhat.weylRepresentative P hp (.sr 1)∈parabolic P .central := by
    rw [show DihedralGroup.sr 1=ConcreteBruhat.relativeReflection .central from rfl,
      ConcreteBruhat.weylRepresentative_simple]
    exact ConcreteBruhat.simpleRepresentative_mem_parabolic P hp .central
  refine ⟨⟨_,(parabolic P .central).mul_mem hw hlong⟩,?_⟩
  change (ConcreteBruhat.weylRepresentative P hp (.sr 1)*long P hp 0 t)*_*
    (ConcreteBruhat.weylRepresentative P hp (.sr 1)*long P hp 0 t)⁻¹=_
  rw [show (ConcreteBruhat.weylRepresentative P hp (.sr 1)*long P hp 0 t)*
      (long P hp 1 e*long P hp 2 f)*(ConcreteBruhat.weylRepresentative P hp (.sr 1)*long P hp 0 t)⁻¹ =
      ConcreteBruhat.weylRepresentative P hp (.sr 1)*
        (long P hp 0 t*(long P hp 1 e*long P hp 2 f)*(long P hp 0 t)⁻¹)*
        (ConcreteBruhat.weylRepresentative P hp (.sr 1))⁻¹ by group,
    hc, central_long_one]

/-- The fixed quotient calculation supplies a conjugator in the second parabolic. -/
theorem fixed_mod_center_conjugate_highest_in_second (P : Parameters) (hp : P.prime=2)
    (u : radical P .arms)
    (h : ∀ a : ExtensionField P, ⁅short P hp 0 a,u.val⁆∈highestRoot P) :
    ∃ g : parabolic P .central, g.val*u.val*g.val⁻¹∈highestRoot P := by
  obtain ⟨e,f,huf⟩ := fixed_mod_center_long_support P hp u h
  have hz (t : fixedField P) : long P hp 2 t∈highestRoot P := by
    refine ⟨longElementary P hp 2 t,?_,rfl⟩
    change elementaryInclusion P (longElementary P hp 2 t)∈splitHighestRoot P
    rw [longElementary_val]
    exact ⟨Multiplicative.ofAdd t.val,rfl⟩
  by_cases he : e=0
  · refine ⟨1,?_⟩
    simpa only [Subgroup.coe_one,one_mul,inv_one,mul_one,huf,he,long_zero] using hz f
  · obtain ⟨g,hg⟩ := long_pair_conjugate_in_second P hp e f he
    exact ⟨g,by rw [huf,hg]; exact hz e⟩
end Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
