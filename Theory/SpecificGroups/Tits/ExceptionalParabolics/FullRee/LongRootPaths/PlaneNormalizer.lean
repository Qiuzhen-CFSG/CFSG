module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.PlaneSeparation
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
/-!
# No switch of the marked plane inside the first endpoint

The two noncentral marks u and zu are not conjugate inside the literal
first parabolic. The one-point certificate handles its derived subgroup;
its other coset is corrected by q, which commutes with both marks.
This is the intrinsic fusion separation used to centralize the source
plane normalizer in the direct J.4.10 parabolic argument.
-/

public section
open Subgroup
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ReeF4 RootRelations FiveNormalizer
open Tits.OuterOddSubgroups.OverlapCentralizers
open Tits.InvolutionRootGeometry.BinaryDerivedFusion

private theorem derived_no_switch (g : Model 0) (hg : g∈first)
    (hd : g∈commutator (Model 0)) (h : g*u=s^2*g) : False := by
  have hm : g∈ExceptionalParabolics.first.map atlasEmbedding := by
    rw [atlas_first_map]
    exact ⟨hg,hd⟩
  obtain ⟨a,ha,rfl⟩ := hm
  have hh : a * Atlas.a .s1 = (Atlas.a .s5)^2*a := by
    apply atlasEmbedding_injective
    simpa only [map_mul,map_pow,u,s] using h
  obtain ⟨⟨n,k⟩,he⟩ := firstNormalForm_surjective ⟨a,ha⟩
  have ha' : atlas1600SylowTwoNormalForm n * firstRotation^k.val=a := congrArg Subtype.val he
  rw [← ha'] at hh
  apply PlaneSeparation.normalForm_no_switch n k
  have hp := congrArg Subtype.val hh
  change (atlas1600SylowTwoNormalForm n).val * firstRotation.val^k.val *
    (Atlas.a .s1).val = (Atlas.a .s5).val^2 *
      ((atlas1600SylowTwoNormalForm n).val * firstRotation.val^k.val) at hp
  have hr : firstRotation.val = Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm := by
    change (atlas1600ParrottAssignment .s1).val * (atlas1600ParrottAssignment .r1).val = _
    rw [atlas1600ParrottAssignment_val,atlas1600ParrottAssignment_val]
    rfl
  simpa only [atlas1600SylowTwoNormalForm_val,Atlas1600SylowTwoCertificate.normalForm,hr,Atlas.a,
    atlas1600ParrottAssignment_val,Atlas1600ParrottData.permutation] using hp

/-- A first-endpoint element cannot interchange u and zu. -/
theorem first_no_switch (g : Model 0) (hg : g∈first) : g*u*g⁻¹≠z*u := by
  intro h
  have hzu : z*u=s^2 := by
    rw [← diagonal_square,q_commutes_s.symm.inv_right.mul_pow,inv_pow,q_square,
      mul_assoc,inv_mul_cancel,mul_one]
  rw [hzu] at h
  have hm : g*u=s^2*g := mul_inv_eq_iff_eq_mul.mp h
  by_cases hd : g∈commutator (Model 0)
  · exact derived_no_switch g hg hd hm
  · have hqF : q∈first := sylow_le_first q_mem_sylow
    have hout : q⁻¹∉commutator (Model 0) := by
      simpa only [q,inv_mem_iff] using fixedU_zero_not_mem
    have hD : q⁻¹*g∈commutator (Model 0) :=
      ((commutator (Model 0)).mul_mem_iff_of_index_two derived_index).mpr
        (iff_of_false hout hd)
    apply derived_no_switch (q⁻¹*g) (first.mul_mem (first.inv_mem hqF) hg) hD
    calc
      (q⁻¹*g)*u=q⁻¹*(g*u) := mul_assoc _ _ _
      _ = q⁻¹*(s^2*g) := congrArg (fun x => q⁻¹*x) hm
      _ = s^2*(q⁻¹*g) := by rw [← mul_assoc,(q_commutes_s.pow_right 2).inv_left.eq,mul_assoc]
end Tits.ExceptionalParabolics.FullRee.LongRootPaths
