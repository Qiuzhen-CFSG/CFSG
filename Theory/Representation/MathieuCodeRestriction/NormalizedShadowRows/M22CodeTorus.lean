module
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.Quotient
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.SectionAction
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Odd
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions

/-!
# Cubic fixed spaces in the full M22 code action

Six invariant octads distinguish the six fixed points of the native cubic.
After restricting to any pair hyperplane, the four octads even on that pair
still distinguish the other four fixed points. An inner actor fixing the
whole cubic fixed space therefore fixes all six points and lies in the cubic.
In particular such a pointwise kernel contains no inner involution.

This proves the fixed-space obstruction used in the M22 case of H.16.7,
without replacing the full pair-stabilizer action by its inner subgroup.
All finite checks use six octads and their 24 coordinates; the existing
six-point conjugacy and pointwise-stabilizer theorems supply the group argument.
Source: Aschbacher--Smith H.13.1,H.15.7,H.16.7, printed pp.395,401--405,
refs/quasithin.pdf. The actual pair application is
Chapter8/Section02/MathieuShadowRows/M22CodeDegree.
-/

public noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation Representation.BinaryOffender Subgroup
open scoped Pointwise
namespace MathieuCode.NormalizedShadowRows.M22CodeTorus

private def messages : Fin 6 → Fin 4096 := ![1312,1156,466,3456,1928,1409]
private theorem message_card : ∀ j, (m24GolayWord (messages j)).card = 8 := by
  decide +kernel
private def octads (j : Fin 6) : Octad :=
  ⟨m24GolayWord (messages j),m24GolayWord_mem_blocks_of_card_eq_eight _ (message_card j)⟩
private def points : Fin 6 → Fin 24 := ![7,8,11,12,20,22]
private theorem points_cover : ∀ x : Fin 24,
    SixPoint.cubicRepresentative.val x = x → ∃ j, points j = x := by
  decide +kernel
private theorem octads_fixed : ∀ j,
    SixPoint.cubicRepresentative.val • (octads j).val = (octads j).val := by
  decide +kernel
private theorem recover : ∀ p q x : Fin 6, ∀ y : Fin 24,
    x ≠ p → x ≠ q →
    (∀ j : Fin 6, (points p ∈ (octads j).val ↔ points q ∈ (octads j).val) →
      (points x ∈ (octads j).val ↔ y ∈ (octads j).val)) → points x = y := by
  decide +kernel

private theorem cubic_fixed_zero (a : m22PairStabilizer) (ha : a^3=1) :
    a.val • (0 : Fin 24) = 0 := by
  have hp (x : Fin 24) (hx : x ∈ m22Pair) : a.val • x = 0 ∨ a.val • x = 9 := by
    simpa only [m22Pair,Finset.mem_insert,Finset.mem_singleton] using
      MulAction.mem_stabilizer_finset'.mp a.property hx
  rcases hp 0 (by decide) with h0 | h0
  · exact h0
  have h9 : a.val • (9 : Fin 24) = 0 := by
    rcases hp 9 (by decide) with h9 | h9
    · exact h9
    · exact (show (0 : Fin 24) ≠ 9 by decide) (a.val.val.injective (h0.trans h9.symm)) |>.elim
  have hh := congrArg (fun b : m22PairStabilizer => b.val • (0 : Fin 24)) ha
  change a.val • (a.val • (a.val • (0 : Fin 24))) = 0 at hh
  rw [h0,h9,h0] at hh
  exact (show (9 : Fin 24) ≠ 0 by decide) hh |>.elim

/-- The inner part of the pointwise kernel of a cubic fixed code space lies in that cubic. -/
theorem inner_fixedSpace_kernel_le (Y : Subgroup m22PairStabilizer)
    (hY : Nat.card Y = 3) (hd : fixedCodim m22OuterCodeRepresentation Y = 6) :
    subspaceKernel m22OuterCodeRepresentation
      (fixedSpace m22OuterCodeRepresentation Y) ⊤ ⊓ m22ToPairStabilizer.range ≤ Y := by
  intro g hg
  obtain ⟨u,hu⟩ := hg.2
  have hg0 : g.val • (0 : Fin 24) = 0 := hu ▸ m22Embedding_fixed_zero u
  have hg9 : g.val • (9 : Fin 24) = 9 := hu ▸ m22Embedding_fixed_nine u
  let Y24 := Y.map m22PairStabilizer.subtype
  have hc : Nat.card Y24 = 3 := (card_map_of_injective m22PairStabilizer.subtype_injective).trans hY
  have hf : Nat.card (SixPoint.FixedPoint Y24) = 6 :=
    ((m22Outer_code_fixedCodim_eq_six_iff Y (by decide) (by decide) hY).mp hd).2
  obtain ⟨t,ht⟩ := SixPoint.cubicSubgroup_conjugacy Y24 hc hf
  have hy0 : (0 : Fin 24) ∈ MulAction.fixedPoints Y24 (Fin 24) := by
    rintro ⟨_,a,ha,rfl⟩
    have ho : orderOf a ∣ 3 := by
      have hh := orderOf_dvd_natCard (⟨a,ha⟩ : Y)
      rwa [←Subgroup.orderOf_coe,hY] at hh
    exact cubic_fixed_zero a (orderOf_dvd_iff_pow_eq_one.mp ho)
  have hy9 : (9 : Fin 24) ∈ MulAction.fixedPoints Y24 (Fin 24) := by
    rintro ⟨_,a,ha,rfl⟩
    have h0 := hy0 ⟨a.val,mem_map_of_mem _ ha⟩
    obtain ⟨b,hb⟩ := (m22ToPairStabilizer_mem_range_iff_fixed_zero a).mpr h0
    exact hb ▸ m22Embedding_fixed_nine b
  have htf (z : Fin 24) (hz : z ∈ MulAction.fixedPoints Y24 (Fin 24)) :
      t • z ∈ MulAction.fixedPoints SixPoint.cubicSubgroup (Fin 24) := by
    intro b
    obtain ⟨a,ha,he⟩ := (show b.val ∈ Y24.map (MulAut.conj t).toMonoidHom from ht.symm ▸ b.property)
    change b.val • (t • z) = t • z
    rw [←he]
    change (t*a*t⁻¹) • (t • z) = t • z
    have hza : a • z = z := hz ⟨a,ha⟩
    rw [mul_smul,mul_smul,inv_smul_smul,hza]
  have htf' (z : Fin 24) (hz : z ∈ MulAction.fixedPoints Y24 (Fin 24)) :
      SixPoint.cubicRepresentative.val (t • z) = t • z :=
    (SixPoint.mem_fixedPoint_zpowers_iff _ _).mp (htf z hz)
  obtain ⟨p,hp⟩ := points_cover (t • 0) (htf' 0 hy0)
  obtain ⟨q,hq⟩ := points_cover (t • 9) (htf' 9 hy9)
  have hback (j : Fin 6) : codeRepresentation t⁻¹ (octadVector (octads j)) ∈
      fixedSpace codeRepresentation Y24 := by
    intro a
    have hv : octadVector (octads j) ∈ fixedSpace codeRepresentation SixPoint.cubicSubgroup := by
      intro b
      exact octadVector_fixed_stabilizer _ ⟨b.val,zpowers_le.mpr (octads_fixed j) b.property⟩
    have h := hv ⟨t*a.val*t⁻¹,ht ▸ ⟨a.val,a.property,rfl⟩⟩
    change codeRepresentation (t*a.val*t⁻¹) (octadVector (octads j)) = octadVector (octads j) at h
    have h' := congrArg (codeRepresentation t⁻¹) h
    change codeRepresentation a.val (codeRepresentation t⁻¹ (octadVector (octads j))) = _
    simpa only [map_mul,Module.End.mul_apply,codeRepresentation.inv_self_apply] using h'
  have hpoint : t*g.val*t⁻¹ ∈ fixingSubgroup M24
      (MulAction.fixedPoints SixPoint.cubicSubgroup (Fin 24)) := by
    apply (mem_fixingSubgroup_iff M24).mpr
    intro z hz
    obtain ⟨x,rfl⟩ := points_cover z ((SixPoint.mem_fixedPoint_zpowers_iff _ _).mp hz)
    by_cases hxp : x = p
    · rw [hxp,hp]
      simpa only [mul_smul,inv_smul_smul] using congrArg (fun z => t • z) hg0
    by_cases hxq : x = q
    · rw [hxq,hq]
      simpa only [mul_smul,inv_smul_smul] using congrArg (fun z => t • z) hg9
    apply (recover p q x _ hxp hxq ?_).symm
    intro j heven
    have hu : codeRepresentation t⁻¹ (octadVector (octads j)) ∈ m22Hyperplane := by
      rw [octadVector,codeRepresentation_mk,mem_m22Hyperplane_mk]
      change wordOfSet (octads j).val (t.val 0) + wordOfSet (octads j).val (t.val 9) = 0
      change wordOfSet (octads j).val (t • 0) + wordOfSet (octads j).val (t • 9) = 0
      rw [←hp,←hq]
      simp only [wordOfSet,heven]
      split <;> simp
    have hv : (⟨codeRepresentation t⁻¹ (octadVector (octads j)),hu⟩ : M22Code) ∈
        fixedSpace m22OuterCodeRepresentation Y := by
      intro a
      exact Subtype.ext (hback j ⟨a.val.val,mem_map_of_mem _ a.property⟩)
    have hgv := congrArg Subtype.val (hg.1.2 _ hv)
    have hfix : codeRepresentation (t*g.val*t⁻¹) (octadVector (octads j)) = octadVector (octads j) := by
      change codeRepresentation g.val (codeRepresentation t⁻¹ (octadVector (octads j))) =
        codeRepresentation t⁻¹ (octadVector (octads j)) at hgv
      simp only [map_mul,Module.End.mul_apply,hgv,codeRepresentation.self_inv_apply]
    have hs := (SectionAction.octadVector_fixed_iff _ _).mp hfix
    constructor
    · intro hh
      exact MulAction.mem_stabilizer_finset'.mp hs hh
    · intro hh
      have hh' := MulAction.mem_stabilizer_finset'.mp ((octadStabilizer (octads j)).inv_mem hs) hh
      simpa only [inv_smul_smul] using hh'
  rw [SixPoint.cubic_fixedPointStabilizer,←ht] at hpoint
  obtain ⟨a,ha,he⟩ := hpoint
  have hga : a = g.val := (MulAut.conj t).injective he
  rw [hga] at ha
  obtain ⟨b,hb,he⟩ := ha
  exact (m22PairStabilizer.subtype_injective he) ▸ hb

/-- No inner involution fixes the whole four-dimensional cubic fixed code space. -/
theorem no_inner_involution_in_cubic_kernel (Y : Subgroup m22PairStabilizer)
    (hY : Nat.card Y = 3) (hd : fixedCodim m22OuterCodeRepresentation Y = 6)
    (g : m22PairStabilizer) (hg : orderOf g = 2) (hi : g ∈ m22ToPairStabilizer.range)
    (hfix : ∀ v ∈ fixedSpace m22OuterCodeRepresentation Y, m22OuterCodeRepresentation g v = v) : False := by
  have hm := inner_fixedSpace_kernel_le Y hY hd ⟨⟨mem_top _,hfix⟩,hi⟩
  have hh := orderOf_dvd_natCard (⟨g,hm⟩ : Y)
  rw [←Subgroup.orderOf_coe,hg,hY] at hh
  norm_num at hh

end MathieuCode.NormalizedShadowRows.M22CodeTorus
