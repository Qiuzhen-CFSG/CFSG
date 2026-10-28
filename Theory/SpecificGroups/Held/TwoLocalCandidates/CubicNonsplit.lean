module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Mathlib.Tactic.Group

/-!
# Nonsplitting above the alternating group in the Held local quotients

The native max3 and max4 relations survive quotienting by the intrinsic
two-core. Two products of adjacent involutions lift disjoint three-cycles,
but their products differ by the square of a nontrivial cubic kernel element.
The marked cubic element survives because it is a nonzero vector in the
certified odd plane and cannot lie in the two-core. All large permutation
identities are reused from the existing checked native relations.

Source: GLS3 Table 5.3p, the two E64.(3.S6) classes; the unchanged ATLAS
max3/max4 and HeG1-p2058B0 data. The nonsplitting calculation is the local
obstruction used for the A₆ branch of Aschbacher–Smith A.3.12, pp.47–48.
-/

public noncomputable section
open Subgroup
open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound
namespace Held.TwoLocalCandidates.CubicNonsplit

private theorem involutions_invert {G : Type*} [Group G] (a b c : G)
    (ha : a * a = 1) (hb : b * b = 1) (h : a * b = c * (b * a)) :
    a * c = c⁻¹ * a ∧ b * c = c⁻¹ * b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have hc : c = a * b * a * b := by
    calc
      c = (c * (b * a)) * (a * b) := by simp [mul_assoc, ←mul_assoc a a, ha, hb]
      _ = a * b * a * b := by rw [←h]; group
  rw [hc]
  simp only [mul_inv_rev, hai, hbi]
  constructor
  · simp only [←mul_assoc, ha, one_mul]
    simp only [mul_assoc, ha, mul_one]
  · simp only [←mul_assoc]

private theorem q_correction (i : Bool) (w : List (Fin 7)) (e : Nat) :
    localQuotientMap i (correction i w e) = localQuotientMap i (kernelThird i) ^ e := by
  rw [correction, map_mul, map_pow]
  have hw : (w.map (coreGenerator i)).prod ∈ pCore 2 (localOvergroup i) := by
    apply (show wordCore i ≤ pCore 2 (localOvergroup i) from
      le_sSup ⟨wordCore_normal i, wordCore_isPGroup i⟩)
    exact (wordCore i).list_prod_mem (fun x hx => by
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
      exact coreGenerator_mem i k)
  have hq : localQuotientMap i ((w.map (coreGenerator i)).prod) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hw
  rw [hq,one_mul]

private theorem third_ne_one (i : Bool) : kernelThird i ≠ 1 := by
  let j : Fin 2 := if i then 1 else 0
  have hv : (kernelThird i).val = LocalActions.RepresentativeImages.basisGenerator i 0 j := by
    cases i <;> rfl
  intro h
  have he : LocalActions.RepresentativeImages.basisGenerator i 0 j = 1 :=
    hv.symm.trans (congrArg Subtype.val h)
  have hs : (⟨LocalActions.RepresentativeImages.basisGenerator i 0 j,
      LocalActions.RepresentativeImages.basisGenerator_mem i 0 j⟩ : LocalActions.candidateOdd i 0) = 1 :=
    Subtype.ext he
  have hh := congrArg (LocalActions.RepresentativeImages.candidateOddEquiv i 0) hs
  rw [LocalActions.RepresentativeImages.candidateOddEquiv_basisGenerator, map_one] at hh
  have := congrFun hh j
  change (if j = j then (1 : ZMod 3) else 0) = 0 at this
  simp at this

private theorem q_third_ne_one (i : Bool) : localQuotientMap i (kernelThird i) ≠ 1 := by
  intro h
  have hm : kernelThird i ∈ pCore 2 (localOvergroup i) :=
    (QuotientGroup.eq_one_iff _).mp h
  let t : pCore 2 (localOvergroup i) := ⟨kernelThird i,hm⟩
  have hc : t ^ 3 = 1 := Subtype.ext (kernelThird_cube i)
  have ht : t = 1 := orderOf_eq_one_iff.mp <|
    Nat.eq_one_of_dvd_coprimes
      (pCore_isPGroup.orderOf_coprime (by decide : Nat.Coprime 2 3) t)
      dvd_rfl (orderOf_dvd_of_pow_eq_one hc)
  exact third_ne_one i (congrArg Subtype.val ht)

private def third (i : Bool) : LocalQuotient i := localQuotientMap i (kernelThird i)
private def reflection (i : Bool) (k : Fin 5) : LocalQuotient i :=
  localQuotientMap i (adjacent i k)
private def leftLift (i : Bool) : LocalQuotient i := reflection i 0 * reflection i 1
private def rightLift (i : Bool) : LocalQuotient i := reflection i 3 * reflection i 4

private theorem third_cube (i : Bool) : third i ^ 3 = 1 := by
  rw [third, ←map_pow, kernelThird_cube, map_one]

private theorem third_ne (i : Bool) : third i ≠ 1 := q_third_ne_one i

private theorem reflection_square (i : Bool) (k : Fin 5) : reflection i k * reflection i k = 1 := by
  simpa only [reflection, map_mul, map_one] using congrArg (localQuotientMap i) (adjacent_square i k)

private theorem relation04 (i : Bool) :
    reflection i 0 * reflection i 4 = third i ^ 2 * (reflection i 4 * reflection i 0) := by
  cases i
  · simpa only [reflection, third, map_mul, q_correction] using congrArg (localQuotientMap false) Checks0.commute04
  · simpa only [reflection, third, map_mul, q_correction] using congrArg (localQuotientMap true) Checks1.commute04

private theorem relation13 (i : Bool) :
    reflection i 1 * reflection i 3 = third i ^ 2 * (reflection i 3 * reflection i 1) := by
  cases i
  · simpa only [reflection, third, map_mul, q_correction] using congrArg (localQuotientMap false) Checks0.commute13
  · simpa only [reflection, third, map_mul, q_correction] using congrArg (localQuotientMap true) Checks1.commute13

private theorem inverse_square {G : Type*} [Group G] (z : G) (hz : z ^ 3 = 1) :
    (z ^ 2)⁻¹ = z := by
  apply inv_eq_of_mul_eq_one_left
  simpa only [←pow_succ'] using hz

private theorem invert_first {G : Type*} [Group G] (a z : G) (hz : z ^ 3 = 1)
    (h : a * z ^ 2 = z * a) : a * z = z ^ 2 * a := by
  have hz4 : z ^ 2 * z ^ 2 = z := by
    rw [←pow_add, pow_eq_pow_mod _ hz]
    exact pow_one z
  calc
    a * z = a * (z ^ 2 * z ^ 2) := by rw [hz4]
    _ = z ^ 2 * a := by rw [←mul_assoc, h, mul_assoc, h, ←mul_assoc, ←pow_two]

private theorem lifted_relation (i : Bool) :
    leftLift i * rightLift i = third i ^ 2 * (rightLift i * leftLift i) := by
  let a := reflection i 0
  let b := reflection i 1
  let c := reflection i 3
  let d := reflection i 4
  let z := third i
  have hz : z ^ 3 = 1 := third_cube i
  have had : a * d = z ^ 2 * (d * a) := relation04 i
  have hbc : b * c = z ^ 2 * (c * b) := relation13 i
  have haz : a * z ^ 2 = z * a := by
    simpa only [inverse_square z hz] using
      (involutions_invert a d (z ^ 2) (reflection_square i 0) (reflection_square i 4) had).1
  have hcz : c * z ^ 2 = z * c := by
    simpa only [inverse_square z hz] using
      (involutions_invert b c (z ^ 2) (reflection_square i 1) (reflection_square i 3) hbc).2
  have hcz1 : c * z = z ^ 2 * c := invert_first c z hz hcz
  change (a*b)*(c*d) = z^2*((c*d)*(a*b))
  cases i
  · have hac : a*c = z*(c*a) := by
      simpa only [a,c,z,reflection,third,map_mul,q_correction,pow_one] using
        congrArg (localQuotientMap false) Checks0.commute03
    have hbd : b*d = z^2*(d*b) := by
      simpa only [b,d,z,reflection,third,map_mul,q_correction] using
        congrArg (localQuotientMap false) Checks0.commute14
    calc
      (a*b)*(c*d) = a*(b*c)*d := by group
      _ = a*(z^2*(c*b))*d := by rw [hbc]
      _ = z*(a*c)*(b*d) := by rw [←mul_assoc a, haz]; group
      _ = z*(z*(c*a))*(z^2*(d*b)) := by rw [hac,hbd]
      _ = z^2*(c*(a*z^2))*(d*b) := by simp only [pow_two]; group
      _ = z^2*((c*z)*a)*(d*b) := by rw [haz]; group
      _ = (z^2*z^2)*(c*(a*d))*b := by rw [hcz1]; group
      _ = (z^2*z^2)*(c*(z^2*(d*a)))*b := by rw [had]
      _ = (z^2*z^2*z)*((c*d)*(a*b)) := by rw [←mul_assoc c, hcz]; group
      _ = z^2*((c*d)*(a*b)) := by
        have he : z^2*z^2*z = z^2 := by
          rw [←pow_add, ←pow_succ, pow_eq_pow_mod _ hz]
        rw [he]
  · have hac : a*c = c*a := by
      simpa only [a,c,reflection,map_mul,q_correction,pow_zero,one_mul] using
        congrArg (localQuotientMap true) Checks1.commute03
    have hbd : b*d = d*b := by
      simpa only [b,d,reflection,map_mul,q_correction,pow_zero,one_mul] using
        congrArg (localQuotientMap true) Checks1.commute14
    calc
      (a*b)*(c*d) = a*(b*c)*d := by group
      _ = a*(z^2*(c*b))*d := by rw [hbc]
      _ = z*(a*c)*(b*d) := by rw [←mul_assoc a, haz]; group
      _ = z*(c*a)*(d*b) := by rw [hac,hbd]
      _ = z*c*(a*d)*b := by group
      _ = z*c*(z^2*(d*a))*b := by rw [had]
      _ = z*(c*z^2)*((d*a)*b) := by group
      _ = z^2*((c*d)*(a*b)) := by rw [hcz]; simp only [pow_two]; group

private theorem lifts_not_commute (i : Bool) : ¬ Commute (leftLift i) (rightLift i) := by
  intro h
  have he := lifted_relation i
  rw [h.eq] at he
  have hz2 : third i ^ 2 = 1 := (mul_right_cancel (he.symm.trans (one_mul _).symm))
  apply third_ne i
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
    (orderOf_dvd_of_pow_eq_one hz2) (orderOf_dvd_of_pow_eq_one (third_cube i)))

private def reflectionImage (i : Bool) (k : Fin 5) : Equiv.Perm (Fin 6) :=
  let c := if i then SixPoint.first i * SixPoint.second i else SixPoint.second i
  c ^ k.val * SixPoint.first i * (c ^ k.val)⁻¹

private theorem reflection_image (i : Bool) (k : Fin 5) :
    SixPoint.quotientAction i (reflection i k) = reflectionImage i k := by
  have ha : SixPoint.action i (generator i 0) = SixPoint.first i := by
    cases i <;> exact SixPoint.action_first _
  have hb : SixPoint.action i (generator i 1) = SixPoint.second i := by
    cases i <;> exact SixPoint.action_second _
  simp only [reflection, SixPoint.quotientAction_mk, adjacent, map_mul, map_pow, map_inv, ha]
  have hc : SixPoint.action i (cycle i) =
      (if i then SixPoint.first i * SixPoint.second i else SixPoint.second i) := by
    cases i <;> simp only [cycle, Bool.false_eq_true, ↓reduceIte, map_mul, ha, hb]
  rw [hc]
  rfl

/-- Native commuting even permutations have noncommuting lifts through the
literal quotient by the local two-core, in both max3 and max4. -/
theorem noncommuting_even_lifts (i : Bool) :
    ∃ x y : LocalQuotient i,
      SixPoint.quotientAction i x ∈ alternatingGroup (Fin 6) ∧
      SixPoint.quotientAction i y ∈ alternatingGroup (Fin 6) ∧
      Commute (SixPoint.quotientAction i x) (SixPoint.quotientAction i y) ∧ ¬ Commute x y := by
  refine ⟨leftLift i, rightLift i, ?_, ?_, ?_, lifts_not_commute i⟩
  all_goals simp only [leftLift, rightLift, map_mul, reflection_image]
  · rw [Equiv.Perm.mem_alternatingGroup]; cases i <;> decide +kernel
  · rw [Equiv.Perm.mem_alternatingGroup]; cases i <;> decide +kernel
  · change _ * _ = _ * _; cases i <;> decide +kernel

/-- The whole residual kernel is the marked cyclic cubic subgroup. -/
private theorem kernel_eq_zpowers (i : Bool) :
    (SixPoint.quotientAction i).ker = zpowers (third i) := by
  have hmap : (wordCore i).map (localQuotientMap i) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    change wordCore i ≤ (QuotientGroup.mk' (pCore 2 (localOvergroup i))).ker
    rw [QuotientGroup.ker_mk']
    exact le_sSup ⟨wordCore_normal i, wordCore_isPGroup i⟩
  apply le_antisymm
  · calc
      _ = ((SixPoint.action i).ker).map (localQuotientMap i) := QuotientGroup.ker_lift _ _ _
      _ ≤ (kernelEnvelope i).map (localQuotientMap i) := map_mono (nativeKernel_le_kernelEnvelope i)
      _ = _ := by
        simp only [kernelEnvelope,Subgroup.map_sup,hmap,bot_sup_eq,MonoidHom.map_zpowers,third]
  · apply zpowers_le.mpr
    exact kernelThird_mem_ker i

/-- The full kernel of the six-point action is cyclic. -/
theorem quotientAction_kernel_isCyclic (i : Bool) : IsCyclic (SixPoint.quotientAction i).ker := by
  rw [kernel_eq_zpowers]
  infer_instance

end Held.TwoLocalCandidates.CubicNonsplit
