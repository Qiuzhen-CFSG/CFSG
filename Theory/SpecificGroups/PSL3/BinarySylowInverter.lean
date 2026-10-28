module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.LongRoot
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import BenderSuzuki.External.Huppert.II.theorem_8_3_split
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupAction.PerfectCentralQuotientSylow
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupAction.InvertedOddLift

/-!
# Full split-torus inversion for binary linear-three Sylow fixers

The faithful highest-root SL₂ embedding carries a reflected split torus
into PSL₃. Involution conjugacy then gives an element of exact order
2ⁿ−1 inverted by any prescribed inner involution. A Sylow fixer on a
perfect central cover descends faithfully to an inner projective actor.
The fixed-kernel odd-order lift retains both its action and the full
split-torus order upstairs.

Source: Aschbacher--Smith 12.6.26, printed p.832; the reflected torus is
Huppert II.8.3. The imported matrix and automorphism results retain their
source attributions. No bound on n or component exclusion is assumed.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.BinarySylowInverter
variable {F : Type*} [Field F] [Finite F]

/-- A binary projective linear-three involution inverts a generator of the full split torus. -/
theorem inner_involution_inverts_split_generator
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    ∃ x : PSL(3,F), orderOf x = 2^n-1 ∧ t*x*t⁻¹=x⁻¹ := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
    BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data hF
  let := hU
  have ho : Odd (2^n-1) := by
    have he : Even ((2:ℕ)^n) := even_two.pow_of_ne_zero (by omega)
    have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
    exact Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  have hUc : Nat.card U = 2^n-1 := by
    rw [hcard,hF,ho.coprime_two_right.gcd_eq_one,Nat.div_one]
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
  let f : PSL(2,F) →* PSL(3,F) :=
    (Matrix.PSL3Even.MinimalParabolicWitness.longRoot F).comp
      (Theory.PSL2.sl2QuotientEquiv F).symm.toMonoidHom
  have hf : Function.Injective f :=
    (Matrix.PSL3Even.MinimalParabolicWitness.longRoot_injective F).comp
      (Theory.PSL2.sl2QuotientEquiv F).symm.injective
  have hwo : orderOf w = 2 := orderOf_eq_prime (by simpa [pow_two] using hw2)
    (fun hh => hw (hh ▸ U.one_mem))
  have hfw : orderOf (f w) = 2 := (orderOf_injective f hf w).trans hwo
  have hwne : f w ≠ 1 := by intro hh; rw [hh,orderOf_one] at hfw; omega
  have htne : t ≠ 1 := by intro hh; rw [hh,orderOf_one] at ht; omega
  obtain ⟨g,hg⟩ := isConj_iff.mp
    ((EvenInnerCentralizers.involution_isConj_root F hn hF (f w) hwne
      (by simpa only [hfw] using pow_orderOf_eq_one (f w))).trans
      (EvenInnerCentralizers.involution_isConj_root F hn hF t htne
        (by simpa only [ht] using pow_orderOf_eq_one t)).symm)
  refine ⟨MulAut.conj g (f x),?_,?_⟩
  · rw [MulEquiv.orderOf_eq,orderOf_injective f hf,Subgroup.orderOf_coe,hx,hUc]
  · have hfi : f w*f x*(f w)⁻¹=(f x)⁻¹ := by
      simpa only [map_mul,map_inv] using congrArg f (hi x x.property)
    rw [←hg]
    change (g*f w*g⁻¹)*(g*f x*g⁻¹)*(g*f w*g⁻¹)⁻¹ = (g*f x*g⁻¹)⁻¹
    calc
      _ = g*(f w*f x*(f w)⁻¹)*g⁻¹ := by group
      _ = g*(f x)⁻¹*g⁻¹ := by rw [hfi]
      _ = _ := by group

/-- Fixed-center Sylow fixers invert the full split-torus order in the original cover. -/
theorem sylow_fixer_inverts_split_generator_of_fixes_center
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [IsSimpleGroup (B ⧸ center B)] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2^n) (e : B ⧸ center B ≃* PSL(3,F))
    (a : MulAut B) (ha : orderOf a = 2)
    (P : Sylow 2 B) (hP : ∀ x ∈ P, a x = x)
    (hZ : ∀ x ∈ center B, a x = x) :
    ∃ x : B, orderOf x = 2^n-1 ∧ a x = x⁻¹ := by
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' (center B)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let b := MulAut.centralQuotientAction e a
  have hb : orderOf b = 2 :=
    (orderOf_injective _ (MulAut.centralQuotientAction_injective e) a).trans ha
  obtain ⟨Q,hQ⟩ := MulAut.centralQuotientAction_exists_fixed_sylow e a P hP
  obtain ⟨t,_,ht⟩ := LinearThree.exists_sylow_center_conj_of_equiv F (by omega) hF
    (MulEquiv.refl _) Q b hQ
  have htc : orderOf t = 2 :=
    (orderOf_injective MulAut.conj
      (Theory.GroupTheory.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect) t).symm.trans
      (ht ▸ hb)
  obtain ⟨y,hy,hi⟩ := inner_involution_inverts_split_generator hn hF t htc
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  apply MulAut.exists_inverted_odd_of_fixed_kernel a b f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (fun x => (MulAut.centralQuotientAction_apply e a x).symm)
    (ha ▸ pow_orderOf_eq_one a) ?_ ?_ y hy ?_
  · intro x hx
    apply hZ x
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    exact hx.trans e.map_one.symm
  · have he : Even ((2:ℕ)^n) := even_two.pow_of_ne_zero (by omega)
    have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
    exact Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  · rw [ht]
    exact hi

end Matrix.PSL3.BinarySylowInverter
