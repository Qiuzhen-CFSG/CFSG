module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.ModelAction
public import Theory.SpecificGroups.PSL3.SevenAction.Fixer
public import Theory.SpecificGroups.PSL3.SevenAction.Inner
public import Theory.GroupAction.PerfectCentralQuotient.FixedResidual

/-!
# Excluding the PSL₃(7) component action

No faithful four-group action on a finite perfect central cover of PSL₃(7)
satisfies the TI fixed-two-perfect restriction. Descend the action through
the specified central-quotient equivalence and choose a nonidentity inner
actor. Its conjugate SL₂(7) block is perfect and fixed pointwise. The fixed
perfect residual lifts through the same quotient map, so the TI restriction
forces every actor to fix this block. The model calculation leaves only the
identity and the chosen inner involution among automorphisms of square one,
contradicting faithfulness of the four-group.

Consequently the sufficient `ThreeCoreFreeAction` property holds for every
quasisimple cover in this case. The argument imposes no condition that K be
centerless: it retains the SL₃(7) alternative and its order-three odd center.
It uses neither an order-27 joint-centralizer subgroup nor an assumed model
centralizer conclusion. Component selection and the remaining model cases
belong to the parent assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the final
PSL₃(7) component case in the proof of 15.3.38, printed p.1137. The corrected
E₉ residual interface and the sufficient intrinsic property are in
`FieldExclusion.ModelAction`.
-/

public section

open Subgroup Theory.GroupTheory
open Matrix.PSL3.SevenAction

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3SevenAction

variable {K Q A : Type*} [Group K] [Group Q] [Group A]

private theorem perfect_isPPerfect [Finite K] [Group.IsPerfect K] : IsPPerfect 2 K := by
  intro N hN hp
  let := hN
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem quotient_fixes_perfect_subgroup [Finite K]
    (e : K ⧸ center K ≃* Q) (φ : A →* MulAut K)
    (hφ : FixesTwoPerfectSubgroups φ) (a : A) (ha : a ≠ 1)
    (P : Subgroup Q) [Group.IsPerfect P]
    (hP : P ≤ (MulAut.centralQuotientAction e (φ a)).fixedSubgroup)
    (b : A) (x : P) : MulAut.centralQuotientAction e (φ b) x = x := by
  obtain ⟨F, hF, hfix, hmap⟩ := MulAut.exists_perfect_fixed_lift e (φ a)
  let := hF
  have hx : (x : Q) ∈ MulAut.fixedPerfectResidual (MulAut.centralQuotientAction e (φ a)) :=
    le_map_solvableResidual_of_isPerfect P _ hP x.property
  rw [← hmap] at hx
  obtain ⟨y, hy, he⟩ := hx
  have hfixed : φ b y = y := hφ a ha F perfect_isPPerfect
    (fun z => (MulAut.mem_fixedSubgroup (φ a) z).mp (hfix z.property)) b ⟨y, hy⟩
  rw [← he]
  exact (MulAut.centralQuotientAction_apply e (φ b) y).trans
    (congrArg (e.toMonoidHom.comp (QuotientGroup.mk' (center K))) hfixed)

/-- The fixed-two-perfect restriction excludes faithful four-group actions on
every finite perfect cover of the specified PSL₃(7) model. -/
theorem not_fixesTwoPerfectSubgroups [Finite K]
    [Group.IsPerfect K] [IsKleinFour A]
    (e : K ⧸ center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7))
    (φ : A →* MulAut K) (hinj : Function.Injective φ) :
    ¬ FixesTwoPerfectSubgroups φ := by
  intro hφ
  let ψ := (MulAut.centralQuotientAction e).comp φ
  have hψ := MulAut.centralQuotientAction_comp_injective e φ hinj
  obtain ⟨a, ha, g, hg⟩ := four_action_has_inner ψ hψ
  let γ := MulAut.conj g
  let P := block.map γ.toMonoidHom
  let : Group.IsPerfect block := block_perfect
  let : Group.IsPerfect P := Group.IsPerfect.map γ.toMonoidHom
  have hP : P ≤ (ψ a).fixedSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    apply (MulAut.mem_fixedSubgroup (ψ a) _).mpr
    rw [hg]
    change γ (actor (γ.symm (γ x))) = γ x
    rw [γ.symm_apply_apply, (MulAut.mem_fixedSubgroup actor x).mp (block_le_fixed hx)]
  have htwo (b : A) : b = 1 ∨ b = a := by
    let β : MulAut Model := γ⁻¹ * ψ b * γ
    have hβsq : β ^ 2 = 1 := by
      have hb : ψ b * ψ b = 1 := by rw [← map_mul, IsKleinFour.mul_self, map_one]
      change (γ⁻¹ * ψ b * γ) ^ 2 = 1
      calc
        _ = γ⁻¹ * (ψ b * ψ b) * γ := by rw [pow_two]; group
        _ = 1 := by rw [hb]; group
    have hβfix (x : block) : β x = x := by
      have hx := quotient_fixes_perfect_subgroup e φ hφ a ha P hP b
        ⟨γ x, mem_map_of_mem γ.toMonoidHom x.property⟩
      change ψ b (γ x) = γ x at hx
      change γ.symm (ψ b (γ x)) = x
      rw [hx, γ.symm_apply_apply]
    rcases involutive_block_fixer β hβsq hβfix with hβ | hβ
    · left
      apply hψ
      rw [map_one]
      have he := congrArg (fun δ : MulAut Model => γ * δ * γ⁻¹) hβ
      change γ * (γ⁻¹ * ψ b * γ) * γ⁻¹ = γ * 1 * γ⁻¹ at he
      simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
        mul_inv_cancel, mul_one] using he
    · right
      apply hψ
      rw [hg]
      have he := congrArg (fun δ : MulAut Model => γ * δ * γ⁻¹) hβ
      change γ * (γ⁻¹ * ψ b * γ) * γ⁻¹ = γ * actor * γ⁻¹ at he
      simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
        mul_inv_cancel, mul_one] using he
  apply IsKleinFour.not_isCyclic (G := A)
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨a, top_unique ?_⟩
  intro b _
  rcases htwo b with rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _

/-- The PSL₃(7) model step required by the field-component assembly, including
quasisimple covers with nontrivial center. All model premises are discharged. -/
theorem threeCoreFreeAction [Finite K]
    [IsQuasisimple K] [IsKleinFour A]
    (e : K ⧸ center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7))
    (φ : A →* MulAut K) (hinj : Function.Injective φ)
    (hφ : FixesTwoPerfectSubgroups φ) : ThreeCoreFreeAction φ :=
  (not_fixesTwoPerfectSubgroups e φ hinj hφ).elim

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3SevenAction
