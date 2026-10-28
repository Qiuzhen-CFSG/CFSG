module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Reduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.ProjectiveDegree
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Inner involutions in the PSL₂(25) source action

The checked cover comparison identifies the actual component with PSL₂(25).
Its nonsplit torus has order thirteen and an inverting involution. Fusion
transports that pair to every inner involution, and then the actual component
embedding transports both actors to G.

The commutator with the order-thirteen element again has order thirteen.
The binary prime-displacement bound and the commutator rank inequality give
displacement at least six, with no upper bound on the module degree. At degree
twelve, order-thirteen actors are fixed-point-free and inner involutions move
exactly six dimensions. No outer element is adjoined to the acting group.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript p.9; Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

private theorem model_inverts_thirteen {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 25)
    (t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (ht : orderOf t = 2) :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      orderOf x = 13 ∧ t * x * t⁻¹ = x⁻¹ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨S, w, _, hS, _, hwS, hw2, hwinv, _, _⟩ :=
    BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data
      (p := 5) (f := 2) (by simpa using hF)
  have hS13 : Nat.card S = 13 := by simpa [hF] using hS
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 13 (by rw [hS13])
  have hw1 : w ≠ 1 := fun hh => hwS (hh ▸ S.one_mem)
  have hw : orderOf w = 2 := orderOf_eq_prime (by simpa [pow_two] using hw2) hw1
  obtain ⟨c, hc⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj w t hw ht)
  refine ⟨c * (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * c⁻¹, ?_, ?_⟩
  · change orderOf (MulAut.conj c (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = 13
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
  · rw [← hc]
    calc
      _ = c * (w * (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * w⁻¹) * c⁻¹ := by group
      _ = c * (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)⁻¹ * c⁻¹ := by rw [hwinv x x.property]
      _ = _ := by group

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- Every inner involution in the actual source group inverts an actual
order-thirteen element of the component. -/
theorem source_inner_inverts_thirteen
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    {t : G} (htL : t ∈ generalizedFitting G) (ht : orderOf t = 2) :
    ∃ x : G, x ∈ generalizedFitting G ∧ orderOf x = 13 ∧ t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := RankOneSize.source_component_isPSL ρ h
    (by decide) (by decide) (by decide) hm
  let tL : generalizedFitting G := ⟨t, htL⟩
  have ht' : orderOf (e tL) = 2 := by
    rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ht
  obtain ⟨x, hx13, hxi⟩ := model_inverts_thirteen hF (e tL) ht'
  let y := e.symm x
  refine ⟨(y : G), y.property, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    change orderOf (e.symm x) = 13
    rw [e.symm.orderOf_eq]
    exact hx13
  · have hi : tL * y * tL⁻¹ = y⁻¹ := by
      apply e.injective
      simpa only [y, map_mul, map_inv, MulEquiv.apply_symm_apply] using hxi
    exact congrArg (fun z : generalizedFitting G => (z : G)) hi

private theorem thirteen_le_displacement {x : G} (hx : orderOf x = 13) :
    12 ≤ fixedCodim ρ (zpowers x) := by
  simpa only [BinaryPrimeDegree.orderOf_two_mod_thirteen] using
    prime_order_le_fixedCodim ρ h.faithful (by decide : Nat.Prime 13) (by decide) x hx

/-- The torus lower bound does not require the degree-twelve reduction. -/
theorem source_inner_displacement_ge_six
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    {t : G} (htL : t ∈ generalizedFitting G) (ht : orderOf t = 2) :
    6 ≤ fixedCodim ρ (zpowers t) := by
  obtain ⟨x, _, hx, hi⟩ := source_inner_inverts_thirteen ρ h hm htL ht
  have hord : orderOf (t * x * t⁻¹ * x⁻¹) = 13 := by
    rw [hi, ← mul_inv_rev, ← pow_two, orderOf_inv]
    have ho : Odd (orderOf x) := by rw [hx]; decide
    rw [ho.coprime_two_right.orderOf_pow, hx]
  have hlo := thirteen_le_displacement ρ h hord
  have hup := fixedCodim_commutator_le_twice ρ t x
  omega

/-- At binary degree twelve every actual order-thirteen actor is fixed-point-free. -/
theorem source_thirteen_fixedSpace_eq_bot
    (hd : Module.finrank (ZMod 2) V = 12) {x : G} (hx : orderOf x = 13) :
    fixedSpace ρ (zpowers x) = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have hlo := thirteen_le_displacement ρ h hx
  have hsum := fixedCodim_add_finrank ρ (zpowers x)
  omega

/-- The source's exact displacement six, with degree twelve still explicit. -/
theorem source_inner_displacement_eq_six
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    (hd : Module.finrank (ZMod 2) V = 12)
    {t : G} (htL : t ∈ generalizedFitting G) (ht : orderOf t = 2) :
    fixedCodim ρ (zpowers t) = 6 := by
  have hlo := source_inner_displacement_ge_six ρ h hm htL ht
  have hup := (involution_actor_rank_and_fixedCodim ρ t ht).2.2.2
  omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
