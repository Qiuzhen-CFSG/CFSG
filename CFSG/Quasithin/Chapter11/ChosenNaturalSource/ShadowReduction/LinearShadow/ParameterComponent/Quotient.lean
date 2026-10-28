module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Orbit

/-!
# Faithfulness of the source quotient action

The representation constructed on H/C_H(VH) has exactly the quotient's
identity as its action kernel. Thus the offender in 11.3.4 has rank at
least s(G,V), on the actual quotient and unchanged orbit module.
Source: Aschbacher--Smith, 11.3.4(1), printed p.771.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}

/-- Faithfulness comes from the literal centralizer denominator. -/
theorem orbitRepresentation_injective (h : Hypothesis1131At D S U₁ H) :
    Function.Injective (orbitRepresentation h) := by
  let := omegaOrbit_elementary h
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective
    (centralizer ((omegaOrbit T H).subgroupOf H : Set H)) x
  change orbitRepresentation h (orbitProjection T H a) = 1 at hx
  apply (QuotientGroup.eq_one_iff a).mpr
  intro w hw
  apply Subtype.ext
  let v : Additive (omegaOrbit T H) := Additive.ofMul ⟨w,hw⟩
  have he : ((orbitRepresentation h (orbitProjection T H a) v).toMul : G) = w := by
    rw [hx]
    rfl
  rw [orbitRepresentation_apply] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The genuine fixed-space family bounds the rank of the actual A*. -/
theorem active_conjugate_rank (h : Hypothesis1131At D S U₁ H)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaOrbit T H : Set G)) :
    letI := D.elementary
    (ChapterE.globalS V).toNat ≤ Representation.BinaryOffender.rank (actorImage T H (V.map (MulAut.conj g).toMonoidHom)) := by
  let := D.elementary
  let := omegaOrbit_elementary h
  exact ChapterE.parameter_le_rank_of_mem_fixedSpaceFamily (orbitRepresentation h)
    (orbitRepresentation_injective h) (active_conjugate_fixedSpaceFamily h g hg ha)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
