module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.LinearFiveStabilizer.Transport
public import Theory.SpecificGroups.BinaryLinear.FiveParabolicStabilizer
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Recognition of the embedded L₄(2) residual

The specified intrinsic quotient has order 20160, so five divides the order
of the parabolic. The whole group is excluded: GL₅(2) is perfect, and a
residual quotient of order 20160 would force its two-core to have order
496, divisible by 31.

Concrete Sylow-overgroup exhaustion identifies the parabolic with an actual
partial-flag stabilizer. Divisibility by five then forces a single cut of
dimension one or four. These end stabilizers are perfect, so the embedded
solvable residual is the point or hyperplane stabilizer itself. The final
theorem discharges both geometric inputs and supplies the recognition premise
for the parent action theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.12(5),
printed pp.47–48, and the proof of 1.3.9, printed p.514.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.LinearFiveStabilizer
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveParabolicStabilizer

private instance : Finite (LinearGroup 5) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) (matrixEquivLinear 5).toEquiv

private theorem card_linearFive : Nat.card (LinearGroup 5) = 9999360 := by
  rw [← Nat.card_congr (matrixEquivLinear 5).toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

private theorem card_linearFour_section {G : Type*} [Group G] (h : ClassicalGroup.IsPSL G 4 2) :
    Nat.card G = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

private theorem subgroup_ne_top_of_quotient
    {A : Subgroup (LinearGroup 5)}
    (h : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2) : A ≠ ⊤ := by
  intro he
  have hcard := card_linearFour_section h
  have hprod := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
  have hcA : Nat.card A = 9999360 := by rw [he, card_top, card_linearFive]
  rw [hcard, hcA] at hprod
  have hc : Nat.card (pCore 2 A) = 496 := by omega
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_dvd_pow
  have hd : 31 ∣ 2 ^ n := (show 31 ∣ Nat.card (pCore 2 A) by rw [hc]; decide).trans hn
  have := (by decide : Nat.Prime 31).dvd_of_dvd_pow hd
  norm_num at this

/-- The original quotient and residual hypotheses exclude the whole-group parabolic. -/
theorem parabolic_ne_top_of_residual_quotient (A P : Subgroup (LinearGroup 5))
    (hres : (solvableResidual P).map P.subtype = A)
    (h : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2) : P ≠ ⊤ := by
  intro he
  have : Group.IsPerfect (LinearGroup 5) := BinaryLinear.linearGroup_isPerfect 5 (by decide)
  have hA : A = ⊤ := by
    rw [← hres]
    subst P
    rw [solvableResidual_eq_top]
    rw [← MonoidHom.range_eq_map, range_subtype]
  exact subgroup_ne_top_of_quotient h hA

/-- The specified intrinsic quotient forces five to divide the order of the parabolic. -/
theorem five_dvd_card_of_residual_quotient (A P : Subgroup (LinearGroup 5))
    (hres : (solvableResidual P).map P.subtype = A)
    (h : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2) : 5 ∣ Nat.card P := by
  have hd : 20160 ∣ Nat.card A := by
    rw [← card_linearFour_section h]
    exact card_quotient_dvd_card (pCore 2 A)
  have hle : A ≤ P := by
    rw [← hres]
    exact map_subtype_le _
  exact ((by decide : 5 ∣ 20160).trans hd).trans (card_dvd_of_le hle)

/-- Conditional final assembly from actual flag exhaustion and flag-residual calculations.
The unconditional theorem below discharges both geometric premises. -/
theorem endParabolic_of_residual_quotient_of_flag_inputs
    (hflags : ∀ (T : Sylow 2 (LinearGroup 5)) (P : Subgroup (LinearGroup 5)),
      (T : Subgroup (LinearGroup 5)) ≤ P → IsFlagParabolic P)
    (hflagResidual : ∀ (b : FiveBasis) (cuts : Set (Fin 4)),
      flagStabilizer b cuts ≠ ⊤ → 5 ∣ Nat.card (flagStabilizer b cuts) →
      IsEndParabolic ((solvableResidual (flagStabilizer b cuts)).map
        (flagStabilizer b cuts).subtype))
    (A P : Subgroup (LinearGroup 5))
    (hP : Section02.LieParabolicTwo P)
    (hres : (solvableResidual P).map P.subtype = A)
    (h : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2) : IsEndParabolic A := by
  have hproper := parabolic_ne_top_of_residual_quotient A P hres h
  have hfive := five_dvd_card_of_residual_quotient A P hres h
  obtain ⟨T, hT⟩ := hP
  obtain ⟨b, cuts, hflag⟩ := hflags T P ((T : Subgroup (LinearGroup 5)).le_normalizer.trans hT)
  subst P
  rw [← hres]
  exact hflagResidual b cuts hproper hfive

/-- A parabolic with embedded solvable residual having intrinsic quotient L₄(2)
has that residual equal to an actual point or hyperplane stabilizer in GL₅(2).
Properness is a consequence of the residual and quotient hypotheses. -/
theorem endParabolic_of_residual_quotient (A P : Subgroup (LinearGroup 5))
    (hP : Section02.LieParabolicTwo P)
    (hres : (solvableResidual P).map P.subtype = A)
    (h : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2) : IsEndParabolic A :=
  endParabolic_of_residual_quotient_of_flag_inputs
    isFlagParabolic_of_sylow_le endParabolic_embeddedResidual_of_five_dvd A P hP hres h

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.LinearFiveStabilizer
