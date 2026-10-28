module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Line
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Complete

/-!
# Common action assembly from the remaining L-module comparison

Sylow placement and G.1.6 construct the marked natural quotient. The actual
Hall group supplies the diagonal and a permitted Cartan. Local uniqueness
gives the left fixed spaces first and identifies the fully moved L-orbit
containing V. The L-module comparison then eliminates the K-fixed space. The faithful line
character and full scalar spectrum prove the original line commutator and
its containment in V_H. Finally the reciprocal transvection calculation
identifies the selected conjugate and transports its literal Sylow image.

The single additional local premise is the L-module dichotomy, still owned
by qt-d-1222-shadow-common-action. Thus this is a conditional assembly, not
an assertion that source 11.3.7 is complete. The remaining explicit inputs
are exact preceding-source clauses from the natural-local-geometry and
parameter-component producers. Relative normality and the two-residual are
retained throughout.

Source: Aschbacher--Smith, 11.3.7, printed p.773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- All five action clauses for the original chosen conjugate, conditional
on the remaining L-module dichotomy. No scalar, orbit, Sylow, fixed-space,
natural-coordinate or transvection premise remains. -/
theorem source_action_of_cartan_dichotomy
    (cL : Coordinates D S.field) (f : InvariantFlag cL) (hu : f.IsInnerUnique)
    (hline : U₁ = cL.binarySubspace (f.space 0))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (hcomponent : Source.NormalComponentIn H (outsideResidual H))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hparameters : (S.field.degree : ℕ∞) < ChapterE.globalR V ∨
      (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        ChapterE.globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (hweak : D.centralQuotientPreimage U₁ ≤
      centralizer (Source.weakClosureZero (T : Subgroup G) V : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (D_H : Subgroup G) (hDH : D_H ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hcases : omegaCenter T ⊓ centralizer (oddCartanPart D_H : Set G) =
        omegaCenter T ⊓ centralizer (L : Set G) ∨
      ⁅omegaCenter T,oddCartanPart D_H⁆ = ⊥) :
    Source.NormalComponentIn H (outsideResidual H) ∧
    outsideResidual H ⊓ centralizer (omegaClosure T H : Set G) =
      (outsideResidual H).pCoreIn 2 ∧
    Function.Injective (residualQuotientAction T H s.outside.1.1.2) ∧
    ClassicalGroup.IsPSL (residualStar T H) 2 (2 ^ S.field.degree) ∧
    oddCartanPart D_H ≤ L ∧
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ ∧
    V ⊓ centralizer (L : Set G) = ⊥ ∧
    omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥ ∧
    V.map (MulAut.conj g).toMonoidHom = V ∧
    (∃ P : Sylow 2 (residualStar T H),
      (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        (V.subgroupOf H).map (starProjection T H)) ∧
    D.centralQuotientPreimage U₁ = ⁅D.centralQuotientPreimage U₁,oddCartanPart D_H⁆ ∧
    D.centralQuotientPreimage U₁ ≤ omegaClosure T H ∧
    ∃ X : Subgroup G, IsCartan T L X ∧ oddCartanPart D_H ≤ X := by
  obtain ⟨hWT,⟨cK⟩,P,hP,_⟩ := selected_natural_action s g hg ha hs hmodel
  have s' : Hypothesis1131At D S (cL.binarySubspace (f.space 0)) H := hline ▸ s
  obtain ⟨hDL,_,X,hX,hDX⟩ := Hall.source_hall_cartan cL f s' cK D_H hDH hHall halt hres hcubic
  obtain ⟨hz,hv,_,_,_,_⟩ := source_component_module s cK D_H hDH hHall hDL
  have hk := (Hall.source_fixed_spaces s hWT cK D_H hDH hHall hcases).2.2
  obtain ⟨hcomm,hVH⟩ := source_line_of_fixed_spaces cL f hu s cK D_H X hDH hHall hX hDX hv hk
  have hVi : f.Vi 0 = D.centralQuotientPreimage U₁ := by rw [hline]; rfl
  rw [hVi] at hcomm hVH
  have hAW : V.map (MulAut.conj g).toMonoidHom ≤ Source.weakClosureZero (T : Subgroup G) V :=
    le_sSup ⟨g,rfl,hg⟩
  have hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) :=
    le_inf hVH (hweak.trans (centralizer_le hAW))
  let := source_residualQuotient_simple hmodel
  obtain ⟨_,he,hP'⟩ := source_seed_star_sylow_transvections cL f hline hG2 s p hcounter
    halt hparameters g cK hv hk (hg.trans s.outside.1.1.2) P hP D_H hDH hHall hcontain hcomm
  exact ⟨hcomponent,source_action_kernel s hmodel,
    source_faithful_quotient_action s hmodel,source_star_model s hmodel,
    hDL,hz,hv,hk,he,⟨P,hP'⟩,hcomm,hVH,X,hX,hDX⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
