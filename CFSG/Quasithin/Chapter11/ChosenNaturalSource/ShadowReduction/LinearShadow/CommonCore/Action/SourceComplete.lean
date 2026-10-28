module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Dichotomy

/-!
# All five common-action clauses of source 11.3.7

The selected conjugate gives the actual residual Sylow image and natural
quotient coordinates. Hall geometry puts D₀ in L and in a permitted Cartan.
The proved homogeneous L-module calculation supplies the Cartan dichotomy,
removing the final local premise of the existing source assembly. That
assembly proves the three fixed-space vanishings, original line commutator,
conjugate equality and actual V-star Sylow placement, alongside the faithful
residual quotient action. Both the SL₃ and Sp₄ cases are retained.

Only exact preceding-source conclusions from §§11.0--11.2 and 11.3.4--6
remain explicit, as permitted by the common-action task contract. Their
producers are qt-d-1222-natural-local-geometry and
qt-d-1222-shadow-parameter-component; qt-d-1222-shadow-common-core retains
final assembly with those inputs. No natural marking, scalar, transvection,
module dichotomy or desired fixed-space conclusion is assumed.
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

/-- All five original action clauses, with every local natural, Cartan and transvection premise discharged. -/
theorem source_action_complete
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
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G)))) :
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
  obtain ⟨_,⟨cK⟩,_⟩ := selected_natural_action s g hg ha hs hmodel
  have s' : Hypothesis1131At D S (cL.binarySubspace (f.space 0)) H := hline ▸ s
  obtain ⟨_,_,X,hX,hDX⟩ := Hall.source_hall_cartan cL f s' cK D_H hDH hHall halt hres hcubic
  have hcases := source_cartan_dichotomy cL f hu hG2 s cK D_H X hDH hHall hX hDX
  exact source_action_of_cartan_dichotomy cL f hu hline hG2 s p hcounter hcomponent
    hmodel hs halt hparameters hweak hres hcubic g hg ha D_H hDH hHall hcases

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
