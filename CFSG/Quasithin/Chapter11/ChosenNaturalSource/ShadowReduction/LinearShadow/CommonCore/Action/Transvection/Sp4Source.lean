module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.MarkedLine.HallSpectrum
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.Sp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.Kernel

/-!
# Identifying the actual conjugate in the Sp₄ branch

Compatible Sylow coordinates retain the full residual action. The genuine
Hall spectrum and its finite-field span identify the original V₁ as a field
line and realize it as [A,u]. The reciprocal Sp₄ displacement orbit supplies
x in N_G(A), with V₁^(x*g)=V₁. The counterexample line-normalizer theorem then
forces A=V, after which the literal A-star Sylow image becomes V-star.

The argument applies to every supplied natural multiplicity. It requires no local line, scalar, orbit or transporter
callback. Earlier natural-action, Cartan and parameter inputs retain their
source producers and are discharged by qt-d-1222-shadow-common-action.
Source: Aschbacher--Smith 11.3.7(4), printed p.773 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The original Sp₄ branch, with all local Cartan-line and reciprocal-orbit
premises discharged and the original star projection preserved. -/
theorem source_seed_star_sylow_sp4
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a))
    (hline : U₁ = (Coordinates.sp4 a).binarySubspace (f.space 0))
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hparameters : (S.field.degree : ℕ∞) < CFSG.Quasithin.ChapterE.globalR V ∨
      (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        CFSG.Quasithin.ChapterE.globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (g : G) (cK : NaturalQuotientMarking T H S.field)
    (hfixedL : V ⊓ centralizer (L : Set G) = ⊥)
    (hfixedK : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))]
    (hAH : V.map (MulAut.conj g).toMonoidHom ≤ H)
    (P : Sylow 2 (residualStar T H))
    (hP : (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H))
    (D_H : Subgroup G)
    (hDH : D_H ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcomm : D.centralQuotientPreimage U₁ = ⁅D.centralQuotientPreimage U₁,oddCartanPart D_H⁆) :
    (∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
      (D.centralQuotientPreimage U₁).map (MulAut.conj (x * g)).toMonoidHom =
        D.centralQuotientPreimage U₁) ∧
      V.map (MulAut.conj g).toMonoidHom = V ∧
      (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        (V.subgroupOf H).map (starProjection T H) := by
  obtain ⟨b,n,he⟩ := cK.compatibleSylowCoordinates hfixedK s.outside.1.1.2
    s.moves_omega_center hAH P hP
  obtain ⟨E,hE,hfix,hEU,_⟩ := source_marked_line_of_hall (.sp4 a) f hline s
    hfixedL g cK b n he D_H hDH hHall hcontain hcomm
  have hN := source_normalizes_of_natural_coordinates s (.sp4 a) f hline
    hparameters g cK.positive n
  obtain ⟨hx,heq⟩ := Reciprocal.source_seed_eq_sp4 s p hcounter halt a f hline
    hfixedL g n hN E hE hfix hEU
  exact ⟨hx,heq,by simpa only [heq] using hP⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
