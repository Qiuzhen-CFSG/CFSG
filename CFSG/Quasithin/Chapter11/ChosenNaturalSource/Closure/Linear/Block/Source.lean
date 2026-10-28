module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Structure

/-!
# Assembly of the SL₃ block and exceptional-K reduction

The marked three-conjugate collapse gives the original SL₃ block. Its
central splitting and point-radical calculation supply the special-factor
order and the elementary rank-4n central quotient. The actual K-action,
including its proved kernel bound, excludes every surviving exceptional
odd extension and yields K=L₁. The preceding natural-sum conclusion then
removes C_U(L), forces multiplicity two, and identifies the original cores.
The center, derived subgroup and Frattini subgroup all become V₁.

All special-factor, center, kernel, nonsection, multiplicity and core
premises from the independent branches are discharged here. The retained
boundary consists of the genuine marked G.2 hypothesis and collapse
(qt-d-1222-sl3-three-conjugates), preceding relative-component and
triangle conclusions (qt-d-1222-natural-relative-components and
qt-d-1222-shadow-component-triangle), the actual Chapter 11 flag, and
precisely the conditional natural-sum conclusion of 11.5.5(3)
(qt-d-1222-cartan-natural-sum). The parent
qt-d-1222-natural-closure-sl3 discharges these earlier source inputs and
retains the final abelianness contradiction.

The quotient marking is for the literal U/V₁ and original solvable
residual. The valid splitting uses T∩L; no equality U=T∩L is asserted.
Source: Aschbacher--Smith, 11.5.7, refs/quasithin.pdf, printed p.782.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

/-- The complete conditional block branch on the original chosen geometry.
The natural-sum input is invoked only after K=L₁ has been proved. -/
theorem source_conclusions
    {κ : GroupClass} (hG₁ : IsSQTK κ E.G₁)
    (hnormal : Source.NormalComponentIn E.G₁ E.K)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y)
    (hcases : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X)
    (f : E.ClosureFlag)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (b : InvariantFlag (.sl3 m))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace (b.space 0))
    (hthree : E.threeSpace = (Coordinates.sl3 m).binarySubspace (b.space 2))
    (hsum : ∀ hK : E.K = E.L₁, ∃ r : ℕ,
      Nonempty (ActionEquiv (Multiplicity.action E f hK)
        (repeated (linearNatural E.input.field 2) r))) :
    ∃ hK : E.K = E.L₁,
      let hseed := Multiplicity.seed_eq E m b hthree
      ChapterC.IsSL3EvenBlock L E.input.field.degree ∧
      E.V₃ = V ∧ E.U = E.W ∧
      Nonempty (ActionEquiv (Multiplicity.action E f hK)
        (repeated (linearNatural E.input.field 2) 2)) ∧
      Nonempty (ActionEquiv (Multiplicity.pointAction E f hseed hK)
        (repeated (linearNatural E.input.field 2) 2)) ∧
      Nonempty (Outside.NaturalPair E) ∧
      Nat.card (SpecialFactor E) = (2 ^ E.input.field.degree) ^ 5 ∧
      Nonempty (SpecialFactor E ≃* E.W) ∧
      Nat.card E.W = (2 ^ E.input.field.degree) ^ 5 ∧
      E.W = E.K.pCoreIn 2 ∧ E.W = E.L₁.pCoreIn 2 ∧ E.W ≤ L ∧
      E.W ⊓ centralizer (L : Set G) = ⊥ ∧ L.pCoreIn 2 = V ∧
      E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E ∧
      E.K ≤ centralizer (closureCenter E : Set G) ∧
      IsElementaryAbelian 2 (CentralQuotient E) ∧
      Group.rank (CentralQuotient E) = 4 * E.input.field.degree ∧
      IsPGroup 2 E.W ∧ closureCenter E = E.V₁ ∧
      center E.W = _root_.commutator E.W ∧ center E.W = frattini E.W ∧
      IsElementaryAbelian 2 (center E.W) ∧ center E.W ≠ ⊥ ∧
      sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
        ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨hcardS, hfixed, hz, he, hr⟩ := Special.consumer_inputs E d hUT hf hc
  let := he
  have hK := Exceptional.K_eq_pointResidual E d hG₁ hnormal hUT hfixed hz hr
    hcases htriangle
  obtain ⟨hseed, hUW, ha, hpa, hp, hcard, hcoreK, hcoreL, hWL, hfix, hcore, hsplit⟩ :=
    Multiplicity.source_conclusions E d hUT hf hc f hK m b hpoint hthree (hsum hK) hcardS
  obtain ⟨htwo, hcenter, hderived, hfrattini, hce, hcn⟩ :=
    closure_special E d hUT hf hc hfix
  exact ⟨hK, component_sl3_block E d hUT hf hc, hseed, hUW, ha, hpa, hp,
    hcardS, ⟨Multiplicity.specialFactorEquiv E hWL hfix⟩, hcard,
    hcoreK, hcoreL, hWL, hfix, hcore, hfixed, hz, he, hr,
    htwo, hcenter, hderived, hfrattini, hce, hcn, hsplit⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
