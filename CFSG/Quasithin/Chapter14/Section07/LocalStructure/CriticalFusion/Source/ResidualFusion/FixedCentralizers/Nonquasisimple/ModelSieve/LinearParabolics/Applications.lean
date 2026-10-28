module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.LinearParabolics.Coordinates

/-!
# Actual C.2.7 applications and geometric transport contracts

The residual belongs to M* in the star quotient. Restriction to the component
is transported by `subgroupOfEquivOfLe`, and the model map is restricted to
that literal subgroup. This preserves the source quotient maps and relative
subgroup convention. The binary-four comparison is unconditional beyond the
permitted A₅ residual input.

The conditional linear-three and binary-five applications below take pure
geometric transport propositions concerning subspace or flag stabilizers.
The descendant `Transport` proves the linear-three contract and completes
binary five-space directly: the residual's factor five puts its actual flag
in endpoint coordinates. Its final applications have no geometric premise.
The full SL₃(4) core-quotient model comes from `MSDescription.1.model`.

Source: Aschbacher–Smith, C.2.7(3)(g,h), printed pp.145–147; C.1.34,
pp.136–137; and 14.7.68(2), pp.1071–1072, combined manuscript (1 March 2004).
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple.LinearParabolics

/-- Pure subspace geometry: put a nonzero proper three-space stabilizer in point or plane coordinates. -/
def LinearThreeTransport (F : Type) [Field F] [Finite F] : Prop :=
  ∀ W : Submodule F (Fin 3 → F), W ≠ ⊥ → W ≠ ⊤ →
    Nonempty (linearStabilizer W ≃* pointParabolicSL F) ∨
      Nonempty (linearStabilizer W ≃* lineParabolicSL F)

/-- Pure flag geometry, retaining the actual projective map, nonempty proper flag and positive rank. -/
def BinaryFiveTransport : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ 5 - 2 → ∀ f : LinearFlag (ZMod 2) 5 k,
    ∃ (b : FiveBasis) (cuts : Set (Fin 4)), flagStabilizer b cuts ≠ ⊤ ∧
      Nonempty ((f.stabilizer.map
        (QuotientGroup.mk' (center SL(5, ZMod 2)))) ≃* flagStabilizer b cuts)

/-- Apply the scalar-quotient contradiction through the given geometric transport. -/
theorem linearThree_false_of_transport {A M : Type*} [Group A] [Group M] [Finite M]
    (h : HasA5TwoResidual M) (P : Subgroup A) (eM : M ≃* P)
    (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hp : IsLinearMaximalParabolic P 3 F)
    (hc : LinearThreeTransport F) : False := by
  obtain ⟨e, W, hW, hWt, he⟩ := hp
  let t := eM.trans ((P.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr he))
  apply linearThree_false_of_coordinates h F hn hF
  rcases hc W hW hWt with hw | hw
  · obtain ⟨ew⟩ := hw
    exact Or.inl ⟨t.trans ew⟩
  · obtain ⟨ew⟩ := hw
    exact Or.inr ⟨t.trans ew⟩

/-- Apply the end-parabolic order contradiction through the given geometric transport. -/
theorem binaryFive_false_of_transport {A M : Type*} [Group A] [Group M] [Finite M]
    (h : HasA5TwoResidual M) (P : Subgroup A) (eM : M ≃* P)
    (hp : IsBinaryPositiveRankParabolic P 5) (hc : BinaryFiveTransport) : False := by
  obtain ⟨e, k, hk, hk', f, he⟩ := hp
  let t := eM.trans ((P.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr he))
  obtain ⟨b, cuts, hproper, ⟨ef⟩⟩ := hc k hk hk' f
  exact binaryFive_false_of_coordinates h b cuts hproper (t.trans ef)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple.LinearParabolics

open Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open Nonquasisimple Nonquasisimple.LinearParabolics
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The literal linear-three alternative gives n=2 and the full core-quotient model.
The descendant `Transport` discharges the geometric premise. -/
theorem fixedComponent_linearThree_of_transport (u : F.U) {Lu : Subgroup G}
    (_h : Nonquasisimple.Case d u Lu)
    (_c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hres : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (n : ℕ) (𝔽 : Type) [Field 𝔽] [Finite 𝔽] (hn : 1 ≤ n)
    (h𝔽 : Nat.card 𝔽 = 2 ^ n)
    (hp : IsLinearMaximalParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu)) 3 𝔽)
    (ms : MSDescription KnownSimple.IsKnownSimple Lu (d.fixedCore u) n 𝔽)
    (hc : LinearThreeTransport 𝔽) :
    n = 2 ∧ Nonquasisimple.IsSLThreeFour (Lu ⧸ pCore 2 Lu) := by
  have hn2 : n = 2 := (linearThree_false_of_transport hres _
    (subgroupOfEquivOfLe (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm
    𝔽 hn h𝔽 hp hc).elim
  refine ⟨hn2, 𝔽, inferInstance, inferInstance, ?_, ms.1.model⟩
  simpa [hn2] using h𝔽

/-- The actual binary-five alternative is impossible once its flag is put in coordinates. -/
theorem fixedComponent_binaryFive_false_of_transport (u : F.U) {Lu : Subgroup G}
    (_h : Nonquasisimple.Case d u Lu)
    (_c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hres : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (hp : IsBinaryPositiveRankParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu)) 5)
    (hc : BinaryFiveTransport) : False := by
  exact binaryFive_false_of_transport hres _
    (subgroupOfEquivOfLe (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm
    hp hc

/-- The four-dimensional branch is excluded directly for the literal star quotient. -/
theorem fixedComponent_binaryFour_false (u : F.U) {Lu : Subgroup G}
    (_h : Nonquasisimple.Case d u Lu)
    (_c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hres : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (hp : IsBinaryPositiveRankParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu)) 4) : False := by
  exact binaryFour_false hres _
    (subgroupOfEquivOfLe (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm
    hp
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

end
