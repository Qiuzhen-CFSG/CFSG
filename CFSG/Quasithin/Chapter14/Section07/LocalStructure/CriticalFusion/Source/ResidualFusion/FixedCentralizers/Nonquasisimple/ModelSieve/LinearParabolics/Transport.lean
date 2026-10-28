module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.LinearParabolics.Applications
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.SubspaceTransport
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.GeometricFlags

/-!
# Transport the actual C.2.7 linear parabolics

Change of basis identifies each SL₃ subspace stabilizer with the full point
or plane parabolic. The literal projective image of a binary flag is carried
by the natural PSL-to-linear equivalence to its linear stabilizer.

For binary five-space, the factor five supplied by the A₅ residual forces
the actual flag to consist of one line or hyperplane. An adapted basis then
identifies this subgroup with the endpoint stabilizer whose two-core quotient
is PSL₄(2). This uses the residual already available to the source consumer;
no additional geometric transport premise is needed in the final exclusions.
The binary-four exclusion is re-exported from `Applications`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.2.7(3)(g,h), pp.145–147; C.1.34, pp.136–137; and 14.7.68(2), pp.1071–1072.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open scoped MatrixGroups Pointwise

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple.LinearParabolics

/-- Identify the source stabilizer with the subgroup defined by the literal matrix action. -/
theorem linearStabilizer_eq_parabolicSL {F : Type*} [Field F] {n : ℕ}
    (W : Submodule F (Fin n → F)) : linearStabilizer W = Matrix.HigherLinear.parabolicSL W := by
  ext g
  rw [linearStabilizer, Subgroup.mem_comap, Submodule.stabilizer_coe,
    MulAction.mem_stabilizer_set]
  rfl

/-- Discharge the pure SL₃ geometric transport contract by a change of basis. -/
theorem linearThreeTransport (F : Type) [Field F] [Finite F] : LinearThreeTransport F := by
  intro W hW hWt
  rw [linearStabilizer_eq_parabolicSL]
  exact Matrix.PSL3.LinearThree.SubspaceTransport.exists_parabolic_equiv W hW hWt

/-- Exclude the full SL₃ parabolic in every even field, including the n=2 source branch. -/
theorem linearThree_false {A M : Type*} [Group A] [Group M] [Finite M]
    (h : HasA5TwoResidual M) (P : Subgroup A) (eM : M ≃* P)
    (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hp : IsLinearMaximalParabolic P 3 F) : False :=
  linearThree_false_of_transport h P eM F hn hF hp (linearThreeTransport F)

/-- The special-linear and binary linear actions preserve the same subspace. -/
theorem binary_mem_linearStabilizer {n : ℕ} (W : Submodule (ZMod 2) (Space n))
    (x : SL(n, ZMod 2)) :
    x ∈ linearStabilizer W ↔ slEquivLinear n x ∈ parabolic W := by
  change Matrix.SpecialLinearGroup.toLin' x ∈
    MulAction.stabilizer (LinearGroup n) W ↔ _
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set]
  rfl

/-- The literal projective image maps onto the full linear flag stabilizer. -/
theorem binaryFlag_map {n k : ℕ} (hn : 0 < n) (f : LinearFlag (ZMod 2) n k) :
    (f.stabilizer.map (QuotientGroup.mk' (center SL(n, ZMod 2)))).map
      (projectiveEquivLinear hn).toMonoidHom = ⨅ i, parabolic (f.space i) := by
  ext g
  obtain ⟨x, rfl⟩ := (slEquivLinear n).surjective g
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
    change projectiveEquivLinear hn (QuotientGroup.mk z) = slEquivLinear n x at hy
    rw [projectiveEquivLinear_mk] at hy
    have hz' : z = x := (slEquivLinear n).injective hy
    subst z
    apply mem_iInf.mpr
    intro i
    exact (binary_mem_linearStabilizer (f.space i) x).mp ((mem_iInf.mp hz) i)
  · intro hx
    refine ⟨QuotientGroup.mk x, ⟨x, ?_, rfl⟩, projectiveEquivLinear_mk hn x⟩
    apply mem_iInf.mpr
    intro i
    exact (binary_mem_linearStabilizer (f.space i) x).mpr ((mem_iInf.mp hx) i)

/-- Restrict the actual PSL-to-linear comparison to the given flag stabilizer. -/
def binaryFlagEquiv {n k : ℕ} (hn : 0 < n) (f : LinearFlag (ZMod 2) n k) :
    (f.stabilizer.map (QuotientGroup.mk' (center SL(n, ZMod 2)))) ≃*
      (⨅ i, parabolic (f.space i) : Subgroup (LinearGroup n)) :=
  ((projectiveEquivLinear hn).subgroupMap _).trans
    (MulEquiv.subgroupCongr (binaryFlag_map hn f))

/-- The restricted equivalence retains the actual projective quotient map. -/
theorem binaryFlagEquiv_apply {n k : ℕ} (hn : 0 < n)
    (f : LinearFlag (ZMod 2) n k)
    (g : f.stabilizer.map (QuotientGroup.mk' (center SL(n, ZMod 2)))) :
    (binaryFlagEquiv hn f g).val = projectiveEquivLinear hn g.val := rfl

/-- Put the actual projective flag in endpoint coordinates using its factor five. -/
theorem binaryFive_coordinates_of_five_dvd {k : ℕ} (hk : 1 ≤ k)
    (f : LinearFlag (ZMod 2) 5 k)
    (hfive : 5 ∣ Nat.card (f.stabilizer.map
      (QuotientGroup.mk' (center SL(5, ZMod 2))))) :
    ∃ (b : FiveBasis) (i : Fin 4), (i = 0 ∨ i = 3) ∧
      flagStabilizer b {i} ≠ ⊤ ∧
      Nonempty ((f.stabilizer.map (QuotientGroup.mk' (center SL(5, ZMod 2)))) ≃*
        flagStabilizer b {i}) := by
  let e := binaryFlagEquiv (by decide : 0 < 5) f
  have hfive' : 5 ∣ Nat.card (⨅ j, parabolic (f.space j) : Subgroup (LinearGroup 5)) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hfive
  obtain ⟨b, i, hi, he⟩ := GeometricFlags.exists_endpoint_coordinates
    (by omega : 0 < k) f.space f.increasing.monotone f.nonzero f.proper hfive'
  refine ⟨b, i, hi, ?_, ⟨e.trans (MulEquiv.subgroupCongr he)⟩⟩
  rw [flagStabilizer_singleton]
  exact FourParabolicAction.parabolic_ne_top (flagSpace_ne_bot b i) (flagSpace_ne_top b i)

/-- Exclude the literal binary-five parabolic with no remaining transport premise. -/
theorem binaryFive_false {A M : Type*} [Group A] [Group M] [Finite M]
    (h : HasA5TwoResidual M) (P : Subgroup A) (eM : M ≃* P)
    (hp : IsBinaryPositiveRankParabolic P 5) : False := by
  obtain ⟨e, k, hk, _, f, he⟩ := hp
  let t := eM.trans ((P.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr he))
  have hfive : 5 ∣ Nat.card (f.stabilizer.map
      (QuotientGroup.mk' (center SL(5, ZMod 2)))) := by
    rw [← Nat.card_congr t.toEquiv]
    exact hasA5TwoResidual_dvd_card h
  obtain ⟨b, i, _, hproper, ⟨ef⟩⟩ := binaryFive_coordinates_of_five_dvd hk f hfive
  exact binaryFive_false_of_coordinates h b {i} hproper (t.trans ef)

/-- Both dimensions in the literal C.2.7(h) alternative are incompatible with the residual. -/
theorem binaryLinear_false {A M : Type*} [Group A] [Group M] [Finite M]
    (h : HasA5TwoResidual M) (P : Subgroup A) (eM : M ≃* P)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hp : IsBinaryPositiveRankParabolic P n) : False := by
  rcases hn with rfl | rfl
  · exact binaryFour_false h P eM hp
  · exact binaryFive_false h P eM hp

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

/-- Discharge the geometric premise in the source's full SL₃(4) model application. -/
theorem fixedComponent_linearThree (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hres : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (n : ℕ) (𝔽 : Type) [Field 𝔽] [Finite 𝔽] (hn : 1 ≤ n)
    (h𝔽 : Nat.card 𝔽 = 2 ^ n)
    (hp : IsLinearMaximalParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu)) 3 𝔽)
    (ms : MSDescription KnownSimple.IsKnownSimple Lu (d.fixedCore u) n 𝔽) :
    n = 2 ∧ Nonquasisimple.IsSLThreeFour (Lu ⧸ pCore 2 Lu) :=
  d.fixedComponent_linearThree_of_transport u h c27 hres n 𝔽 hn h𝔽 hp ms
    (linearThreeTransport 𝔽)

/-- Exclude the actual linear-three source alternative, including n=2. -/
theorem fixedComponent_linearThree_parabolic_false (u : F.U) {Lu : Subgroup G}
    (hres : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (n : ℕ) (𝔽 : Type) [Field 𝔽] [Finite 𝔽] (hn : 1 ≤ n)
    (h𝔽 : Nat.card 𝔽 = 2 ^ n)
    (hp : IsLinearMaximalParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu)) 3 𝔽) : False :=
  linearThree_false hres _
    (subgroupOfEquivOfLe (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm
    𝔽 hn h𝔽 hp

/-- Exclude the actual binary-five source alternative with its literal star residual. -/
theorem fixedComponent_binaryFive_false (u : F.U) {Lu : Subgroup G}
    (_h : Nonquasisimple.Case d u Lu)
    (_c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hres : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (hp : IsBinaryPositiveRankParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu)) 5) : False :=
  binaryFive_false hres _
    (subgroupOfEquivOfLe (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm hp

/-- Discharge C.2.7(h) with its exact disjunction of binary model dimensions. -/
theorem fixedComponent_binaryLinear_false (u : F.U) {Lu : Subgroup G}
    (hres : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hp : IsBinaryPositiveRankParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu)) n) : False :=
  binaryLinear_false hres _
    (subgroupOfEquivOfLe (starM_le Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))).symm hn hp

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

end
