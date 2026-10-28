module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.Construction
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.Normalization
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.BlockCore
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ConjugateAssembly
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ParabolicCore

/-!
# Local model calculations for the commuting cyclic lifts

All three E.6.11 branches supply the local calculation. The L₂-block proof
uses its actual Borel quotient. Component Borels use their model orders or
torus actions; the symplectic parabolic uses a scalar Levi torus central
modulo its two-core. The common normalization theorem applies the earlier
C-component theorem inside the local normalizer.

When necessary, replace the original cyclic subgroup by a faithful regular
one with the same action image. Conjugating that choice supplies the actual
candidates and envelopes, which are the corresponding conjugates of L ∩ M
inside N_G(V). The algebraic correction then gives the factor bound. The
earlier model and relative C-component conclusions remain explicit source
inputs; no commutator bound or two-group action kernel is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11,
printed pp.249–250, and the proof of E.6.25, printed p.255.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
open Components
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U X L : Subgroup G}
variable [IsElementaryAbelian 2 V]

/-- Actual candidates and local envelopes for the E.6.11 L₂-block branch. -/
theorem exists_local_calculations_l2Block
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hr : 0 < subgroupCorank V U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (hB : L2BlockBorel L ((L ⊓ M).subgroupOf L) (subgroupCorank V U)) :
    ∃ (F : Candidates U X D) (B : Fin D.size → Subgroup (normalizer (V : Set G))),
      (∀ i j, F.subgroup i ≤ normalizer (B j : Set (normalizer (V : Set G)))) ∧
      Pairwise fun i j => ⁅F.subgroup i, F.subgroup j⁆ ≤ (B i).pCoreIn 2 := by
  have hBN : L ⊓ M ≤ normalizer (V : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hL.1)).trans
      (h.localCentralizer_le_normalizer hU.2.1 hU.1)
  apply exists_calculations_of_ambient_control hX D (regularCyclicSection_odd hX hr)
    (L ⊓ M) hBN
  intro A hA ho hc
  exact ⟨odd_normalizes_local_intersection h earlier hU hX hL hA ho hc,
    odd_commutator_le_core_l2Block h earlier hU hX hL hXL hB hA ho hc⟩

/-- The proved block calculation completes the factor count in that branch. -/
theorem factor_count_le_two_l2Block
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hr : 1 < subgroupCorank V U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (hB : L2BlockBorel L ((L ⊓ M).subgroupOf L) (subgroupCorank V U)) : D.size ≤ 2 := by
  obtain ⟨F, B, hn, hc⟩ := exists_local_calculations_l2Block h earlier hU hX
    (by omega) D hL hXL hB
  exact factor_count_le_two_of_local_calculations h hU hX hr F B hn hc

/-- The actual component Borel models supply candidates and local envelopes.
The compatible cyclic replacement preserves the prescribed action factors. -/
theorem exists_local_calculations_componentBorel
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hr : 1 < subgroupCorank V U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hcomp : ComponentIn (centralizer (U : Set G)) L)
    (hB : BorelAlternative M V U L (subgroupCorank V U))
    (hTX : TorusAction M V L X (subgroupCorank V U))
    (hVL : V ≤ normalizer (L : Set G))
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype =
      L ⊓ sylowCentralizer (T : Subgroup G) V) :
    ∃ (F : Candidates U X D) (B : Fin D.size → Subgroup (normalizer (V : Set G))),
      (∀ i j, F.subgroup i ≤ normalizer (B j : Set (normalizer (V : Set G)))) ∧
      Pairwise fun i j => ⁅F.subgroup i, F.subgroup j⁆ ≤ (B i).pCoreIn 2 := by
  obtain ⟨Y, _, hY, himage, hcore⟩ :=
    componentBorel_lift h earlier hU hcomp hL hX hB hTX hr hVL rfl S hS
  have hBN : L ⊓ M ≤ normalizer (V : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hL.1)).trans
      (h.localCentralizer_le_normalizer hU.2.1 hU.1)
  apply exists_calculations_of_replacement hX hY himage D
    (regularCyclicSection_odd hX (by omega)) (L ⊓ M) hBN
  intro A hA ho hc
  exact ⟨odd_normalizes_local_intersection h earlier hU hY hL hA ho hc,
    hcore A hA ho hc⟩

/-- The symplectic scalar Levi torus supplies candidates and local envelopes.
Its commutators lie in the intrinsic parabolic two-core even though the
root centralizer, the parabolic solvable residual, is not a two-group. -/
theorem exists_local_calculations_parabolic
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hr : 1 < subgroupCorank V U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hVL : V ≤ normalizer (L : Set G))
    (hTX : TorusAction M V L X (subgroupCorank V U))
    (hP : MaximalParabolic L (L ⊓ M))
    (hroot : SymplecticRoot L ⁅V, X⁆ (subgroupCorank V U)) :
    ∃ (F : Candidates U X D) (B : Fin D.size → Subgroup (normalizer (V : Set G))),
      (∀ i j, F.subgroup i ≤ normalizer (B j : Set (normalizer (V : Set G)))) ∧
      Pairwise fun i j => ⁅F.subgroup i, F.subgroup j⁆ ≤ (B i).pCoreIn 2 := by
  obtain ⟨Y, _, hY, himage, hcore⟩ :=
    exists_parabolic_core_control h earlier hU hX hr hL hVL hTX hP hroot
  have hBN : L ⊓ M ≤ normalizer (V : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hL.1)).trans
      (h.localCentralizer_le_normalizer hU.2.1 hU.1)
  apply exists_calculations_of_replacement hX hY himage D
    (regularCyclicSection_odd hX (by omega)) (L ⊓ M) hBN
  intro A hA ho hc
  exact ⟨odd_normalizes_local_intersection h earlier hU hY hL hA ho hc,
    hcore A hA ho hc⟩

/-- Construct the E.6.25 local calculations in every E.6.11 model branch.
The explicit model alternatives retain the actual block quotient, component
Borel with its embedded Sylow subgroup, or symplectic matrix root. Only
earlier source conclusions occur in these premises; the local normalization
and two-core commutator bounds are constructed here. -/
theorem exists_local_calculations
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hr : 1 < subgroupCorank V U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hmodels :
      (X ≤ L ∧ L2BlockBorel L ((L ⊓ M).subgroupOf L) (subgroupCorank V U)) ∨
      (ComponentIn (centralizer (U : Set G)) L ∧
        BorelAlternative M V U L (subgroupCorank V U) ∧
        TorusAction M V L X (subgroupCorank V U) ∧
        V ≤ normalizer (L : Set G) ∧
        ∃ S : Sylow 2 L, (S : Subgroup L).map L.subtype =
          L ⊓ sylowCentralizer (T : Subgroup G) V) ∨
      (V ≤ normalizer (L : Set G) ∧
        TorusAction M V L X (subgroupCorank V U) ∧
        MaximalParabolic L (L ⊓ M) ∧ SymplecticRoot L ⁅V, X⁆ (subgroupCorank V U))) :
    ∃ (F : Candidates U X D) (B : Fin D.size → Subgroup (normalizer (V : Set G))),
      (∀ i j, F.subgroup i ≤ normalizer (B j : Set (normalizer (V : Set G)))) ∧
      Pairwise fun i j => ⁅F.subgroup i, F.subgroup j⁆ ≤ (B i).pCoreIn 2 := by
  rcases hmodels with ⟨hXL, hB⟩ | ⟨hcomp, hB, hTX, hVL, S, hS⟩ |
    ⟨hVL, hTX, hP, hroot⟩
  · exact exists_local_calculations_l2Block h earlier hU hX (by omega) D hL hXL hB
  · exact exists_local_calculations_componentBorel h earlier hU hX hr D hL
      hcomp hB hTX hVL S hS
  · exact exists_local_calculations_parabolic h earlier hU hX hr D hL hVL hTX hP hroot

/-- The local model calculations and simultaneous cyclic lifting give the
factor count used in E.6.25. All additional inputs are earlier model outputs,
not assumed bounds on commutators or the action kernel. -/
theorem factor_count_le_two_of_local_models
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hr : 1 < subgroupCorank V U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hmodels :
      (X ≤ L ∧ L2BlockBorel L ((L ⊓ M).subgroupOf L) (subgroupCorank V U)) ∨
      (ComponentIn (centralizer (U : Set G)) L ∧
        BorelAlternative M V U L (subgroupCorank V U) ∧
        TorusAction M V L X (subgroupCorank V U) ∧
        V ≤ normalizer (L : Set G) ∧
        ∃ S : Sylow 2 L, (S : Subgroup L).map L.subtype =
          L ⊓ sylowCentralizer (T : Subgroup G) V) ∨
      (V ≤ normalizer (L : Set G) ∧
        TorusAction M V L X (subgroupCorank V U) ∧
        MaximalParabolic L (L ⊓ M) ∧ SymplecticRoot L ⁅V, X⁆ (subgroupCorank V U))) :
    D.size ≤ 2 := by
  obtain ⟨F, B, hn, hc⟩ := exists_local_calculations h earlier hU hX hr D hL hmodels
  exact factor_count_le_two_of_local_calculations h hU hX hr F B hn hc

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
