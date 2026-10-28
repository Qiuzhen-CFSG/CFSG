module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Conjugates
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.Construction
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.Normalization
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations

/-!
# Commuting lifts for the local factor count

The E.6.11 block, component Borel and symplectic parabolic models supply
cyclic candidates whose cross commutators lie in the intrinsic two-cores
of local envelopes normalized by all candidates. Independence and
faithfulness of their action images make the generated action kernel a
two-group. A single Schur–Zassenhaus section then constructs commuting
cyclic subgroups inside N_G(U), with the original orders and prescribed
factor images. Their independence follows from `CyclicLifts.independent`.

Only the earlier local component and model conclusions remain explicit
inputs. In particular, no commutator bound, commuting-lift witness, or
two-group centralizer is assumed. The model calculation may replace the
original torus by a regular cyclic subgroup with the same action image.
The exported `factor_count_le_two_of_local_models` connects this
construction to the prime-rank argument. The E.6 owner supplies the earlier
inputs; the remaining E.6.25 branches belong to the local-factor assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11,
printed pp.249–250, and E.6.25, printed p.255 (PDF p.266).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
open Components

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U X L : Subgroup G}
variable [IsElementaryAbelian 2 V]

/-- Construct the genuinely commuting cyclic lifts in the factor-count
paragraph of E.6.25 from the earlier E.6.11 local models. This step needs
only the lower corank bound: the source assumptions about `localM` and
`globalR` are used to obtain the earlier models and in later branches.
All extra premises describe the actual earlier component/block actions;
the local two-core calculations and simultaneous correction are proved. -/
theorem exists_cyclicLifts_of_local_models
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
    Nonempty (CyclicLifts U X D) := by
  obtain ⟨F, B, hn, hc⟩ := exists_local_calculations h earlier hU hX hr D hL hmodels
  exact F.cyclicLifts_of_local_calculations (regularCyclicSection_odd hX (by omega))
    B hn hc

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
