module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Reduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Alignment
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Cubic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Exclusion

/-!
# The paired Suzuki branch of 13.6.6

This module constructs a Borel through the actual intersection and excludes
the moving pair from its genuine component coordinates, Sylow witness, cubic
action and earlier source inputs. The covered Thompson geometry and transport
through an arbitrary aligned marking are proved in the supporting modules.
The literal central quotient, lifted product Borel, action kernel and
superscript residuals are retained, including the Sz(8) central covers.

The assembled interfaces are `PairFactors.false_of_cubic_action` and
`PairFactors.false_of_cubic_field_action`. The parent 13.6.6 assembly still
constructs their actual component pair and cubic actor and discharges the
earlier multiplier, involution-lifting and local-configuration inputs.
The original conditional interface below is retained for existing users.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.6, printed p.927 (PDF p.944).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
open Subgroup ChapterB Stellmacher BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
variable {G : Type*} [Group G] [Finite G]

/-- Assemble the normalizer, residual, and actual field-action arguments.
The omega geometry and compatibility identity are still explicit premises;
their independent producers are required for the complete source branch. -/
theorem false_of_omega_geometry_and_field_action
    {T K L M V : Subgroup G} {v : G} (d : Marking T K v)
    (hKG : K ≤ Gv v) (hZ : IsPGroup 2 (center (orbit T K v)))
    [IsElementaryAbelian 2 (omega T K v)]
    (hJ : elementaryAbelianMaxJ (Tv T v) ≤ centralizer (omega T K v : Set G))
    (hgeom : d.borel ≤ normalizer
      ((Tv T v ⊓ centralizer (omega T K v : Set G) : Subgroup G) : Set G))
    (hS : baumann T ≤ Tv T v)
    (h1325 : normalizer (baumann T : Set G) ≤ M)
    (h1226 : Mv M v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M)
    (haction : IsPiGroup twoThreePrimes (localAction V v).range)
    (hLC : Lv L v ≤ normalizer (M ⊓ centralizer (V : Set G) : Set G))
    (hCL : M ⊓ centralizer (V : Set G) ≤ normalizer (Lv L v : Set G))
    (hkernel : Lv L v ⊓ (M ⊓ centralizer (V : Set G)) ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype)
    (c : G) (hc : c ∈ Lv L v) (hcN : c ∈ normalizer (orbit T K v : Set G))
    (σ : BinaryGaloisField (2 * d.parameter + 1) ≃ₐ[ZMod 2]
      BinaryGaloisField (2 * d.parameter + 1)) (hσ : orderOf σ = 3)
    (hfield : ∀ x : orbit T K v,
      (d.quotientMap ((orbit T K v).normalizerMonoidHom ⟨c, hcN⟩ x)).1 =
        suzukiFieldAut d.parameter σ (d.quotientMap x).1) : False := by
  have hBN := normalizes_baumann_of_omega T K d.borel v hJ hgeom
  have hB := borel_le_localNormalizer d hKG hS h1325 h1226 hMV hBN
  have hcomm := commutator_le_twoCore d hZ hB hMV haction hLC hCL hkernel
  exact cubic_field_contradiction d c hc hcN σ hσ hfield hcomm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
