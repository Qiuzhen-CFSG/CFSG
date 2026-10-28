module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Recognition
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointOrbitCardinality
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core

/-!
# Native cover rows and the full Janko Sylow

The proved linear-five quotient and its literal elementary kernel give the
normalizer order. Its two-part is too small to contain a full Sylow of J4.
The certified ATLAS conjugating word identifies the second native cover row
with the first involution centralizer as an equality of embedded subgroups.
Both facts are used on the original parabolic and actor in the exterior
local-normalizer source argument; abstract model isomorphisms do not suffice.

Source: Aschbacher--Smith 12.5.4, printed p.819; the native linear-five
recognition and ATLAS conjugator retain the imported source attribution.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LinearFive
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

theorem fullNormalizer_card : Nat.card fullNormalizer = 1024 * 9999360 := by
  have hc := normalizerKernel.card_mul_index
  rw [index_eq_card, Nat.card_congr normalizerQuotient.toEquiv,
    Representation.SL5ExteriorSquare.card_specialLinearFive] at hc
  have hk : Nat.card normalizerKernel = 1024 :=
    (Nat.card_congr (subgroupOfEquivOfLe F.le_normalizer).toEquiv).trans F_card
  rw [hk] at hc
  exact hc.symm

theorem not_sylow_le_fullNormalizer (S : Sylow 2 Model) :
    ¬ (S : Subgroup Model) ≤ fullNormalizer := by
  intro hs
  have h2 : 2^21 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 21) (by
    rw [Cardinality.model_card]
    decide)
  have hd := h2.trans (card_dvd_of_le hs)
  rw [fullNormalizer_card] at hd
  norm_num at hd

end Janko4.LocalStructure.LinearFive

namespace Janko4.LocalStructure.NativeCoverTransport
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The certified ATLAS conjugator identifies the second cover row with
its literal first-involution centralizer, as subgroups of the same model. -/
theorem sourceSubgroup_map_conj_firstCentralizer :
    sourceSubgroup.map (MulAut.conj h⁻¹).toMonoidHom =
      InvolutionCentralizers.First.centralizer := by
  rw [sourceSubgroup_map_conj, localSubgroup_eq_top, ← MonoidHom.range_eq_map,
    centralizerToModel_range]

end Janko4.LocalStructure.NativeCoverTransport
