module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneTransport
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarFullEnlargement
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourWeakClosure

/-!
# The original full reduced Hermitian module

When the actual full R₂(LT) is Hermitian, its nonzero moved layer exhausts
it by irreducibility. The original enlarged Hypothesis 6.1.1 then gives
E.6.1 and the exact centralizer kernel on that same full module. No equality
between a proper original layer and R₂ is assumed.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n s : ℕ} [NeZero s]
local instance fullReducedFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance fullReducedBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- Irreducibility and the original noncentrality make the full reduced
Hermitian module equal to its actual moved layer. -/
theorem full_reduced_hermitian_layer_eq
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) :
    layer L (reducedSubgroup (L ⊔ (T : Subgroup G))) =
      reducedSubgroup (L ⊔ (T : Subgroup G)) := by
  have hR := h.reduced_enlargement
  exact (hermitian_invariant_subgroup hm _ hR.layer_le_V
    (normalizer_commutator_ge_right _ _)).resolve_left hR.nontrivial_action

/-- E.6.1 holds on the literal full reduced module in its Hermitian branch. -/
theorem full_reduced_hermitian_hypothesisE61
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M
      (reducedSubgroup (L ⊔ (T : Subgroup G))) := by
  have he := full_reduced_hermitian_layer_eq h hm
  have hm' := hm
  rw [←he] at hm'
  simpa only [he] using original_hermitian_layer_hypothesisE61 h.reduced_enlargement hm'

/-- The actual Sylow centralizer of full R₂ is O₂(LT). -/
theorem full_reduced_hermitian_sylow_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) :
    (T : Subgroup G) ⊓ centralizer (reducedSubgroup (L ⊔ (T : Subgroup G)) : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have he := full_reduced_hermitian_layer_eq h hm
  have hm' := hm
  rw [←he] at hm'
  simpa only [he,ChapterE.Section06.sylowCentralizer] using original_hermitian_layer_sylow_centralizer h.reduced_enlargement hm'

/-- Every actual hyperplane of the full Hermitian reduced module has the
same centralizer in the original T, with no action-kernel premise. -/
theorem full_reduced_hermitian_hyperplane_sylow_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (U : Subgroup G) (hU : U ≤ reducedSubgroup (L ⊔ (T : Subgroup G)))
    (hcor : ChapterE.subgroupCorank (reducedSubgroup (L ⊔ (T : Subgroup G))) U = 1) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      (T : Subgroup G) ⊓ centralizer (reducedSubgroup (L ⊔ (T : Subgroup G)) : Set G) :=
  (h.reduced_enlargement.rankOneInput hout).hermitian_hyperplane_sylow_centralizer
    hm hs U hU hcor

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
