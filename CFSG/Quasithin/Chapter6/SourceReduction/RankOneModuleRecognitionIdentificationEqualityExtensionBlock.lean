module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionContracts

/-!
# The complete equality block and marked S₅ quotient

The involution-cover calculation identifies V with O₂(L). Together with
the elementary centralizer bound and the marked local quotient this
constructs every field of the published block contract. The centralizer
order-four case remains present for the subsequent transfer argument.

Source: Aschbacher–Smith, proof of 6.2.13, printed pp.687–688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The complete block and marked quotient output, with the order-four
alternative retained for the subsequent transfer argument. -/
theorem LocalAnalysis.equality_extension_block
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    EqualityExtensionBlock (T : Subgroup G) L M R z where
  elementary := A.equality_centralizer_elementary h611 hnatural hz horder hTH hbranch
  card := A.equality_centralizer_card h611 hnatural hz horder hTH hbranch
  layer_core := A.equality_layer_eq_core h611 hnatural hz horder hTH hbranch
  kernel_normal := A.equality_local_core_normal h611 hnatural hz horder hTH hbranch
  marked_quotient := A.equality_marked_local_core_quotient h611 hnatural hz horder hTH hbranch

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
