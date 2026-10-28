module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Rudvalis.SevenReduction
public import Theory.GroupAction.AutomorphismNormalizer
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer

/-!
# The remaining inputs to the Rudvalis pair-fixer bound

The checked permutation-normalizer calculation already supplies one half of
all-automorphism innerness. Invariance of the actual degree-4060 point-stabilizer
class supplies the other half. Combine these with the reduction through the
actual quotient cover and its embedded Suzuki subgroup.

The stabilizer-class and intrinsic element-centralizer assertions remain
explicit obligations below. The final reduction needs only the centralizer of
an element of order seven modulo its actual cyclic subgroup. This is conditional assembly, not a completed
proof of the Rudvalis row or of source 16.3.5. In particular the shape of a
single involution centralizer does not identify the full embedded-pair fixer.

Source: Aschbacher–Smith 16.1.5(11), 16.1.7(3i), and 16.3.5,
printed pp.1172–1173 and 1178–1179 (1 March 2004 manuscript);
GLS3 Table 5.3r, printed p.279.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.RudvalisPair
open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G] {𝒦 : GroupClass}
variable {E L I : Subgroup G} {t i : G}

/-- The existing permutation-normalizer theorem discharges that part of the
innerness calculation. The two other model calculations remain prerequisites. -/
theorem rudvalisBound_of_stabilizerClass_of_elementCentralizers
    (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (hstable : ∀ (_ : IsSimpleGroup Model) (_ : Group.IsPerfect Model)
      (a : MulAut Model), ∃ y : Fin 4060,
      (MulAction.stabilizer Model (0 : Fin 4060)).map a.toMonoidHom =
        MulAction.stabilizer Model y)
    (hb : ∀ (_ : IsSimpleGroup Model) (_ : Group.IsPerfect Model),
      ElementCentralizerBound) : RudvalisBound L I := by
  apply rudvalisBound_of_inner_of_elementCentralizers h hG _ hb
  intro hs hp
  let : MulAction.IsPretransitive _root_.Rudvalis.modelSubgroup (Fin 4060) :=
    _root_.Rudvalis.model_isPretransitive
  exact Subgroup.conj_surjective_of_stabilizers_of_normalizer
    _root_.Rudvalis.modelSubgroup 0 (hstable hs hp)
    _root_.Rudvalis.outer_permutation_normalizer_eq

/-- A sufficient pair of independent intrinsic inputs: stabilizer-class invariance
for all automorphisms, and the actual order-seven centralizer projection.
The quotient cover, embedding of Sz(8), and numerical/action transfers are
all discharged by the preceding reductions. -/
theorem rudvalisBound_of_stabilizerClass_of_sevenCentralizers
    (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (hstable : ∀ (_ : IsSimpleGroup Model) (_ : Group.IsPerfect Model)
      (a : MulAut Model), ∃ y : Fin 4060,
      (MulAction.stabilizer Model (0 : Fin 4060)).map a.toMonoidHom =
        MulAction.stabilizer Model y)
    (hseven : ∀ (_ : IsSimpleGroup Model) (_ : Group.IsPerfect Model),
      SevenCentralizerProjection) : RudvalisBound L I := by
  exact rudvalisBound_of_stabilizerClass_of_elementCentralizers h hG hstable
    (fun hs hp => elementCentralizerBound_of_sevenCentralizers (hseven hs hp))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.RudvalisPair
