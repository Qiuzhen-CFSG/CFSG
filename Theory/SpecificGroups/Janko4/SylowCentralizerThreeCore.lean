module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.SylowIndex
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.GroupTheory.QuasithinBasic

/-!
# The cubic core in a Sylow-central J₄ involution centralizer

The full first centralizer quotient is the actual matrix extension 3.M₂₂.2.
Its map onto Aut(M₂₂) has the scalar subgroup of order three as kernel.
The centerless simple M₂₂ has trivial three-core, so the automorphism
core argument identifies that scalar subgroup with the entire three-core
of the quotient. In particular it has three-rank at most one.

The certified involution-class and Sylow-index comparison transports this
bound to every involution centralizing a full Sylow two-subgroup. Both the
two-core quotient and the cubic kernel are retained.
Source: GLS3 Table 5.3i; Aschbacher–Smith 12.6.26, printed p.832,
the J₄ row in the final rank-two inspection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.InvolutionCentralizers.First
open QuotientExtension Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

theorem quotient_threeCore_eq_scalar : pCore 3 actionGroup = scalarSubgroup := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : Group.IsPerfect M22 := Group.IsPerfect.ofSurjective
    (f := M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
      (QuotientGroup.mk' (center M22TripleCover)))
    (M22TripleCover.centralQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  have hp : pCore 3 M22 = ⊥ := by
    rcases (inferInstance : (pCore 3 M22).Normal).eq_bot_or_eq_top with h|h
    · exact h
    · have hP : IsPGroup 3 M22 :=
        (show IsPGroup 3 (⊤ : Subgroup M22) from h ▸ pCore_isPGroup).of_equiv topEquiv
      let : Group.IsNilpotent M22 := hP.isNilpotent
      exact (Group.IsPerfect.not_isSolvable M22 inferInstance).elim
  have hk : IsPGroup 3 quotientConjugation.ker := by
    rw [quotientConjugation_ker]
    exact IsPGroup.of_card (n := 1) (by simpa only [pow_one] using scalarSubgroup_card)
  exact (core_eq_kernel_of_action 3 (Theory.GroupTheory.conj_injective_of_center_eq_bot m22_center_eq_bot)
    hp quotientConjugation (fun x => quotientConjugation_surjective (MulAut.conj x)) hk).trans
      quotientConjugation_ker

theorem quotient_threeCore_card : Nat.card (pCore 3 (centralizer ⧸ pCore 2 centralizer)) = 3 := by
  let e := (quotientEquiv.subgroupMap (pCore 3 _)).trans
    (MulEquiv.subgroupCongr ((pCore_map_iso 3 quotientEquiv).trans quotient_threeCore_eq_scalar))
  exact (Nat.card_congr e.toEquiv).trans scalarSubgroup_card

theorem quotient_threeCore_rank : primeRank 3 (pCore 3 (centralizer ⧸ pCore 2 centralizer)) ≤ 1 := by
  apply primeRank_le_one_of_square_not_dvd
  rw [quotient_threeCore_card]
  decide
end Janko4.InvolutionCentralizers.First

namespace Janko4.InvolutionCentralizers
open Subgroup Theory.GroupTheory
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The full cubic kernel is retained in the two-central involution quotient. -/
theorem sylow_fixed_centralizer_quotient_threeCore_rank
    (t : Model) (ht : orderOf t = 2) (P : Sylow 2 Model)
    (hP : (P : Subgroup Model) ≤ centralizer ({t} : Set Model)) :
    primeRank 3 (pCore 3 (centralizer ({t} : Set Model) ⧸
      pCore 2 (centralizer ({t} : Set Model)))) ≤ 1 := by
  obtain ⟨e⟩ := centralizer_equiv_first_of_sylow_index_le_two t ht P
    (by rw [relIndex_eq_one.mpr hP]; decide)
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let c := (q.subgroupMap (pCore 3 _)).trans (MulEquiv.subgroupCongr (pCore_map_iso 3 q))
  rw [primeRank_equiv 3 c]
  exact First.quotient_threeCore_rank
end Janko4.InvolutionCentralizers

