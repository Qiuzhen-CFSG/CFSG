module
public import Theory.Mathieu.M22.TripleCover
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Theory.GroupTheory.CoprimeInvolutionFusion
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimePowerDecomposition
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension.Matrix
/-!
# Two-rank and involution fusion for the genuine triple Mathieu actors

The native maps from the cover to M22 and from its matrix extension to Aut(M22)
have kernels of order three. Coprime-kernel rank transport gives bounds four and
five, and dihedral odd-kernel lifting transports the native involution fusion.
All statements concern the original matrix groups.
Source: Aschbacher--Smith H.12.1(7),(11), printed pp.393--395.
-/
public section
noncomputable section
open Sporadic.Mathieu Theory.GroupTheory
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
namespace Sporadic.Mathieu.M22TripleCover.NoFF
private def nativeQuotient : M22TripleCover →* M22 :=
  centralQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center M22TripleCover))
private lemma nativeQuotient_surjective : Function.Surjective nativeQuotient :=
  centralQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
private lemma nativeQuotient_ker : nativeQuotient.ker = Subgroup.center M22TripleCover := by
  change (centralQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' _)).ker = _
  exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' _) centralQuotientEquiv.toMonoidHom centralQuotientEquiv.injective).trans (QuotientGroup.ker_mk' _)
private lemma nativeQuotient_coprime : Nat.Coprime 2 (Nat.card nativeQuotient.ker) := by
  rw [nativeQuotient_ker, center_card]
  decide
lemma twoRank_le_four : primeRank 2 M22TripleCover ≤ 4 :=
  (primeRank_le_of_coprime_ker 2 nativeQuotient nativeQuotient_coprime).trans m22_twoRank_le_four
lemma ambient_twoRank_le_five : primeRank 2 actionGroup ≤ 5 := by
  apply (primeRank_le_of_coprime_ker 2 quotientConjugation ?_).trans m22_automorphism_twoRank_le_five
  rw [quotientConjugation_ker, scalarSubgroup_card]
  decide
lemma involutions_isConj (x y : M22TripleCover) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  apply nativeQuotient.isConj_of_map_isConj_of_involutions_of_odd_ker
    nativeQuotient_surjective nativeQuotient_coprime hx hy
  apply m22_involutions_isConj
  · rw [nativeQuotient.orderOf_eq_of_prime_power_of_coprime_ker nativeQuotient_coprime x
      ⟨1, by simpa only [pow_one, hx] using pow_orderOf_eq_one x⟩, hx]
  · rw [nativeQuotient.orderOf_eq_of_prime_power_of_coprime_ker nativeQuotient_coprime y
      ⟨1, by simpa only [pow_one, hy] using pow_orderOf_eq_one y⟩, hy]
end Sporadic.Mathieu.M22TripleCover.NoFF
