module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.LocalCover
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# The genuine binary triality carrier has no full Sylow pair at seven

The intrinsic product has a nontrivial two-core. Finite Borel–Tits places its
two-local overgroup in a genuine root parabolic. Exact Borel orders and root
parabolic indices show that neither order is divisible by 49. This includes
the original q = 2 carrier, with no perfectness or larger-field premise.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511;
GLS3 Theorem 3.1.3 and Sections 2.6.4–8.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat

abbrev binaryTwo := binaryParameters 1 (by decide)

theorem triality_two_parabolic_not_fortynine_dvd (a : Node) :
    ¬ 49 ∣ Nat.card (parabolic binaryTwo a) := by
  have hc := ((borel binaryTwo).subgroupOf (parabolic binaryTwo a)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (borel_le_parabolic binaryTwo a)).toEquiv,
    FixedCellCount.card_borel 1 (by decide)] at hc
  change binaryTwo.q ^ 12 * ((binaryTwo.q ^ 3 - 1) * (binaryTwo.q - 1)) *
    (borel binaryTwo).relIndex (parabolic binaryTwo a) = _ at hc
  rw [OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at hc
  rw [← hc]
  cases a <;> norm_num [binaryTwo, binaryParameters, Parameters.q]

theorem triality_two_no_seven_pair
    (B : Subgroup (Carrier binaryTwo)) (S : Sylow 2 (Carrier binaryTwo))
    (hB : XiOddQuotient 7 B)
    (hperm : (B : Set (Carrier binaryTwo)) * (S : Set (Carrier binaryTwo)) =
      (S : Set (Carrier binaryTwo)) * (B : Set (Carrier binaryTwo))) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let T := unipotentSylow binaryTwo rfl
  have hT : Nat.card T = 4096 := by
    change Nat.card (unipotent binaryTwo) = _
    rw [card_unipotent_binary binaryTwo rfl]
    norm_num [binaryTwo, binaryParameters, Parameters.q]
  apply no_exceptional_pair_of_local_cover (Or.inr (Or.inl rfl)) T
    (by rw [hT]; norm_num) _ B S hB hperm
  intro M hM _ hd
  obtain ⟨g,a,hg⟩ := TwoLocalCover.maximalTwoLocal_cover 1 (by decide) M hM
  apply triality_two_parabolic_not_fortynine_dvd a
  have hm : 49 ∣ Nat.card (M.map (MulAut.conj g).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hd
  exact hm.trans (card_dvd_of_le hg)

variable {κ : GroupClass} {J : Type*} [Group J] [Finite J]
    {D B : Subgroup J} {S : Sylow 2 J}

theorem not_triality_two
    (hA : OddCartan.AmbientInput κ D B S 7)
    (hB : SourceTransport.PairAction 7 (S : Subgroup J) B)
    (hD : IsTrialityGroupAt 2 D) : False := by
  let : D.Normal := hA.normal
  obtain ⟨e⟩ := (isTrialityGroupAt_two_iff D).mp hD
  obtain ⟨U,_,hU,hperm⟩ := exists_model_sylow_pair S hA.inside hB.oddComplement hA.permutes e
  exact triality_two_no_seven_pair _ U hU hperm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
