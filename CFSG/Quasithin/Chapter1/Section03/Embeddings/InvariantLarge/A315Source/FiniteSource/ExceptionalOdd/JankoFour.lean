module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.JankoFourBounds
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.NormalizerModels

/-!
# Janko four has no full Sylow pair at eleven

The original solvable product has a nontrivial two-core. Its canonical
minimal normal elementary closure lies in the checked matrix kernel. The
order-eight rows are excluded because the product order is prime to seven.
The remaining rows give actual max1 containment, an actual max2 normalizer
equivalence, or containment in the prescribed max4 conjugate. None has the
required prime-square divisor 121. Sylow conjugacy and the original component
isomorphism transport the literal pair throughout.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511; GLS3 Table 5.3i.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
open Janko4 Janko4.OuterReduction.OddIndex Janko4.LocalStructure.SymmetricLinear
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open InvariantThree.SporadicActions.J4Reduction.Source
attribute [local irreducible] Janko4.modelGroup matrixA matrixB

private theorem j4_fixed_no_eleven_pair (B : Subgroup Model) (S : Sylow 2 Model)
    (hS : S.toSubgroup = twoSubgroup) (hB : XiOddQuotient 11 B)
    (hperm : (B : Set Model) * (S : Set Model) = (S : Set Model) * (B : Set Model)) : False := by
  let H := B ⊔ S.toSubgroup
  have h121 : 121 ∣ Nat.card H :=
    (prime_square_dvd_complement hB).trans (card_dvd_of_le (show B ≤ H from le_sup_left))
  have hHN := overgroup_le_elementaryClosure_normalizer S H le_sup_right
  have hnot8 := j4_eleven_closure_card_ne_eight B S hB hperm
  rcases elementaryClosure_catalogue S H le_sup_right hS (j4_eleven_product_twoCore B S hB hperm)
    with hm | h1 | h2 | h3 | h4
  · exact j4_max1_not_eleven_square (h121.trans (card_dvd_of_le hm))
  · have hc : Nat.card (elementaryClosure S H le_sup_right) = 2 := by
      rw [h1,KernelOrders.pureKernelCatalogue.2 1]
      rfl
    obtain ⟨e⟩ := normalizer_equiv_max2_of_closure_card_two S H le_sup_right hc
    have hd := h121.trans (card_dvd_of_le hHN)
    rw [Nat.card_congr e.toEquiv] at hd
    exact j4_max2_not_eleven_square hd
  · rw [h2] at hHN
    have hd := h121.trans (card_dvd_of_le (hHN.trans candidate_two_normalizer_le_max4_conjugate))
    rw [card_map_of_injective (MulAut.conj _).injective] at hd
    exact j4_max4_not_eleven_square hd
  · apply hnot8
    rw [h3,KernelOrders.pureKernelCatalogue.2 3]
    rfl
  · apply hnot8
    rw [h4,KernelOrders.pureKernelCatalogue.2 4]
    rfl

theorem jankoFour_no_eleven_pair (B : Subgroup Model) (S : Sylow 2 Model)
    (hB : XiOddQuotient 11 B)
    (hperm : (B : Set Model) * (S : Set Model) = (S : Set Model) * (B : Set Model)) : False := by
  obtain ⟨T,hT⟩ := (IsPGroup.of_card twoSubgroup_card).exists_le_sylow
  have hTf : T.toSubgroup = twoSubgroup := by
    symm
    apply eq_of_le_of_card_ge hT
    rw [ambient_sylow_card T, twoSubgroup_card]
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S T
  let e := MulAut.conj g
  have hm : (S : Subgroup Model).map e.toMonoidHom = T := by
    change ((g • S : Sylow 2 Model) : Subgroup Model) = _
    rw [hg]
  apply j4_fixed_no_eleven_pair (B.map e.toMonoidHom) T hTf
    (hB.of_mulEquiv (equivMapOfInjective B e.toMonoidHom e.injective))
  have hmSet : ((S : Subgroup Model).map e.toMonoidHom : Set Model) = (T : Set Model) :=
    congrArg (fun U : Subgroup Model => (U : Set Model)) hm
  rw [← hmSet]
  have hpermSub : (B : Set Model) * ((S : Subgroup Model) : Set Model) =
      ((S : Subgroup Model) : Set Model) * (B : Set Model) := hperm
  simpa only [Set.image_mul, ← coe_map] using congrArg (Set.image e.toMonoidHom) hpermSub

variable {κ : GroupClass} {J : Type*} [Group J] [Finite J]
    {D B : Subgroup J} {S : Sylow 2 J}

theorem not_jankoFour
    (hA : OddCartan.AmbientInput κ D B S 11)
    (hB : SourceTransport.PairAction 11 (S : Subgroup J) B)
    (e : D ≃* Model) : False := by
  let : D.Normal := hA.normal
  obtain ⟨U,_,hU,hperm⟩ := exists_model_sylow_pair S hA.inside hB.oddComplement hA.permutes e
  exact jankoFour_no_eleven_pair _ U hU hperm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
