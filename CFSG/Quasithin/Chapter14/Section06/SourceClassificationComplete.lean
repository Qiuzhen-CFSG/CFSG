module
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationInputs
public import Theory.GroupTheory.ConjugateSpanSupplement
public import CFSG.Quasithin.Chapter14.Section06.SourceFactorizationComplete
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableNormalizer.LocalSylow
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedNaturalSixComplete

/-!
# The common terminal contradiction of original section 14.6

Choose a maximal-intersection outside subgroup, preferring C_G(u) when its
Sylow intersection is minimal. Original 14.6.9 supplies the residual product,
which forces the first intersection parabolic to escape Mc. Thus the actual
rank-three theorem applies without an extra escape or local Sylow premise.
The residual span of rank four equals the second-parabolic span, contradicting
that theorem. Both the solvable endgame and the final component endgame use
this same argument.

The full rank-three source and existence of the terminal witness remain
explicit independent inputs. The alternating-six block case is discharged
here by the existing original module calculation.
Source: Aschbacher--Smith, endgames on printed pp.1036--1037 and 1042.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))


/-- The completed residual product supplies the escape required by the
second-parabolic module analysis, at every actual IStar choice. -/
theorem source_second_parabolic_intersection_escape
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M)) :
    ¬ I ⊓ M ≤ Mc := by
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hcover := (source_factorizations hG T hempty hM hunique hmany hcard e hab H hH
    d.u d.mem_span d.index d.moves_core d.product_moves_core d.local_normalizer hlocal
    d.core_index d.module_rank I hI).1
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.index d.moves_core d.product_moves_core d.local_normalizer
    hlocal I hI.1).1
  have hout := (source_intersection_parabolic_data hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.index d.moves_core d.product_moves_core I hI.1.2.1
    hSyl hcover).2.2.2
  intro hIM
  apply hout
  exact (le_inf ((map_subtype_le _).trans inf_le_right)
    (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc))).trans hIM

/-- Adjoining the chosen Sylow intersection does not change the residual
span. This identifies the two span conventions in the printed endgames. -/
theorem source_second_parabolic_span_eq_residual_span
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M)) :
    conjugateSpanBy (localModule T M)
      ((pResidual 2 d.H2).map d.H2.subtype ⊔ ((T : Subgroup G) ⊓ I)) =
    conjugateSpanBy (localModule T M) ((pResidual 2 d.H2).map d.H2.subtype) := by
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hS0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique
    hmany hcard e hab H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
    d.local_normalizer hlocal I hI.1
  have hSH2 : (T : Subgroup G) ⊓ I ≤ d.H2 := by
    obtain ⟨S,hS⟩ := d.quotient_sylow
    exact hS0.trans (hS ▸ map_subtype_le (S : Subgroup d.H2))
  apply conjugateSpanBy_sup_of_normalizes_seed
  · exact (inf_le_left.trans hM.1.2).trans (le_normalizer_conjugateSpanBy _ _)
  · exact hSH2.trans (d.H2.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.H2 (pResidual 2 d.H2)))

/-- The natural alternating-six branch of the exact remaining rank-three
contract, with escape and local Sylow hypotheses discharged internally. -/
theorem source_second_parabolic_rank_three_of_alternating_block
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))
    (hpreferred : (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({d.u} : Set G) →
      I ≤ centralizer ({d.u} : Set G))
    :
    let I2 := (pResidual 2 d.H2).map d.H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
    let I0 := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
    ChapterC.IsAlternatingBlock ((pResidual 2 I0).map I0.subtype) 6 →
      primeRank 2 (conjugateSpanBy (localModule T M) I2) = 3 := by
  dsimp only
  intro hblock
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  exact (source_generated_parabolic_naturalSix_rank_three hG T hempty hM hunique hmany
    hcard e hab H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
    d.local_normalizer hlocal I d.H2 hI
    (source_second_parabolic_intersection_escape hG T hempty hM hunique hmany hcard e hab H hH d I hI)
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside d.core_index
    d.module_rank hpreferred hblock).2.2

/-- The two original rank contradictions use the same preferred choice and
the equality of the literal residual and second-parabolic spans. -/
theorem source_terminal_contradiction
    (hthree : SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab)
    (hwitness : SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab) : False := by
  obtain ⟨H,hH,d,houtside,hfour⟩ := hwitness
  let : Finite (Subgroup G) :=
    Finite.of_injective (fun A : Subgroup G => (A : Set G)) SetLike.coe_injective
  obtain ⟨I,hI,hpreferred⟩ := exists_iStar_preferred
    (T := (T : Subgroup G))
    (S := (T : Subgroup G) ⊓ centralizer ({d.u} : Set G))
    (Set.toFinite _) houtside inf_le_right
  have hthreeI := hthree H hH d I hI (fun he => (hpreferred he).le)
  rw [source_second_parabolic_span_eq_residual_span hG T hempty hM hunique hmany
    hcard e hab H hH d I hI] at hthreeI
  omega

end CFSG.Quasithin.Chapter14.Section06
