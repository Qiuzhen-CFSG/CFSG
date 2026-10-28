module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedA6SpanEquality
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.NaturalSixSpan
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedCoordinates
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The actual order-sixteen A₆ source branch

The original generated plane span equals the moved star module. In its
order-sixteen branch, B.5 supplies coordinates on the whole span, with the
literal conjugation action of O²(I₀). The original Sylow intersection fixes
the source point and plane; the second parabolic centralizes the point and
moves the plane. Natural symplectic geometry therefore gives its conjugate
span order eight and rank three.

No alternating-block or whole-core reconstruction premise is used. Together
with the proved order-sixteen-or-thirty-two alternative, this reduces the
A₆ source row to the genuine rank-five central-cover branch.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029, with B.5 and C.2.7.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
universe u
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {G : Type u} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal

/-- The actual order-sixteen A₆ star branch has a rank-three second span. -/
theorem source_generated_parabolic_a6_rank_three_of_card
    (I H2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hSylH2 : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u) H2)
    (hH2kernel : H2 ≤
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).kernel (zpowers u))
    (hH2quot : Nonempty ((H2 ⧸ pCore 2 H2) ≃* Equiv.Perm (Fin 3)))
    (hH2out : ¬ H2 ≤ M)
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
    let I0 := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
      (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)
    let C := (pResidual 2 I0).map I0.subtype
    Nonempty (starImage C (I1.pCoreIn 2) C ≃* alternatingGroup (Fin 6)) →
      Nat.card (conjugateSpanBy (localModule T M) I0) = 16 →
      IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) I2) ∧
        Nat.card (conjugateSpanBy (localModule T M) I2) = 8 ∧
        primeRank 2 (conjugateSpanBy (localModule T M) I2) = 3 := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let A := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype
  let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
  let I0 := (A ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
  let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
    (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)
  let C := (pResidual 2 I0).map I0.subtype
  let W := (⁅starV C (I1.pCoreIn 2),C.subgroupOf (C ⊔ I1.pCoreIn 2)⁆).map
    (C ⊔ I1.pCoreIn 2 : Subgroup G).subtype
  dsimp only
  intro he hcardU
  obtain ⟨hi,_,_⟩ := source_generated_parabolic_ms_inputs
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  have hUW : conjugateSpanBy (localModule T M) I0 = W :=
    source_generated_parabolic_a6_span_eq_star_module
      hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
      I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank he
  have hcW : Nat.card W = 16 := by rw [←hUW]; exact hcardU
  obtain ⟨f,hf,q,ha⟩ := ChapterC.C27Source.star_alternatingSix_natural_coordinates_ambient
    hi he.some hcW
  obtain ⟨hI0,hS,hgen,hI2H2,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  have hH2H : H2 ≤ H := fun x hx =>
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp (hH2kernel hx)).1
  have hI2H : I2 ≤ H := hI2H2.trans hH2H
  have hI2M : ¬ I2 ≤ M := by
    intro hh
    apply hI0.1.2.2.2
    exact sup_le (sup_le (((map_subtype_le _).trans inf_le_left).trans
      (sourceResidual_le M Mc)) (inf_le_left.trans hM.1.2)) hh
  have hCI : C ≤ I0 := map_subtype_le _
  have hIC : I0 ≤ normalizer (C : Set G) := I0.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I0 (pResidual 2 I0))
  have hIW : I0 ≤ normalizer (W : Set G) := by
    rw [←hUW]
    exact le_normalizer_conjugateSpanBy _ _
  have hVW : localModule T M ≤ W := hUW ▸ le_conjugateSpanBy _ I0
  have hZV : centralInvolutions T ≤ localModule T M := le_conjugateSpanBy _ _
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I0 hI0.1).1
  have hCN : (C.subgroupOf I0).Normal := normal_subgroupOf_of_le_normalizer hIC
  obtain ⟨S,hSC⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hCI
    hCN.isSubnormal
  have hST : (S : Subgroup C).map C.subtype ≤ (T : Subgroup G) :=
    hSC.le.trans (inf_le_left.trans inf_le_left)
  have hTV : (T : Subgroup G) ≤ normalizer (localModule T M : Set G) :=
    hM.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have hTZ : (T : Subgroup G) ≤ normalizer (centralInvolutions T : Set G) :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hI2Z : I2 ≤ centralizer (centralInvolutions T : Set G) :=
    hI2H.trans (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).2
  have hm : ¬ I2 ≤ normalizer (localModule T M : Set G) := by
    rwa [← InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
  have hc := NaturalSixSpan.span_card_of_natural_component I0 C W hCI hIC hIW
    f hf q ha (localModule T M) (centralInvolutions T) I2 le_sup_right hVW
    (hZV.trans hVW) hcard (plane_centralInvolutions_card T M hM.1.2 hcard e)
    S (hST.trans hTV) (hST.trans hTZ) hI2Z hm
  let V0 := conjugateSpanBy (localModule T M) I2
  let : IsElementaryAbelian 2 (Multiplicative (BinaryPermutation.natural (Fin 6))) :=
    Representation.BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective q.toMonoidHom q.injective
  let : IsElementaryAbelian 2 V0 := IsElementaryAbelian.of_le
    (conjugateSpanBy_le hVW (le_sup_right.trans hIW))
  refine ⟨inferInstance,hc,?_⟩
  apply le_antisymm
  · exact IsElementaryAbelian.primeRank_le_of_card_le V0 (n := 3) (by rw [hc]; decide)
  · let : IsElementaryAbelian 2 (⊤ : Subgroup V0) := IsElementaryAbelian.of_injective
      (⊤ : Subgroup V0).subtype (⊤ : Subgroup V0).subtype_injective
    exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup V0)
      ((Nat.card_congr (topEquiv : (⊤ : Subgroup V0) ≃* V0).toEquiv).trans hc)

/-- The A₆ source row is reduced to its genuine order-thirty-two branch. -/
theorem source_generated_parabolic_a6_rank_three_or_rank_five
    (I H2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hSylH2 : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u) H2)
    (hH2kernel : H2 ≤
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).kernel (zpowers u))
    (hH2quot : Nonempty ((H2 ⧸ pCore 2 H2) ≃* Equiv.Perm (Fin 3)))
    (hH2out : ¬ H2 ≤ M)
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
    let I0 := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
      (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)
    let C := (pResidual 2 I0).map I0.subtype
    Nonempty (starImage C (I1.pCoreIn 2) C ≃* alternatingGroup (Fin 6)) →
      (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) I2) ∧
        Nat.card (conjugateSpanBy (localModule T M) I2) = 8 ∧
        primeRank 2 (conjugateSpanBy (localModule T M) I2) = 3) ∨
      Nat.card (conjugateSpanBy (localModule T M) I0) = 32 := by
  dsimp only
  intro he
  rcases source_generated_parabolic_a6_span_card
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank he with hc | hc
  · exact Or.inl (source_generated_parabolic_a6_rank_three_of_card
      hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
      I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank he hc)
  · exact Or.inr hc

end CFSG.Quasithin.Chapter14.Section06
