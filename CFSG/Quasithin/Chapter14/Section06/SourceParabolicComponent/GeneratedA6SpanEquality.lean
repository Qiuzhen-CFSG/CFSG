module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.StarModule
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedMSInputs
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedEquality
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedA6CoreComparison

/-!
# The original A₆ plane span is the complete moved star module

The first residual moves the source plane and lies in O²(I₀). Hence the
full original plane span is noncentral for that residual component.
The Irr⁺ conclusion of B.5 identifies it with the complete moved star
module. Its order is therefore exactly sixteen or thirty-two, and the
source core comparison identifies it with [Ω₁Z(O₂(I₀)),O²(I₀)].

This removes a module-identification premise from the rank-five crossing
argument. Control of the commutator of the whole two-core remains separate.
Source: Aschbacher–Smith 14.6.10(5), p.1029, using B.5.1 and C.2.7.
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

/-- The literal generated plane span equals the full A₆ moved star module. -/
theorem source_generated_parabolic_a6_span_eq_star_module
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
      conjugateSpanBy (localModule T M) I0 =
        (⁅starV C (I1.pCoreIn 2),C.subgroupOf (C ⊔ I1.pCoreIn 2)⁆).map
          (C ⊔ I1.pCoreIn 2 : Subgroup G).subtype := by
  let A := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype
  let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
  let I0 := (A ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
  let C := (pResidual 2 I0).map I0.subtype
  let U := conjugateSpanBy (localModule T M) I0
  dsimp only
  intro he
  obtain ⟨eC⟩ := he
  obtain ⟨hi,_,_⟩ := source_generated_parabolic_ms_inputs
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  apply ChapterC.C27Source.star_alternatingSix_moved_eq_of_source_ambient hi eC
  · exact source_generated_parabolic_span_le_star_module
      hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
      I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  · exact (map_subtype_le _).trans (le_normalizer_conjugateSpanBy _ _)
  · have hAI0 : A ≤ I0 := le_sup_left.trans le_sup_left
    have hAC : A ≤ C := by
      have hp := (isPPerfect_embedded_pResidual 2 (sourceResidual M Mc ⊓ I)).of_surjective
        (subgroupOfEquivOfLe hAI0).symm.toMonoidHom
        (subgroupOfEquivOfLe hAI0).symm.surjective
      have hh := map_mono (f := I0.subtype) (le_pResidual_of_isPPerfect (A.subgroupOf I0) hp)
      rwa [map_subgroupOf_eq_of_le hAI0] at hh
    intro hc
    have hv : localModule T M ≤ centralizer (A : Set G) :=
      (le_conjugateSpanBy _ I0).trans (hc.trans (centralizer_le hAC))
    have hm := source_parabolic_plane_moved hG T hempty hM hunique hmany hcard e hab
      H hH u hu hindex hmove hproduct hU3 hlocal I hI.1 hout
    have hz : localModule T M = ⊥ := hm.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hv)
    rw [hz,card_bot] at hcard
    omega

/-- The original span has exactly the natural or augmentation-cover order. -/
theorem source_generated_parabolic_a6_span_card
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
      Nat.card (conjugateSpanBy (localModule T M) I0) = 16 ∨
        Nat.card (conjugateSpanBy (localModule T M) I0) = 32 := by
  dsimp only
  intro he
  have hm := source_generated_parabolic_a6_span_eq_star_module
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank he
  obtain ⟨hi,_,_⟩ := source_generated_parabolic_ms_inputs
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  rw [hm,card_map_of_injective (subtype_injective _)]
  exact ChapterC.C27Source.star_alternatingSix_moved_card_from_source hi he.some

/-- The plane span is the commutator of the original two-core omega-center. -/
theorem source_generated_parabolic_a6_span_eq_omegaCore_commutator
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
      conjugateSpanBy (localModule T M) I0 = ⁅omegaOneCenterAmbient (I0.pCoreIn 2),C⁆ := by
  dsimp only
  intro he
  exact (source_generated_parabolic_a6_span_eq_star_module
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank he).trans
    (source_generated_parabolic_residual_core
      hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
      I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank).2
end CFSG.Quasithin.Chapter14.Section06
