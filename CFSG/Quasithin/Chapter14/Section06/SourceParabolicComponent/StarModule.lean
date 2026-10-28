module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedModule
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.ResidualModule

/-!
# The original generated plane module in the actual star module

Let C = O²(I) and J = CR₁. The full I-span U of the source plane is moved
by C and lies in Ω₁Z(O₂(I)). Movement puts U in C, while J is subnormal
because it contains O²(I). Therefore O₂(J) lies in O₂(I), and U belongs
to Ω₁Z(O₂(J)). Taking commutators puts U in the literal moved star module
of J. This allows the already proved B.5 action classification to control U
without assuming reconstruction of the whole component two-core.

The source consumer retains the exact first-parabolic core R₁ and the
actual generated I₀. No block or module-coordinate premise is introduced.
Source: Aschbacher--Smith 14.6.10(5), printed p.1029, and C.2.7, p.146.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
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

/-- The original 14.6.10 generated plane module lies in the moved module
classified by B.5 on the actual C.2.7 star action. -/
theorem source_parabolic_span_le_star_module
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let C := (pResidual 2 I).map I.subtype
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    let R := I1.pCoreIn 2
    conjugateSpanBy (localModule T M) I ≤
      (⁅starV C R,C.subgroupOf (C ⊔ R)⁆).map (C ⊔ R : Subgroup G).subtype := by
  dsimp only
  apply ChapterC.C27Source.residual_moved_omegaCore_le_star_module I
  · exact (pCoreIn_le 2 _).trans
      (sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right)
  · exact le_normalizer_conjugateSpanBy _ _
  · exact source_parabolic_span_le_omegaCore hG T hempty hM hunique hmany hcard e
      hab H hH u hu hindex hmove hproduct hU3 hlocal hrank I I2 hI hSI2 hI2H
      hquot2 hout hgen
  · exact (source_parabolic_global_span_moved hG T hempty hM hunique hmany hcard e
      hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1 hout).symm

/-- The literal generated I₀ has the same star-module containment, with
all construction premises discharged by the source parabolic data. -/
theorem source_generated_parabolic_span_le_star_module
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
    let R := I1.pCoreIn 2
    conjugateSpanBy (localModule T M) I0 ≤
      (⁅starV C R,C.subgroupOf (C ⊔ R)⁆).map (C ⊔ R : Subgroup G).subtype := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let L := sourceResidual M Mc
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let S := (T : Subgroup G) ⊓ I
  let I2 := (pResidual 2 H2).map H2.subtype ⊔ S
  let I0 := (R ⊔ S) ⊔ I2
  obtain ⟨hI0,hS,hgen,hI2H2,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  have hH2H : H2 ≤ H := fun x hx =>
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp (hH2kernel hx)).1
  have hSI2 : (T : Subgroup G) ⊓ I0 ≤ I2 := by
    rw [hS]
    exact le_sup_right
  have hS0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct
  have hsecond := suitable_second_parabolic_data h u hu H2 S
    (le_inf inf_le_left hI.1.2.1) hS0 hi.1 hi.2.2.2.1
    hSylH2 hH2kernel hH2quot hlocal
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hRout := (source_intersection_parabolic_data hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover).2.2.2
  have hout0 : ¬ I0 ⊓ M ≤ Mc := by
    intro hh
    apply hRout
    exact (le_inf (le_sup_left.trans le_sup_left)
      (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc))).trans hh
  exact source_parabolic_span_le_star_module hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal hrank I0 I2 hI0 hSI2
    (hI2H2.trans hH2H) hsecond.2.1 hout0 hgen

end CFSG.Quasithin.Chapter14.Section06
