module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.Structure
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.OddRadical
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import Theory.GroupTheory.CComponent.TwoClosedKernel
public import Theory.GroupTheory.SolvableRadical.TwoCoreOddQuotient

/-!
# Quasisimplicity of the original component quotient

The prime-to-three kernel has a normal Sylow two-subgroup by F.6.11.
The radical Sylow argument therefore makes the radical of K/O₂(K) odd.
The genuine A.3.6 conclusion supplied by the known-simple A/C theorems
excludes its noncentral radical branch, giving quasisimplicity of this
literal quotient of the original normal C-component.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029, using 1.2.1(4).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterF SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

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


/-- The selected original normal component has a quasisimple two-core quotient. -/
theorem source_parabolic_component_twoCore_quasisimple
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I)
    (K : Subgroup I) (hK : K.IsCComponent) [K.Normal]
    (himage : IsComponent (I ⧸ pPrimeCore 3 I)
      (K.map (QuotientGroup.mk' (pPrimeCore 3 I)))) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  have ht := source_parabolic_goldschmidtTriple_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hout hgen
  obtain ⟨S,hS⟩ := ht.primeToThreeCore_sylow
  have hSn : (S : Subgroup (pPrimeCore 3 I)).Normal := by
    have he : (S : Subgroup (pPrimeCore 3 I)) = (pCore 2 I).subgroupOf (pPrimeCore 3 I) := by
      apply map_injective (pPrimeCore 3 I).subtype_injective
      rw [hS,map_subgroupOf_eq_of_le twoCore_le_primeToThreeCore]
    rw [he]
    infer_instance
  have ho : Odd (Nat.card (solvableRadical (K ⧸ pCore 2 K))) := by
    apply odd_radical_twoCore_quotient_iff.mpr
    exact odd_radical_relIndex_of_component_quotient (pPrimeCore 3 I) K
      ⟨S,hSn⟩ ht.primeToThreeCore_quotient_twoCore_eq_bot himage
  have hsq : IsSQTK KnownSimple.IsKnownSimple I := by
    let N := normalizer (I.pCoreIn 2 : Set G)
    have hIN : I ≤ N := I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
    have hN : IsTwoLocal N := ⟨I.pCoreIn 2,hI.1.1,isPGroup_pCoreIn 2 I,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
      ((hG.twoLocal_sqtk hN).subgroup (I.subgroupOf N))
  exact Chapter1.Section02.quasisimple_twoCore_quotient_of_a36_of_odd_radical
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hsq hK ho

end CFSG.Quasithin.Chapter14.Section06
