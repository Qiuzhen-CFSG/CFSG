module
public import CFSG.Quasithin.Chapter14.Section06.SourceNoncharacteristicFactorization
public import CFSG.Quasithin.Chapter14.Section06.SourceInvariantSubgroups

/-!
# Reducing the original factorizations to characteristic-two minimal choices

An inclusion-minimal outside subgroup inside a maximal-intersection choice
has the same Sylow intersection. Monotonicity of the embedded two-residual
therefore lifts both literal products from that minimal subgroup to the
original overgroup. The non-characteristic-two minimal branch is discharged
by the proved component classification and rank contradiction.

The only remaining source input is the factorization for characteristic-two
minimal choices. The invariant-subgroup dichotomy of 14.6.10(3) and its
normal-complement exclusion now consume that same restricted input.

Source: Aschbacher--Smith 14.6.5--6, 14.6.9 and 14.6.10(3),(5),
printed pp.1022--1029. The characteristic-two input is the remaining
original C.5 block argument in 14.6.9, printed pp.1025--1027.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Enlarging the outside subgroup preserves both residual products when
its Sylow intersection is unchanged. -/
theorem residual_factorizations_lift (L T J I : Subgroup G) (hJI : J ≤ I)
    (hmeet : T ⊓ J = T ⊓ I)
    (hf :
      (L : Set G) =
        ((pResidual 2 (L ⊓ J : Subgroup G)).map (L ⊓ J).subtype : Set G) *
          (L.pCoreIn 2 : Set G) ∧
      (L ⊔ T : Subgroup G) =
        ((pResidual 2 (L ⊓ J : Subgroup G)).map (L ⊓ J).subtype : Set G) *
          (T ⊓ J : Subgroup G) * ((L ⊔ T).pCoreIn 2 : Set G)) :
    (L : Set G) =
      ((pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype : Set G) *
        (L.pCoreIn 2 : Set G) ∧
    (L ⊔ T : Subgroup G) =
      ((pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype : Set G) *
        (T ⊓ I : Subgroup G) * ((L ⊔ T).pCoreIn 2 : Set G) := by
  have hR := embedded_pResidual_mono 2 (inf_le_inf_left L hJI)
  constructor
  · apply Set.Subset.antisymm
    · rw [hf.1]
      exact Set.mul_subset_mul hR (Set.Subset.refl _)
    · rintro x ⟨r,hr,q,hq,rfl⟩
      exact L.mul_mem (((map_subtype_le _).trans inf_le_left) hr) (pCoreIn_le _ _ hq)
  · apply Set.Subset.antisymm
    · rw [hf.2,hmeet]
      exact Set.mul_subset_mul
        (Set.mul_subset_mul hR (Set.Subset.refl _)) (Set.Subset.refl _)
    · rintro x ⟨rs,⟨r,hr,s,hs,rfl⟩,q,hq,rfl⟩
      exact (L ⊔ T).mul_mem
        ((L ⊔ T).mul_mem
          (mem_sup_left (((map_subtype_le _).trans inf_le_left) hr))
          (mem_sup_right hs.1)) (pCoreIn_le _ _ hq)
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
variable
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (hchar2 : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G) → ∀ J : Subgroup G,
      J ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) →
      generalizedFitting J = pCore 2 J →
      (let L := sourceResidual M Mc
       let R := (pResidual 2 (L ⊓ J : Subgroup G)).map (L ⊓ J).subtype
       (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
         (L ⊔ (T : Subgroup G) : Subgroup G) =
           (R : Set G) * ((T : Subgroup G) ⊓ J : Subgroup G) *
             ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)))

include hcoreIndex hrank hchar2

/-- Both original 14.6.9 products for every maximal-intersection outside
choice, with only the characteristic-two minimal branch remaining. -/
theorem source_factorizations_of_characteristic_minimal
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  let : Finite (Subgroup G) :=
    Finite.of_injective (fun A : Subgroup G => (A : Set G)) SetLike.coe_injective
  obtain ⟨J,hJI,hJ,hmeet⟩ := exists_iMin_le_same_intersection (Set.toFinite _) hI
  apply residual_factorizations_lift (sourceResidual M Mc) (T : Subgroup G) J I hJI hmeet
  by_cases hF : generalizedFitting J = pCore 2 J
  · exact hchar2 hcoreIndex J hJ hF
  · exact source_noncharacteristic_factorization hG T hempty hM hunique hmany hcard e hab
      H hH u hu hindex hmove hproduct hU3 hlocal hrank J hF hJ

/-- Original 14.6.10(3), with the full outside factorization premise replaced
by its characteristic-two inclusion-minimal source branch. -/
theorem source_lemma_14_6_10_3_of_characteristic_minimal
    (I P : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hPI : P ≤ I)
    (hN : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I) ≤
        normalizer (P : Set G)) :
    (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ P ∨
        P ≤ M ⊓ centralizer (localModule T M : Set G) := by
  apply source_lemma_14_6_10_3_of_factorizations hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I P hI _ hPI hN
  intro J _ hJ
  exact (source_factorizations_of_characteristic_minimal hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank hchar2 J hJ).1

/-- The original normal-complement contradiction, using only the remaining
characteristic-two minimal factorization source. -/
theorem source_normal_complement_exclusion_of_characteristic_minimal
    (I P : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hPI : P ≤ I) (hN : I ≤ normalizer (P : Set G))
    (hgen : P ⊔ ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) = I)
    (hmeet : P ⊓ sourceResidual M Mc ≤ (sourceResidual M Mc).pCoreIn 2) : False := by
  apply source_normal_complement_exclusion_of_factorizations hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I P hI _ hPI hN hgen hmeet
  intro J _ hJ
  exact (source_factorizations_of_characteristic_minimal hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank hchar2 J hJ).1

end CFSG.Quasithin.Chapter14.Section06
