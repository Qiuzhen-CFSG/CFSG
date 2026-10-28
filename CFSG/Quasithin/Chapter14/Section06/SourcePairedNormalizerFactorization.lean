module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointRadical
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.ResidualCentralizer
public import CFSG.Quasithin.Chapter14.Section02.ProperCompletionThreeResidual
public import Theory.GroupTheory.PResidual.HalfSylowProduct

/-!
# What the proposed paired-normalizer factorization forces

For the actual paired C.5 source configuration, normalizer control and
point-core geometry give [T:T∩N_G(D)] = 2. The proposed LT product thus
puts the two-perfect residual L inside N_G(D), and its literal intersection
residual is L itself. The original cubic generation theorem then puts L
inside O^{3′}(N_G(D)). No minimality of N_G(D) is used.

This proves the initial reduction in the printed factorization contradiction.
The subsequent moved-overcomponent centralization step of1.2.8 is separate;
this module does not claim that the proposed factorization is impossible.

Source: Aschbacher--Smith14.6.9, printed p.1026.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))

/-- The LT product and its actual index-two Sylow intersection place the
original two-perfect residual L in the proposed overgroup. -/
theorem source_residual_le_of_halfSylow_factorization
    (X : Subgroup G) (hindex : ((T : Subgroup G) ⊓ X).relIndex (T : Subgroup G) = 2)
    (hfac : let L := sourceResidual M Mc
      let LX := (pResidual 2 (L ⊓ X : Subgroup G)).map (L ⊓ X).subtype
      ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) =
        (LX : Set G) * ((T : Subgroup G) ⊓ X : Subgroup G) *
          ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) : sourceResidual M Mc ≤ X := by
  let L := sourceResidual M Mc
  have hT : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) := le_sup_right
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype hT)
  exact twoPerfect_le_of_halfSylow_product L T _ _ _ X
    (residualY_isPPerfect M Mc) hindex hQ ((map_subtype_le _).trans inf_le_right)
    inf_le_right hfac

open ChapterC ChapterC.Section05.BlockAnalysis

variable (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
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

/-- The original paired source produces the half-Sylow needed to absorb L.
The conclusion retains the literal embedded residual and cubic residual. -/
theorem source_paired_normalizer_factorization_forces_residual
    (I Λ : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2)
    (hne : ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) ≠ ⊥)
    (hfac : let D := ((T : Subgroup G) ⊓ I) ⊓
        centralizer ((pResidual 2 I).map I.subtype : Set G)
      let ID := normalizer (D : Set G)
      let L := sourceResidual M Mc
      let LD := (pResidual 2 (L ⊓ ID : Subgroup G)).map (L ⊓ ID).subtype
      ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) =
        (LD : Set G) * ((T : Subgroup G) ⊓ ID : Subgroup G) *
          ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) :
    let D := ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G)
    let ID := normalizer (D : Set G)
    let L := sourceResidual M Mc
    L ≤ ID ∧ L = (pResidual 2 (L ⊓ ID : Subgroup G)).map (L ⊓ ID).subtype ∧
      L ≤ (primeToResidual 3 ID).map ID.subtype := by
  let D := ((T : Subgroup G) ⊓ I) ⊓
    centralizer ((pResidual 2 I).map I.subtype : Set G)
  let ID := normalizer (D : Set G)
  let L := sourceResidual M Mc
  have hn : I ≤ ID := c.sylow_centralizer_normalized
  have heq := (source_lemma_14_6_9_normalizers T
    ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) M Mc I hI.1 D hne inf_le_left hn).2.1
  obtain ⟨_,_,_,hR0,_⟩ := source_paired_point_radical hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI Λ c b i j hij hs hi hpairIndex
  have hRindex : ((T : Subgroup G) ⊓ ID).relIndex (T : Subgroup G) = 2 := by
    rw [heq,hR0]
    exact hindex
  have hLI : L ≤ ID := source_residual_le_of_halfSylow_factorization T ID hRindex hfac
  refine ⟨hLI,?_,Section02.source_residual_le_three_residual hG T hempty hM hunique
    hmany hcard e ID hLI⟩
  rw [inf_eq_left.mpr hLI,(pResidual_eq_top_iff 2 L).mpr (residualY_isPPerfect M Mc),
    ←MonoidHom.range_eq_map,range_subtype]

end CFSG.Quasithin.Chapter14.Section06
