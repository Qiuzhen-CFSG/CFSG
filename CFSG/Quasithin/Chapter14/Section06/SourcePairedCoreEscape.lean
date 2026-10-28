module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointRadical
public import Theory.GroupTheory.TwoLocalUniquenessControl
/-!
# The final Thompson obstruction in the paired normalizer branch

The literal point-radical theorem gives Q₁≤Rz and J(Rz)=O₂(I).
If O₂(I) lay in Q₁, Thompson heredity would give J(Q₁)=O₂(I).
Then M_c would normalize O₂(I). The original uniqueness hypothesis forces
its whole normalizer into M_c, contradicting the choice of I outside M_c.

This supplies the final contradiction in the characteristic-two D-normalizer
argument once C.1.29/A.4.4.1 yields O₂(I)≤Q₁. That earlier containment is
not assumed or asserted here; the source conclusion is its negation.
Source: Aschbacher--Smith, proof of 14.6.9, printed p.1026
(refs/quasithin.pdf).
-/

public section
namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual paired core cannot lie in Q₁=O₂(M_c). -/
theorem source_paired_core_not_le_Mc_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2) :
    ¬ I.pCoreIn 2 ≤ Mc.pCoreIn 2 := by
  intro hQ
  have hd := source_paired_point_radical hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct hU3 hlocal I hI Λ c b i j hij hs hi hpairIndex
  have hJ : elementaryAbelianMaxJ (Mc.pCoreIn 2) = I.pCoreIn 2 :=
    (elementaryAbelianMaxJ_eq_of_intermediate_finite ((I ⊓ Mc).pCoreIn 2) (Mc.pCoreIn 2)
      (hd.1.trans_le hQ) hd.2.2.1).trans hd.1
  have hMcQ : Mc ≤ normalizer (I.pCoreIn 2 : Set G) := by
    rw [←hJ]
    exact Mc.le_normalizer.trans
      ((normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)).trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ (Mc.pCoreIn 2)))
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hMc := (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ).2.2.1
  have huni : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      centralizer (centralInvolutions T : Set G) ≤ N → N = Mc := by
    intro N hN hCN
    have hm : N ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) := ⟨hN,hCN⟩
    rw [hunique] at hm
    exact Set.mem_singleton_iff.mp hm
  have hN : normalizer (I.pCoreIn 2 : Set G) ≤ Mc :=
    normalizer_le_of_unique_maximalTwoLocal huni (isPGroup_pCoreIn 2 I) hI.1.1.1 (hMc ▸ hMcQ)
  have hIQ : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  exact hI.1.1.2.2.1 (hIQ.trans hN)

end CFSG.Quasithin.Chapter14.Section06
