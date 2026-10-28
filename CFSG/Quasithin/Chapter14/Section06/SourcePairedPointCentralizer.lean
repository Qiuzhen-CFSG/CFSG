module
public import CFSG.Quasithin.Chapter14.Section06.SourceCharacteristicTwoBlocks
public import CFSG.Quasithin.Chapter14.Section06.SourceIntersection
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointCentralizer
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection

/-!
# The original paired-A₅ point-centralizer models in 14.6.9

The original 14.6.7 involution gives C_G(z)=Mc. Transitivity of the
literal C.5 block orbit proves that each selected block escapes Mc;
its marked fixed vector identifies Kᵢ ∩ Mc with the natural binary
A₄ extension. The original noncommuting conjugator supplies the
whole-kernel hypothesis. Consequently the actual two-core of the
two-residual of Kᵢ ∩ Mc is Q₈ * Q₈, with order 32 and center order 2.

These declarations consume the configuration constructed by
`source_characteristicTwo_natural_or_paired_or_factorization`.
The later identification with the factors of O²(I ∩ Mc), the Thompson
subgroup comparison, and D=1 remain separate source steps.

Source: Aschbacher--Smith, proof of 14.6.9, printed pp.1025--1026
(refs/quasithin.pdf).
-/

public section
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open Subgroup Theory.GroupTheory
variable {A : Type*} [Group A] [Finite A]
private theorem orbit_block_not_le
    (S : Sylow 2 A) (R : Subgroup A)
    (b : OrbitDecomposition (S : Subgroup A) R (pResidual 2 A))
    (N : Subgroup A) (hSN : (S : Subgroup A) ≤ N) (hN : N ≠ ⊤)
    (i : Fin b.size) : ¬ b.block i ≤ N := by
  intro hi
  have hall (j : Fin b.size) : b.block j ≤ N := by
    obtain ⟨s,hs,he⟩ := b.transitive i j
    rw [he]
    rintro x ⟨y,hy,rfl⟩
    change s⁻¹*y*(s⁻¹)⁻¹ ∈ N
    exact N.mul_mem (N.mul_mem (N.inv_mem (hSN hs)) (hi hy))
      (N.inv_mem (N.inv_mem (hSN hs)))
  have hr : pResidual 2 A ≤ N := b.generate ▸ iSup_le hall
  exact hN (top_unique ((pResidual_sup_sylow_eq_top S) ▸ sup_le hr hSN))
end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis

namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_paired_block_point_marking
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
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    ∃ z ∈ centralInvolutions T, centralizer ({z} : Set G) = Mc ∧
      z ∈ ChapterB.baumann ((T : Subgroup G) ⊓ I) ∧
      z ∈ centralizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) ∧
      ¬ (b.block i).map I.subtype ≤ Mc ∧
      ∃ h : AlternatingPairSetup ((T : Subgroup G) ⊓ I)
        ((b.block i).map I.subtype) ((b.block j).map I.subtype),
      ∃ v : sourceModule ((b.block i).map I.subtype),
        h.coordinates v = Multiplicative.ofAdd BinaryPermutation.AlternatingFiveBorel.fixedVector ∧
        (b.block i).map I.subtype ⊓ Mc =
          (b.block i).map I.subtype ⊓ centralizer ({(v : G)} : Set G) ∧
        ∀ k : (b.block i).map I.subtype, (k : G) ∈ Mc ↔
          h.action (inclusion le_sup_left k) 4 = 4 := by
  obtain ⟨⟨z,hz,h115⟩,_,_⟩ := source_lemma_14_6_7_initial hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI.1.1 c.sylow c.sylow_image
  let R := (T : Subgroup G) ⊓ I
  have hzR : z ∈ R := by
    change z ∈ (T : Subgroup G) ⊓ I
    rw [←c.sylow_image]
    exact h115.mem_sylow
  have hzC : z ∈ centralizer (R : Set G) := by
    intro r hr
    exact h115.central r (c.sylow_image.symm ▸ hr)
  have hzomega : z ∈ omegaOneCenterAmbient R :=
    (mem_omegaOneCenterAmbient_iff R z).mpr
      ⟨hzR,by rw [←h115.involution]; exact pow_orderOf_eq_one z,hzC⟩
  have hzJ := (mem_omegaOneCenterAmbient_iff _ z).mp
    (omegaCenter_le_omegaCenter_maxJ R hzomega)
  have hzS : z ∈ ChapterB.baumann R := ChapterB.elementaryAbelianMaxJ_le_baumann R hzJ.1
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hMc := (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ).2.2.1
  have heq : centralizer ({z} : Set G) = Mc := by
    apply le_antisymm h115.centralizer_le
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (((hMc ▸ hx) z hz).symm)
  have hSMc : (c.sylow : Subgroup I) ≤ Mc.subgroupOf I := by
    intro s hs
    exact h115.mem_HeOver.2.2 (mem_map_of_mem I.subtype hs)
  have hN : Mc.subgroupOf I ≠ ⊤ := fun he => hI.1.1.2.2.1 (subgroupOf_eq_top.mp he)
  have hout : ¬ (b.block i).map I.subtype ≤ Mc := by
    intro hk
    apply orbit_block_not_le c.sylow _ b (Mc.subgroupOf I) hSMc hN i
    exact fun a ha => hk (mem_map_of_mem I.subtype ha)
  obtain ⟨⟨h⟩,_⟩ := c.alternating_paired_setups b i j hij hs hi
  obtain ⟨v,hv,hcentral,hpoint⟩ := h.central_point_marking z hzS hzC (heq.symm ▸ hout)
  refine ⟨z,hz,heq,hzS,hzC,hout,h,v,hv,?_,?_⟩
  · simpa only [heq] using hcentral
  · simpa only [heq] using hpoint

end CFSG.Quasithin.Chapter14.Section06

namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_paired_block_borel
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
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    Nonempty (((b.block i).map I.subtype ⊓ Mc : Subgroup G) ≃*
      BinaryPermutation.AlternatingFiveExtension.BorelModel) := by
  obtain ⟨z,hz,heq,hzS,hzC,hout,h,v,hv,hcentral,hpoint⟩ := source_paired_block_point_marking
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule ((b.block i).map I.subtype)).map
      (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((b.block i).map I.subtype) : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hb := h.central_point_borel x (c.R_normal hx) hnc z hzS hzC (heq.symm ▸ hout)
  obtain ⟨eb⟩ := hb
  exact ⟨(MulEquiv.subgroupCongr (congrArg
    (fun C : Subgroup G => (b.block i).map I.subtype ⊓ C) heq.symm)).trans eb⟩
end CFSG.Quasithin.Chapter14.Section06

namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation.AlternatingFiveExtension
variable {G : Type*} [Group G] [Finite G]

theorem source_paired_block_borel_core
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
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    let B := (b.block i).map I.subtype ⊓ Mc
    let X := (pResidual 2 B).map B.subtype
    Nonempty (QuaternionCentralProductData (X.pCoreIn 2)) ∧
      Nat.card (X.pCoreIn 2) = 32 ∧ Nat.card (center (X.pCoreIn 2)) = 2 := by
  let B := (b.block i).map I.subtype ⊓ Mc
  let X := (pResidual 2 B).map B.subtype
  obtain ⟨eb⟩ := source_paired_block_borel hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi
  let er := (eb.subgroupMap (pResidual 2 B)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 eb.toMonoidHom eb.surjective))
  let ep := ((er.subgroupMap (pCore 2 (pResidual 2 B))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 er))).trans borel_core_equiv
  let ex := (pResidual 2 B).equivMapOfInjective B.subtype B.subtype_injective
  let exP := (ex.subgroupMap (pCore 2 (pResidual 2 B))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 ex))
  let ea := exP.trans ((pCore 2 X).equivMapOfInjective X.subtype X.subtype_injective)
  let em := ea.symm.trans ep
  exact ⟨⟨coreModelQuaternionData.map em.symm⟩,
    (Nat.card_congr em.toEquiv).trans card_coreModel,
    (Nat.card_congr (centerCongr em).toEquiv).trans card_center_coreModel⟩
end CFSG.Quasithin.Chapter14.Section06
