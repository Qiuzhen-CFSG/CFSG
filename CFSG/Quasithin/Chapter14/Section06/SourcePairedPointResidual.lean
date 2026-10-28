module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointResidual
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointRadical

/-!
# The actual paired residual factors and Sylow normality in 14.6.9

The original central involution and the C.5 noncommuting conjugator identify
O²(I∩M_c) with the join of O²(K₁∩M_c) and O²(K₂∩M_c). Its intersections
with the original blocks are precisely these two residuals. The previously
proved R=T₀ identity and the source index-two hypotheses also identify Λ
with T and show that T normalizes R.

These are the literal residual and Sylow inputs for the subsequent paired
core and irreducible-section argument; no D=1 hypothesis is needed here.
Source: Aschbacher--Smith, proof of 14.6.9, printed pp.1026--1027
(refs/quasithin.pdf).
-/

public section
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original pair gives the source Kz decomposition and both literal intersections. -/
theorem source_paired_point_residuals
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
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let Kz := (pResidual 2 (I ⊓ Mc : Subgroup G)).map (I ⊓ Mc).subtype
    let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
    let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
    Kz = X₁ ⊔ X₂ ∧ Kz ⊓ K₁ = X₁ ∧ Kz ⊓ K₂ = X₂ := by
  let R := (T : Subgroup G) ⊓ I
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let K := (pResidual 2 I).map I.subtype
  obtain ⟨z,hz,heq,hzS,hzR,hout,h,v,hv,hcentral,hpoint⟩ :=
    source_paired_block_point_marking hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨_,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  have hjoin : K₁ ⊔ K₂ = K := c.pair_join b i j hij hs
  have hIgen : I = (K₁ ⊔ K₂) ⊔ R := by rw [hjoin,c.residual_sup_sylow]
  have hIK : I ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [hjoin]
    exact c.normalizes_residual
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hres := h.central_point_residual_pair h' x (c.R_normal hx) hnc z hzS hzR
    I c.sylow c.sylow_image hIgen hIK
  have hres₁ := h.central_point_residual_factor h' x (c.R_normal hx) hnc z hzS hzR
    I c.sylow c.sylow_image hIgen hIK
  obtain ⟨y,hy,hcomm'⟩ := c.exists_noncommuting_module b j
  have hnc' : ¬ (sourceModule K₂).map (MulAut.conj y⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₂ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm'
    exact fun hh => hcomm' (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hIgen' : I = (K₂ ⊔ K₁) ⊔ R := by rw [sup_comm K₂ K₁]; exact hIgen
  have hIK' : I ≤ normalizer ((K₂ ⊔ K₁ : Subgroup G) : Set G) := by rw [sup_comm K₂ K₁]; exact hIK
  have hres₂ := h'.central_point_residual_factor h y (c.R_normal hy) hnc' z hzS hzR
    I c.sylow c.sylow_image hIgen' hIK'
  rw [heq] at hres hres₁ hres₂
  exact ⟨hres,hres₁,hres₂⟩

/-- Suitability forces Λ=T and the normality of the actual R in T. -/
theorem source_paired_point_sylow_configuration
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
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2) (hΛT : Λ ≤ (T : Subgroup G)) :
    Λ = (T : Subgroup G) ∧ (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ I) : Set G) := by
  have hr := source_paired_point_radical hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct hU3 hlocal I hI Λ c b i j hij hs hi hpairIndex
  have he := hr.2.2.2.1
  have hRT : (((T : Subgroup G) ⊓ I).relIndex (T : Subgroup G)) = 2 := by
    rw [he]
    exact hindex
  have hm := relIndex_mul_relIndex ((T : Subgroup G) ⊓ I) Λ (T : Subgroup G) c.R_le_M hΛT
  rw [hpairIndex,hRT] at hm
  have hΛ : Λ.relIndex (T : Subgroup G) = 1 := by omega
  exact ⟨le_antisymm hΛT (relIndex_eq_one.mp hΛ),
    (normal_subgroupOf_iff_le_normalizer (show (T : Subgroup G) ⊓ I ≤ (T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hRT)⟩

end CFSG.Quasithin.Chapter14.Section06
