module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedQuotientMarking
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCoreCover
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedBorelAction
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingPairFamily
public import Theory.Representation.BinaryAlternatingFiveExtension.PairedCoreQuotient

/-!
# The actual paired four-group quotient in original 14.6.9(l)

After the residual centralizer D vanishes, the original two-core O₂(I)
is the join of the two marked block modules. The point-core cover identifies
O₂(I ∩ Mc) with the join of the two literal Borel cores. Their independent
A₄ actors and the original element of T ∩ I exchanging the blocks give an
irreducible quotient. The vector-preserving Borel markings identify its
kernel with O₂(I), so the conclusion concerns the actual source subgroups.

The actor is I ∩ Mc. The outside element of the full Sylow subgroup moves
the original core, and is not used to normalize the quotient kernel.

Source: Aschbacher--Smith, 14.6.9(l), printed p.1027.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation BinaryPermutation.AlternatingFiveExtension
variable {G : Type*} [Group G] [Finite G]

/-- Independent point stabilizers and the original factor exchanger act irreducibly
on the literal point-core quotient after D = 1. -/
theorem source_paired_core_quotient_irreducible
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
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hindex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2)
    (hD : ((T : Subgroup G) ⊓ I) ⊓ centralizer
      (((pResidual 2 I).map I.subtype) : Set G) = ⊥) :
    IsIrreducibleSection (I ⊓ Mc) (I.pCoreIn 2) ((I ⊓ Mc).pCoreIn 2) := by
  have hcover := source_paired_point_core_cover hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi hindex hD
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let B₁ := K₁ ⊓ Mc
  let B₂ := K₂ ⊓ Mc
  obtain ⟨h,h',hpoint,hpoint',hlift,hlift',hRB,t,ht,hKt⟩ :=
    source_paired_borel_action_inputs hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨e₁,he₁⟩ := source_paired_block_borel_vectors hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨e₂,he₂⟩ := source_paired_block_borel_vectors hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b j i hij.symm hs h'.block
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hdK : Disjoint K₁ K₂ := h.disjoint_blocks x (c.R_normal hx) hnc
  have hd : Disjoint B₁ B₂ := hdK.mono inf_le_left inf_le_left
  have hc : B₁ ≤ centralizer (B₂ : Set G) :=
    inf_le_left.trans ((le_centralizer_iff.mp h.commute).trans (centralizer_le inf_le_left))
  have hB₁ : B₁ ≤ I ⊓ Mc := inf_le_inf (map_subtype_le _) le_rfl
  have hB₂ : B₂ ≤ I ⊓ Mc := inf_le_inf (map_subtype_le _) le_rfl
  have hMc : Mc.map (MulAut.conj t).toMonoidHom = Mc :=
    mem_normalizer_iff_map_conj_eq.mp (Mc.le_normalizer (hRB ht).2)
  have hBt : B₁.map (MulAut.conj t).toMonoidHom = B₂ := by
    change (K₁ ⊓ Mc).map (MulAut.conj t).toMonoidHom = K₂ ⊓ Mc
    rw [map_inf _ _ _ (MulAut.conj t).injective,hKt,hMc]
  have hA : I.pCoreIn 2 = sourceModule K₁ ⊔ sourceModule K₂ := by
    obtain ⟨y,hy,hyout,hfrat,hinter,hcore,hmax,hbaum,hfamily⟩ :=
      c.alternating_pair_family b i j hij hs hi hindex
    rw [hD,sup_bot_eq] at hcore
    rw [hcore,←c.pair_join b i j hij hs]
    have ht' : ∃ t : Λ, (t : G) ∈ (T : Subgroup G) ⊓ I ∧ K₁.conjBy (t : G) = K₂ :=
      ⟨⟨t,c.R_le_M ht⟩,ht,hKt⟩
    exact h.two_block_core_eq_module h' Λ ((T : Subgroup G) ⊓ I) x hx (c.R_normal hx)
      hindex (c.pair_action b i j hij hs) ht' hnc
  have hJA : I ⊓ Mc ≤ normalizer (I.pCoreIn 2 : Set G) :=
    inf_le_left.trans (I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hJC : I ⊓ Mc ≤ normalizer ((I ⊓ Mc).pCoreIn 2 : Set G) :=
    (I ⊓ Mc).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (I ⊓ Mc) (pCore 2 (I ⊓ Mc : Subgroup G)))
  apply PairedCoreQuotient.paired_borel_core_irreducible (I ⊓ Mc) B₁ B₂
    (I.pCoreIn 2) ((I ⊓ Mc).pCoreIn 2) e₁ e₂ hd hc hB₁ hB₂
  · change I.pCoreIn 2 = PointCoreGeometry.vectors.map
      (((b.block i).map I.subtype ⊓ Mc).subtype.comp e₁.symm.toMonoidHom) ⊔
      PointCoreGeometry.vectors.map
      (((b.block j).map I.subtype ⊓ Mc).subtype.comp e₂.symm.toMonoidHom)
    rw [he₁,he₂]
    exact hA
  · exact hcover
  · exact hJA
  · exact hJC
  · exact ⟨t,hRB ht,hBt⟩

end CFSG.Quasithin.Chapter14.Section06
