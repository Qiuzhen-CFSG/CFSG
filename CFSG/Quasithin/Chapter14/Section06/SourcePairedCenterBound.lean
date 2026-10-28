module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedBorelAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.CenterBound

/-!
# The literal paired center bound in original 14.6.9(k)

The source point markings identify Uᵢ ∩ Rᵢ and Z(Rᵢ) with the Borel
three-spaces and fixed lines. The marked center theorem then proves
Z(Tᵢ/Z₀) ≤ E₀/Z₀ as a literal preimage containment. The original
noncommuting conjugators supply both module-centralizer decompositions.
The sole additional mathematical hypothesis is D = C_(T∩I)(O²(I)) = 1.

Source: Aschbacher--Smith, 14.6.9(k), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation BinaryPermutation.AlternatingFiveFlag
variable {G : Type*} [Group G] [Finite G]

/-- The actual source quotient has center preimage in E₀. Normality of the
literal denominator is supplied together with the bound. -/
theorem source_paired_quotient_center_bound
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
    (hD : ((T : Subgroup G) ⊓ I) ⊓
      centralizer (((pResidual 2 I).map I.subtype : Subgroup G) : Set G) = ⊥) :
    let R := (T : Subgroup G) ⊓ I
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
    let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
    let E₀ := (K₁.pCoreIn 2 ⊓ X₁.pCoreIn 2) ⊔ (K₂.pCoreIn 2 ⊓ X₂.pCoreIn 2)
    let Z₀ := (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
      (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype
    ∃ hZ : (Z₀.subgroupOf R).Normal,
      letI := hZ
      ((center (R ⧸ Z₀.subgroupOf R)).comap
        (QuotientGroup.mk' (Z₀.subgroupOf R))).map R.subtype ≤ E₀ := by
  let R := (T : Subgroup G) ⊓ I
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
  let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
  let E₀ := (K₁.pCoreIn 2 ⊓ X₁.pCoreIn 2) ⊔ (K₂.pCoreIn 2 ⊓ X₂.pCoreIn 2)
  let Z₀ := (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
    (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype
  obtain ⟨h,h',_,_,hE₁,hE₂,hZ₁,hZ₂,_,_,_⟩ := source_paired_borel_flags
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  obtain ⟨y,hy,hcomm'⟩ := c.exists_noncommuting_module b j
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hnc' : ¬ (sourceModule K₂).map (MulAut.conj y⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₂ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm'
    exact fun hh => hcomm' (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  obtain ⟨hU₁,hU₂⟩ := source_paired_cores_eq_modules c b i j hij hs hi
  have hE : E₀ = three.map h.borelMap ⊔ three.map h'.borelMap := by
    change (K₁.pCoreIn 2 ⊓ X₁.pCoreIn 2) ⊔ (K₂.pCoreIn 2 ⊓ X₂.pCoreIn 2) = _
    rw [hU₁,hU₂,hE₁,hE₂]
  have hZ : Z₀ = line.map h.borelMap ⊔ line.map h'.borelMap := congrArg₂ (· ⊔ ·) hZ₁ hZ₂
  have hZR : Z₀ ≤ R := by
    rw [hZ]
    apply sup_le
    · rintro _ ⟨v,_,rfl⟩
      exact (h.module_le.trans inf_le_left) (h.coordinates.symm v).property
    · rintro _ ⟨v,_,rfl⟩
      exact (h'.module_le.trans inf_le_left) (h'.coordinates.symm v).property
  obtain ⟨_,_,_,_,_,_,hR,_⟩ := source_paired_borel_action_inputs
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hnZ : (Z₀.subgroupOf R).Normal := (normal_subgroupOf_iff_le_normalizer hZR).mpr
    (hR.trans (source_paired_center_normalized c b i j hij hs Mc))
  refine ⟨hnZ,?_⟩
  let := hnZ
  have hD' : R ⊓ centralizer (K₁ ⊔ K₂ : Subgroup G) = ⊥ := by
    rw [show K₁ ⊔ K₂ = (pResidual 2 I).map I.subtype from c.pair_join b i j hij hs]
    exact hD
  change ((center (R ⧸ Z₀.subgroupOf R)).comap
    (QuotientGroup.mk' (Z₀.subgroupOf R))).map R.subtype ≤ E₀
  rintro _ ⟨g,hg,rfl⟩
  rw [hE]
  apply h.mem_borel_six_of_line_commutators h' x y
    (c.R_normal hx) (c.R_normal hy) hnc hnc' hD' g g.property
  intro r hr
  rw [←hZ]
  change ⁅g,(⟨r,hr⟩ : R)⁆ ∈ Z₀.subgroupOf R
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' _ ⁅g,(⟨r,hr⟩ : R)⁆ = 1
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact (mem_center_iff.mp hg _).symm

end CFSG.Quasithin.Chapter14.Section06
