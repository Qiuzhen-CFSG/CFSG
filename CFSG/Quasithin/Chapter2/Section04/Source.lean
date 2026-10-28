module
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.Chapter2.Section04.BlockNormality.SourceRecognition
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicOrbit
/-!
# Source block normality and the cubic residual

The complete Theorems A, C and C.1.29 discharge the remaining earlier inputs
of the nonsolvable selected-block normality theorem. For the cubic branch,
the actual Sylow orbit identifies L₀ with A₄ or A₄×A₄. Its trivial center
and the proved core formula give the literal direct product Q=U₀×C_S(L₀).

These results retain the selected subgroup, its actual residual and module,
and the full known-simple catalogue. The cubic core-normalizer assertion
and the later shadow classification still require their source arguments.

Source: Aschbacher--Smith, §2.4, printed pp.528 and 543--550,
using C.1.9, C.1.28--29 and 2.4.5 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original 2.4.6 normality assertion for every nonsolvable selected
block, with A, C and C.1.29 supplied by their complete source proofs. -/
theorem MinimalBlockSetup.coreNormalizer_normalizes_L0_source_of_not_three
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (h3 : ¬ ChapterC.IsAlternatingBlock d.block 3) :
    normalizer (twoCore d.H : Set G) ≤ normalizer (d.L0.map d.H.subtype : Set G) :=
  d.coreNormalizer_normalizes_L0_of_not_three hG
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    localC129Input_knownSimple T hM hTM hunique h3

/-- In the A₃ source branch, the actual residual is A₄ or A₄×A₄. -/
theorem MinimalBlockSetup.cubic_residual_models
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h3 : ChapterC.IsAlternatingBlock d.block 3) :
    Nonempty (d.L0 ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (d.L0 ≃* AlternatingFourPair.Model) := by
  have hf := generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp d.mem_gammaEvenZero.2)
  have hr : primeRank 3 d.H ≤ 2 := (d.local_sqtk hG).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hm := ChapterC.RankOne.ChiProduct.cubic_orbit_models hf hr d.S d.block d.block_type.1 h3
  have he : conjugateSpanBy d.block (d.S : Subgroup d.H) = d.L0 := by
    rw [conjugateSpanBy_eq_iSup_conj]
    rfl
  rcases hm.2 with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨(MulEquiv.subgroupCongr he.symm).trans e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨(MulEquiv.subgroupCongr he.symm).trans e⟩

private theorem center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hc : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro x hx
  have h := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center B at h
  rw [hc,mem_bot] at h
  exact mem_bot.mpr (e.injective (h.trans e.map_one.symm))

/-- The cubic source residual has no central factor. -/
theorem MinimalBlockSetup.cubic_residual_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h3 : ChapterC.IsAlternatingBlock d.block 3) : center d.L0 = ⊥ := by
  rcases d.cubic_residual_models hG h3 with h | h
  · obtain ⟨e⟩ := h
    exact center_eq_bot_of_equiv e (alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4)))
  · obtain ⟨e⟩ := h
    exact center_eq_bot_of_equiv e AlternatingFourPair.center_eq_bot

/-- The actual A₃ source core is the direct product U₀×C_S(L₀).
This retains the original subgroup factors used by the cubic shadows. -/
theorem MinimalBlockSetup.cubic_core_product
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (h3 : ChapterC.IsAlternatingBlock d.block 3) :
    let D := (d.S : Subgroup d.H).map d.H.subtype ⊓
      centralizer (d.L0.map d.H.subtype : Set G)
    Nonempty (twoCore d.H ≃* (d.U0.map d.H.subtype × D)) := by
  let U := d.U0.map d.H.subtype
  let D := (d.S : Subgroup d.H).map d.H.subtype ⊓
    centralizer (d.L0.map d.H.subtype : Set G)
  have hUL : U ≤ d.L0.map d.H.subtype := map_mono d.U0_le_L0
  have hc : U ≤ centralizer (D : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le hUL))
  have hd : Disjoint U D := by
    apply disjoint_def.mpr
    intro x hxU hxD
    obtain ⟨y,hy,rfl⟩ := hUL hxU
    have hyc : (⟨y,hy⟩ : d.L0) ∈ center d.L0 := by
      apply mem_center_iff.mpr
      intro z
      apply Subtype.ext
      apply Subtype.ext
      exact hxD.2 z (mem_map_of_mem d.H.subtype z.property)
    rw [d.cubic_residual_center hG h3,mem_bot] at hyc
    exact congrArg (fun y : d.L0 => ((y : d.H) : G)) hyc
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting U D hd hc
  have he : twoCore d.H = U ⊔ D := (d.core_source hG T hST).2.1
  exact ⟨(MulEquiv.subgroupCongr he).trans e.symm⟩
end CFSG.Quasithin.Chapter2
