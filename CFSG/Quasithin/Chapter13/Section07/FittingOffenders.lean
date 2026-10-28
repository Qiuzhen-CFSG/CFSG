module

public import CFSG.Quasithin.Chapter13.Section07.SourceSeedPlane
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedGeneration
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Kernel
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.PlaneExclusion

/-!
# The original Fitting-offender exclusion13.7.14

Use the literal action of H/O₂(H) on U_H/U₀ and the original V₃ image.
The original13.7.12 commutator bound places all A* displacement in this
binary plane. Its L₁ action is nontrivial by V₃=[V₃,L₁] and
C_V₃(O₂(H))=V₁. The image of Q is a two-group normalized by L₁*, so the
B.1.9 plane exclusion centralizes F(H*) for every minimal offender in A*.

Faithfulness is precisely the genuine earlier13.7.4 input. All factor
normalization, rank, seed and displacement conclusions are derived here.
Source: Aschbacher–Smith13.7.14, printed p.943.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup Representation.BinaryOffender
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed.BarMarking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Original13.7.14 for the specified plus-section coordinates. The only
unproved conclusion used is the explicitly retained earlier faithfulness. -/
theorem source_minimal_offender_centralizes_fitting
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hfaith : Function.Injective σ)
    {B : Subgroup (H ⧸ pCore 2 H)} (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H))) :
    B ≤ centralizer (fittingSubgroup (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U := Section08.Source.UH H V₃
  let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
  let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
  let A := conjugate (Section08.Source.VH H V) (g : G) ⊓ Q
  let π := QuotientGroup.mk' (pCore 2 H)
  let K := (F.L₁.subgroupOf H).map π
  let R := (Q.subgroupOf H).map π
  let P := s.imageSpace V₃
  let : Finite W := Finite.of_surjective (fun x : U => (s.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have hHG : H ≤ G₁ := by
    rw [d.first_normalizer]
    exact h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hL₁H : F.L₁ ≤ H := le_sup_left.trans h.local_le
  have hL₁L : F.L₁ ≤ L := (map_subtype_le _).trans inf_le_left
  have hres : F.L₁ = sourceOne L T V₁ := by
    have hh := normalizer_residual_eq L V₁ (T : Subgroup G) T.isPGroup' d.normalizes_L
    change sourceOne L T V₁ =
      (pResidual 2 (L ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        (L ⊓ normalizer (V₁ : Set G)).subtype at hh
    have hn : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) := h.normalizer_point_eq
    rw [hn] at hh
    exact hh.symm
  have hgen : ⁅V₃,F.L₁⁆ = V₃ := by
    rw [hres]
    exact ModelExclusions.seed_commutator_point_residual d
  have hpL : IsPPerfect 2 F.L₁ := isPPerfect_embedded_pResidual 2 _
  have hpLH : IsPPerfect 2 (F.L₁.subgroupOf H) := hpL.of_surjective
    (subgroupOfEquivOfLe hL₁H).symm.toMonoidHom (subgroupOfEquivOfLe hL₁H).symm.surjective
  have hpK : IsPPerfect 2 K := hpLH.of_surjective
    (π.subgroupMap (F.L₁.subgroupOf H)) (π.subgroupMap_surjective _)
  have hpR : IsPGroup 2 R := (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype.map π
  have hNQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) := by
    simpa only [Q,pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)).le_normalizer_map
        (L ⊔ (T : Subgroup G)).subtype
  have hKR : K ≤ normalizer (R : Set (H ⧸ pCore 2 H)) := by
    apply (map_mono (show F.L₁.subgroupOf H ≤ normalizer (Q.subgroupOf H : Set H) from ?_)).trans
      ((Q.subgroupOf H).le_normalizer_map π)
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp (hNQ (mem_sup_left (hL₁L hx))) y.val
  have hseedU : V₃ ≤ U := le_conjugateSpanBy V₃ H
  have hseedN : F.L₁ ≤ normalizer (V₃ : Set G) := le_sup_left.trans h.local_normalizes
  have hP : K ≤ subspaceStabilizer σ P := by
    apply le_subspaceStabilizer
    rintro _ ⟨x,hx,rfl⟩ w hw
    obtain ⟨z,hz,rfl⟩ := (s.mem_imageSpace_iff V₃ w).mp hw
    let z' : U := ⟨(x : G) * z * (x : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized x.property) z).mp z.property⟩
    exact (s.mem_imageSpace_iff V₃ _).mpr ⟨z',
      (mem_normalizer_iff.mp (hseedN hx) z).mp hz, s.equivariant x z⟩
  have hinter : U₀ ⊓ V₃ = V₁ := by
    have he := seed_centralizer_eq_line d h (seed_noncentral_on_local_core h hHG hne)
    change V₃ ⊓ centralizer (H.pCoreIn 2 : Set G) = V₁ at he
    rw [← he]
    ext z
    exact ⟨fun hz => ⟨hz.2,hz.1.2⟩,fun hz => ⟨⟨hseedU hz.1,hz.2⟩,hz.1⟩⟩
  obtain ⟨hd,hmove⟩ := source_plus_seed_plane d h hU hV hne g hs hout σ s B hBA
  have hn : ¬ P ≤ fixedSpace σ K := by
    intro hfixed
    have hc : ⁅F.L₁,V₃⁆ ≤ U₀ := by
      apply commutator_le.mpr
      intro x hx z hz
      let xH : H := ⟨x,hL₁H hx⟩
      let zU : U := ⟨z,hseedU hz⟩
      have hv := hfixed ((s.mem_imageSpace_iff V₃ _).mpr ⟨zU,hz,rfl⟩)
        ⟨π xH,mem_map_of_mem π hx⟩
      have hzero : ((σ.comp π) xH - 1) (s.coordinates zU).toAdd = 0 := sub_eq_zero.mpr hv
      have hm := (s.displacement_mem_imageSpace_iff ⊥ bot_le xH zU).mp
        (hzero ▸ (s.imageSpace ⊥).zero_mem)
      simpa only [bot_sup_eq] using hm
    have h3 : V₃ ≤ U₀ := by rw [commutator_comm, hgen] at hc; exact hc
    exact (not_le_of_gt h.point_lt) ((le_inf h3 le_rfl).trans_eq hinter)
  have hrank : primeRank 3 (H ⧸ pCore 2 H) ≤ 2 := by
    apply (primeRank_quotient_le_of_isTwoGroup 3 (by decide)
      (pCore 2 H) pCore_isPGroup).trans
    have hlocal : IsTwoLocal G₁ := ⟨V₁,
      (fun he => by have hc := d.line_card; rw [he,Subgroup.card_bot] at hc; omega),
      IsPGroup.of_card (n := 1) (by simpa using d.line_card),d.first_normalizer⟩
    exact (primeRank_mono 3 hHG).trans
      (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp d.counterexample.qtke.quasithin
        G₁ hlocal 3 Nat.prime_three (by decide))
  exact ChapterB.FittingStructure.minimal_offender_centralizes_fitting_of_seed_plane σ
    hfaith (pCore_quotient_pCore_eq_bot (G := H) 2) hrank hpK hpR hKR P hP hd hn hB
    (hBA.trans (map_mono (comap_mono inf_le_right))) hmove

end CFSG.Quasithin.Chapter13.Section07
