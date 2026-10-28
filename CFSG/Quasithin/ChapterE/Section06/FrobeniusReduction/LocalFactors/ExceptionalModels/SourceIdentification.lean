module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.CommutationSource
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.FixedSpaces
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.BlockExclusion
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.ComponentExclusion

/-!
# Identifying and excluding the actual enlarged component in E.6.25

With trivial odd core, the enlarged C-component is ordinary or its join
with the common Sylow has characteristic two. In the latter case the exact
E.6.7 decomposition and A.3.8 Sylow-orbit theorem supply a conjugate block
factor. The conjugating element centralizes V, so it preserves the original
fixed space. The alternating block rows have corank one; the natural row's
direct decomposition gives its field exponent as the actual fixed-space
corank. In particular corank three yields a centralizer L₂(8) block.

The ordinary and block inspections then exclude both original seed types.
This discharges the whole local model sieve, retaining E.6.7, E.6.8, E.6.21
and A.3.8 as genuine earlier source inputs. C.1.9, the inner actor and all
centralizer calculations are supplied by proved theorems.

Source: Aschbacher–Smith, E.6.7 and E.6.25, printed pp.246,256;
A.3.8(3), printed p.45 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
open Hyperplanes Hyperplanes.ComponentBalance Hyperplanes.Enlargement
open Hyperplanes.Enlargement.BlockInspection
open InvariantSubspaces.BlockSelection Lifting.CharacteristicTwoBlocks
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V W J : Subgroup G}

/-- Above corank one, the actual escaping C-component is ordinary or a natural block of that corank. -/
theorem component_or_natural_of_corank_gt_one
    (h : HypothesisE61 K T M V) (ho : OddCoreFree V)
    (h67 : E67Input T M V) (h38 : SylowOrbitSource K)
    (hW : W ∈ obstructionFamily M V)
    (hJ : J ∈ Chapter1.cComponentsIn (centralizer (W : Set G)))
    (he : ¬ J ≤ M)
    (hr : 1 < subgroupCorank V (V ⊓ centralizer (J : Set G))) :
    CentralizerComponent W J ∨ (CentralizerBlock W J ∧
      ChapterC.IsL2EvenBlock J (subgroupCorank V (V ⊓ centralizer (J : Set G)))) := by
  let _ := h.elementary
  rcases Lifting.centralizer_cComponent_overgroup_dichotomy h ho hW hJ with hc | hf
  · exact Or.inl hc
  right
  obtain ⟨d,i,s,hs,hsi⟩ := Lifting.exists_factor_conjugate_of_source_blockCommutation
    h h67 h38 hW hJ he hf
  have hfixed : V ⊓ centralizer (d.block i : Set G) = V ⊓ centralizer (J : Set G) := by
    rw [hsi, ← fixedSpace_conjugate J s (Subgroup.centralizer_le_normalizer _ hs.2)]
    exact mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ (centralizer_le inf_le_left hs.2))
  have hnatural : ChapterC.IsL2EvenBlock (d.block i)
      (subgroupCorank V (V ⊓ centralizer (J : Set G))) := by
    rcases d.type i with ⟨n,hn⟩ | ha | ha
    · obtain ⟨B,_,_,_,hgen,hdis,hcard,_,_,_⟩ := d.rankOne i n hn
      have hDV : ⁅V,B⁆ ≤ V := (le_sup_right : ⁅V,B⁆ ≤
        (V ⊓ centralizer (d.block i : Set G)) ⊔ ⁅V,B⁆).trans hgen.symm.le
      have hnD : ⁅V,B⁆ ≤ normalizer (V ⊓ centralizer (d.block i : Set G) : Set G) :=
        hDV.trans (V.le_centralizer.trans
          ((centralizer_le inf_le_left).trans (Subgroup.centralizer_le_normalizer _)))
      have hcor := corank_of_direct_decomposition hgen hnD hdis hcard
      rw [hfixed] at hcor
      exact hcor.symm ▸ hn
    · have hb := (d.alternating i 3 ha).1
      rw [hfixed] at hb
      omega
    · have hb := (d.alternating i 5 ha).1
      rw [hfixed] at hb
      omega
  let e : J ≃* d.block i := ((MulAut.conj s).subgroupMap J).trans
    (MulEquiv.subgroupCongr hsi.symm)
  have hnJ := hnatural.of_mulEquiv e.symm
  exact ⟨⟨hJ.1,⟨inferInstance,hnJ.2.1.of_mulEquiv (subgroupOfEquivOfLe hJ.1).symm,
    hJ.2.subnormal⟩⟩,hnJ⟩


/-- The complete corank-three model sieve on the original enlarged C-component. -/
theorem TwoCentralEnlargement.excluded_of_earlier_sources
    {U L : Subgroup G}
    (h : HypothesisE61 K T M V) (ho : OddCoreFree V)
    (h67 : E67Input T M V) (h38 : SylowOrbitSource K)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ B : Subgroup G,
      CentralizerComponent A B →
        (∃ n, Components.BorelAlternative M V A B n) ∨
        (∃ n, Components.SymplecticAlternative M V A B n) ∨ Components.actionCorank V B ≤ 2)
    (d : TwoCentralEnlargement M V U L W J) (hUV : U ≤ V)
    (hLM : ¬ L ≤ M) (hseed : IsQuasisimple L ∨ ChapterC.IsL2EvenBlock L 2) : False := by
  rcases component_or_natural_of_corank_gt_one h ho h67 h38 d.obstruction d.component
      (fun he => hLM (d.proper.le.trans he)) (by rw [d.corank]; decide) with hc | ⟨hb,hn⟩
  · exact d.not_quasisimple_or_field_four_seed hUV (h68 W d.obstruction J hc) hseed
  · rw [d.corank] at hn
    exact d.not_block_eight h ho hUV hb hn

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
