module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingNormalizerSource
public import CFSG.Quasithin.ChapterC.Section06.AlternatingKernel
/-!
# The faithful four-family action on the selected A₅ shadow

The original source constructs the marked A₅ setup. The core normalizer
barrier of 2.4.4 then identifies the pointwise kernel of the actual Sylow
action on the four maximum elementary subgroups with J(S), and [S:J(S)]=2.
No permutation representation or kernel identity is a consumer hypothesis.

Source: Aschbacher--Smith 2.4.5(3), C.6.1 case (beta), pp.528,165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_family_action
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (htype : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    (elementaryAbelianMaxJ S).relIndex S = 2 ∧
      (∀ A ∈ elementaryAbelianMaxSubgroups S,
        elementaryAbelianMaxJ S ≤ normalizer (A : Set G)) ∧
      ∀ g ∈ (T : Subgroup G),
        (∀ A ∈ elementaryAbelianMaxSubgroups S, g ∈ normalizer (A : Set G)) ↔
          g ∈ elementaryAbelianMaxJ S := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,h,x,hx,hnc⟩ := d.single_alternating_configuration hG T hST.le hsingle htype
    M₀ hSM hMT hi
  have ha := ChapterC.Section06.alternating_action_from_original c h hi x hx hnc
  refine ⟨ha.1,ha.2.1,?_⟩
  have hQ : twoCore d.H ≠ ⊥ := by
    intro he
    have hf := ChapterC.Section06.alternating_family_from_original c h hi x hx hnc
    have hu := le_sup_left.trans_eq (h.product.symm.trans hf.1)
    exact moduleLayer_ne_bot htype.2.1 (bot_unique (he ▸ hu))
  have hQR : twoCore d.H ≤ (d.S : Subgroup d.H).map d.H.subtype := pCoreIn_le_sylow d.H d.S
  have hnormal : (twoCore d.H).subgroupOf d.H |>.Normal :=
    (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 d.H)).mpr
      (d.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.H (pCore 2 d.H)))
  have hc := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
    (twoCore d.H) hQ hQR hnormal
  exact ChapterC.Section06.alternating_family_kernel_from_original c h T hc hi x hx hnc

end CFSG.Quasithin.Chapter2
