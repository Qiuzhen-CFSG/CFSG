module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.NoncontainedSL2Four
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.BlockLayer
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The original A₆ block chief-count obstruction

An A₆ block has its full commutator layer equal to the original natural
module V. The intrinsic subnormal-core commutator bound therefore places
[O₂(LT),L] inside V. An actual cubic subgroup of L₁ fixes its original line
V₁. Since |V|=16 and |V₁|=2, its cubic fixed length on O₂(LT) is at most one.
The literal A₄ quotient of L₁ contributes one additional noncentral binary
chief factor, bounding every complete L₁ series by two.

The already proved original two-conjugate count is at least three. Thus
L is not an A₆ block under the original nonabelian V-span hypotheses. No
chief-count bound, whole-core reconstruction or module-classification premise
is added.

Source: Aschbacher--Smith, 13.7.4(1), 13.7.10(8), and 13.7.19,
printed pp.937,942,945.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion Section05.PlaneGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_block_core_commutator_le_module
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hb : ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ ≤ V := by
  let X := L ⊔ (T : Subgroup G)
  let LX := L.subgroupOf X
  have hc := commutator_le_core_commutator_of_isSubnormal LX (pCore 2 X)
    d.counterexample.local_component.1.1.subnormal hb.2.1.twoPerfect
    pCore_isPGroup le_normalizer_of_normal
  have he := block_layer_eq_module d hb
  let e : LX ≃* L := subgroupOfEquivOfLe le_sup_left
  have hu : ((ChapterC.blockU LX).map LX.subtype).map X.subtype = V := by
    rw [map_map]
    change (ChapterC.blockU LX).map (L.subtype.comp e.toMonoidHom) = V
    rw [←map_map,ChapterC.RankOne.Solvable.blockU_map_equiv e,he]
  have hh := map_mono (f := X.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le (show L ≤ X from le_sup_left)] at hh
  exact hh.trans hu.le

theorem source_block_cubic_length_le_one
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hb : ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hAL : A ≤ L) (hAV₁ : A ≤ centralizer (V₁ : Set G)) :
    conjugationCubicLength A ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 1 := by
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  let := local_module_normal d
  let := local_module_elementary d
  have hVX : V ≤ X := d.chosen.le_sylow.trans le_sup_right
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 X).map X.subtype
    have hc : V.subgroupOf X ≤ pCore 2 X :=
      le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 (V.subgroupOf X)⟩
    simpa only [map_subgroupOf_eq_of_le hVX] using map_mono (f := X.subtype) hc
  have hXQ : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hAX : A ≤ X := hAL.trans le_sup_left
  let : (V.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 X).trans d.normalizes_V)
  have he := CubicComparison.length_eq_of_commutator_le A Q V
    (IsPGroup.of_card (n := 1) (by simpa using hA)) (isPGroup_pCoreIn 2 X)
    hVQ (hAX.trans hXQ) (hAX.trans d.normalizes_V)
    ((commutator_mono le_rfl hAL).trans (source_block_core_commutator_le_module d hb))
  rw [←he]
  have hline : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hi : (centralizer (A : Set G)).relIndex V ≤ 8 := by
    let C := (centralizer (A : Set G)).subgroupOf V
    have hVC : V₁.subgroupOf V ≤ C := comap_mono (le_centralizer_iff.mp hAV₁)
    have hcardC : 2 ≤ Nat.card C := by
      have hm := Nat.card_le_card_of_injective (inclusion hVC) (inclusion_injective hVC)
      rw [Nat.card_congr (subgroupOfEquivOfLe hline).toEquiv,d.line_card] at hm
      exact hm
    have hcardV : Nat.card V = 16 := by
      rw [Nat.card_congr d.coordinate.toEquiv]
      change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
        BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
      decide
    have hm := C.card_mul_index
    rw [hcardV] at hm
    change C.index ≤ 8
    nlinarith
  exact (Nat.log_mono_right (b := 4) hi).trans_eq (by decide)

theorem source_block_L1_chief_count_le_two
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hb : ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6)
    (s : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁)
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.noncentralTwoCount ≤ 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨f,hf,hker⟩ := source_local_residual_surjection d h hU hV
  have hd : 3 ∣ Nat.card F.L₁ := by
    apply dvd_trans (b := Nat.card (alternatingGroup (Fin 4)))
    · rw [nat_card_alternatingGroup]
      norm_num
    · exact card_dvd_of_surjective f hf
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := F.L₁) 3 hd
  let A := zpowers (x : G)
  have hA : Nat.card A = 3 := by
    rw [Nat.card_zpowers,F.L₁.orderOf_coe x,hx]
  have hAJ : A ≤ F.L₁ := zpowers_le.mpr x.property
  have hAL : A ≤ L := hAJ.trans ((map_subtype_le _).trans inf_le_left)
  have hAV₁ : A ≤ centralizer (V₁ : Set G) :=
    hAJ.trans ((le_sup_left.trans h.local_le).trans h.H_centralizes)
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype
  have hAi : Nat.card (A.subgroupOf F.L₁) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA
  have hc := CubicComparison.alternatingFour_count f hf hp (A.subgroupOf F.L₁) hAi s h0 h1
  have hl : conjugationCubicLength (A.subgroupOf F.L₁) f.ker ≤ 1 := by
    rw [hker]
    have he := CubicComparison.length_subgroupOf A (Q ⊓ F.L₁) F.L₁ hAJ inf_le_right
    rw [inf_subgroupOf_right] at he
    rw [he]
    exact (conjugationCubicLength_mono A inf_le_left).trans
      (source_block_cubic_length_le_one d hb A hA hAL hAV₁)
  omega

theorem source_not_alternatingBlock
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ¬ ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6 := by
  exact source_not_alternatingBlock_of_chief_bound d h hU hV
    (source_block_L1_chief_count_le_two d h hU hV)

end CFSG.Quasithin.Chapter13.Section07
