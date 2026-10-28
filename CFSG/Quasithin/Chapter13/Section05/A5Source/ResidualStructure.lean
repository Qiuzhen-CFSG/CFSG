module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BlockApplication
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.StarQuotient
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.CoreCollapse.CubicImage

/-!
# The original A₅ residual and its two-core

The constructed G.2.4 marking identifies the original residual image
with an A₄ Borel and its two-core with the marked four-group. Its
cubic quotient is therefore obtained before any component selection.
Counting the kernel of the actual map L₁→LT/O₂(LT) also gives
|O₂(L₁)|≤4|O₂(L)|, the upper bound used in13.5.23. When L₁ is normal
in H, its actual H/O₂(H) image is cyclic of order three.
Source: Aschbacher–Smith13.5.14(2),13.5.15(1),13.5.23, pp.919–925.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterG.Section02.AlternatingFive
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
include d hA312 hH hU

/-- The exact residual quotient has order three; no quotient model is assumed. -/
theorem residual_quotient_card :
    Nat.card (residualCentralizer L V₁ ⧸ pCore 2 (residualCentralizer L V₁)) = 3 := by
  obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
  have b := blockMarking d hA312 hH hU hg hg₁
  have hc := b.terminal_local_core_quotient_card b.earlierStructure
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  change Nat.card (D.g2.L₁ ⧸ pCore 2 D.g2.L₁) = 3 at hc
  rw [hf.g2_L₁] at hc
  exact hc

/-- Original13.5.14(2), in the literal quotient LT/O₂(LT). -/
theorem closure_star_core :
    let S := chapter13Setup V₁ V₃ L T H
    S.star (Source.UH H V₃) = (S.star (residualCentralizer L V₁)).pCoreIn 2 ∧
      Nat.card (S.star (Source.UH H V₃)) = 4 := by
  obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
  have b := blockMarking d hA312 hH hU hg hg₁
  have hc := b.star_U_eq_local_core
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  change D.g2.star D.g2.U = (D.g2.star D.g2.L₁).pCoreIn 2 at hc
  rw [hf.g2_L₁] at hc
  exact ⟨hc,b.star_U_card⟩

/-- The actual starred residual in13.5.15(1) is cyclic of order three. -/
noncomputable def normal_residual_star_cubic
    (hn : ((residualCentralizer L V₁).subgroupOf H).Normal) :
    Source.starImage H (residualCentralizer L V₁) ≃* Multiplicative (ZMod 3) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  exact (NormalBranch.localStarEquiv hf hn).symm.trans
    (mulEquivOfPrimeCardEq (residual_quotient_card d hA312 hH hU) (by simp))

/-- The bound in13.5.23 comes from the original star-map kernel. -/
theorem residual_core_card_bound :
    Nat.card ((residualCentralizer L V₁).pCoreIn 2) ≤ 4 * Nat.card (L.pCoreIn 2) := by
  obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
  let S := chapter13Setup V₁ V₃ L T H
  let b : Hypothesis S g := blockMarking d hA312 hH hU hg hg₁
  let f := terminalLocalStarProjection S
  have hcard := b.terminal_star_local_card b.earlierStructure
  have hquot := b.terminal_local_core_quotient_card b.earlierStructure
  have hk : Nat.card f.ker * 12 = Nat.card S.L₁ := by
    have he := f.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr (terminalLocalStarProjection_surjective S),
      Nat.card_congr (topEquiv : (⊤ : Subgroup (S.star S.L₁)) ≃* S.star S.L₁).toEquiv,
      hcard] at he
    exact he
  have hc : Nat.card (pCore 2 S.L₁) * 3 = Nat.card S.L₁ := by
    have he := (pCore 2 S.L₁).card_mul_index
    rw [index_eq_card,hquot] at he
    exact he
  have hker : f.ker.map S.L₁.subtype ≤ L.pCoreIn 2 := by
    rintro x ⟨y,hy,rfl⟩
    have hy1 : f y = 1 := hy
    have hy2 := congrArg Subtype.val hy1
    have hm : (y : G) ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      let z : S.LT := ⟨y, (((map_subtype_le _).trans inf_le_left).trans
        le_sup_left) y.property⟩
      have hz : QuotientGroup.mk' (pCore 2 S.LT) z = 1 := hy2
      exact mem_map_of_mem S.LT.subtype ((QuotientGroup.eq_one_iff z).mp hz)
    rw [← d.local_core_intersection]
    exact ⟨(map_subtype_le _).trans inf_le_left y.property,hm⟩
  have hbound : Nat.card f.ker ≤ Nat.card (L.pCoreIn 2) := by
    rw [← card_map_of_injective (K := f.ker) S.L₁.subtype_injective]
    exact card_le_of_le hker
  have hres : residualCentralizer L V₁ = S.L₁ := by
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    exact hf.g2_L₁.symm
  rw [hres,pCoreIn,card_map_of_injective S.L₁.subtype_injective]
  omega

end CFSG.Quasithin.Chapter13.Section05.A5Source
