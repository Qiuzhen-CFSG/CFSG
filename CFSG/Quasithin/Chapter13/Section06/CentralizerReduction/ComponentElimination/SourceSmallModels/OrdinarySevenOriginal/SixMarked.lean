module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.SixCore
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.Module

/-!
# The original marked point for the six-point replacement

The source Sylow centralizer restricts to the replacement joined with Tᵥ,
so the replacement has an intrinsic Sylow two-subgroup inside Tᵥ. Its core
commutator lies in the original ordinary A₇ layer U_K, hence in W_K.
The original checked-central point a therefore satisfies the Sylow-averaging
criterion on that elementary layer. Equality of the Lᵥ- and replacement-fixed
subgroups is the only remaining action input.

Source: Aschbacher–Smith, Lemma 13.6.22, printed pp.932–933, with the original
marked local configuration of 13.6.2–5, printed pp.926–927.
-/

public section
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
open ComponentSelection A5Module SourceContainment
open BinaryRankTwo.SourceActors AlternatingBranches.OrdinarySeven
open LinearThreeBranch.MSSourceModels LinearThreeBranch.MSSourceModels.SeedCarrier
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {K L M V V₁ V₂ : Subgroup G}

/-- The six-point replacement centralizes the actual original marked a once
its fixed space on W_K agrees with the fixed space of Lᵥ. No short-block
recognition of the replacement, new marked point or Sylow witness is assumed. -/
theorem replacement_centralizes_markedA
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hblock : IsAlternatingBlock K 7)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hLB : Lv L (markedV d.flag.module) ≤ replacement K e 6)
    (hTB : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (replacement K e 6 : Set G))
    (hfix : WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ⊓
        centralizer (Lv L (markedV d.flag.module) : Set G) =
      WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ⊓
        centralizer (replacement K e 6 : Set G)) :
    replacement K e 6 ≤ Gv (markedA d.flag.module) := by
  let B := replacement K e 6
  let T₀ := Tv (T : Subgroup G) (markedV d.flag.module)
  let W := WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)
  have hBK : B ≤ K := replacement_le K e 6
  have hBv := hBK.trans hK.1.1
  obtain ⟨hW, hWT, _, hUK⟩ :=
    module_inputs_of_localConfiguration d c hblock hK hn hLK hchar hL hz
  let := hW
  have hKW : K ≤ normalizer (W : Set G) := by
    dsimp [W]
    rw [WK_eq_seedSpan hn hLK]
    exact le_normalizer_conjugateSpanBy _ _
  have hUeq : (blockU K).map K.subtype = ⁅W, K⁆ :=
    (sourceU_eq_of_central K hblock.2.1.twoPerfect hblock.2.1.central).symm.trans hUK.symm
  have hcore : (blockU B).map B.subtype ≤ W :=
    (replacement_core_commutator_le K e 6).trans
      (hUeq.le.trans (le_normalizer_iff_commutator_le_left.mp hKW))
  have hSylow : Chapter1.IsSylowIn 2 T₀ (Gv (markedV d.flag.module)) :=
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  obtain ⟨S, hS⟩ := hSylow.restrict
    (show T₀ ≤ B ⊔ T₀ from le_sup_right) (sup_le hBv inf_le_right)
  have hS' : (S : Subgroup ↥(B ⊔ T₀)) = T₀.subgroupOf (B ⊔ T₀) := by
    apply map_injective (B ⊔ T₀).subtype_injective
    rw [hS, map_subgroupOf_eq_of_le (show T₀ ≤ B ⊔ T₀ from le_sup_right)]
  obtain ⟨P, hP⟩ := exists_source_sylow hTB S hS'
  have hP' : (P : Subgroup B).map B.subtype ≤ T₀ := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hP] at hk
    exact hk
  have hv : markedV d.flag.module ^ 2 = 1 := by
    change d.flag.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
    rw [← map_pow]
    exact (congrArg d.flag.module.map
      (show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
        by decide +kernel)).trans d.flag.module.map.map_one
  have haD : ((inclusion inf_le_right c.aPoint : Gv (markedV d.flag.module)) : G) ∈
      centralizer (Lv L (markedV d.flag.module) : Set G) := by
    change (c.aPoint : G) ∈ _
    rw [c.aPoint_val]
    exact c.a_centralizes.2
  have ha : checkedQuotientMap (markedV d.flag.module) (inclusion inf_le_right c.aPoint) ∈
      centralizer (checkedImage (markedV d.flag.module) T₀ : Set (Gcheck (markedV d.flag.module))) := by
    rintro x ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp c.a_checked_central
      ((checkedSylowMap (T : Subgroup G) (markedV d.flag.module)).rangeRestrict ⟨y, hy⟩))
  have hc := checked_centralizes_of_elementary_layer L B T₀ W
    (markedV d.flag.module) hBv hv (hWT.trans inf_le_right)
    (replacement_twoPerfect K e 6) (hBK.trans hKW) hcore hTB
    c.reductions.centralizerSylow c.reductions.sylow_image P hP' hchar hLB hfix
    (inclusion inf_le_right c.aPoint) haD ha
  change B ≤ Gv (c.aPoint : G) at hc
  rwa [c.aPoint_val] at hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
