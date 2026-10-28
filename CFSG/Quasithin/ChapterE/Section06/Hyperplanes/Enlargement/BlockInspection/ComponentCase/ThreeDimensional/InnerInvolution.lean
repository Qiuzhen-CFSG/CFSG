module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ModelExclusions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models

/-!
# An inner involution for the Borel inspection in E.6.23

Write W = [V, X ∩ M]. The genuine E.6.8 decomposition gives V = W × A,
and normalization of X puts W inside X. Choose an element of U outside A
and split it as wa. Since A ≤ U, its W-part lies in U ∩ X. The fixed-space
equality C_V(X) = A shows that this part is noncentral in X.

The actual small block centralizes this involution. Its alternating quotient
has order divisible by three, so the full involution centralizer does too.
No normality of the block in that centralizer is needed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1)
and E.6.23, printed pp.247,254 (PDF pp.258,265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
open ComponentBalance Components
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- The Borel displacement supplies an inner involution in the hyperplane
whose image in the component's central quotient is nonidentity. -/
theorem borel_hyperplane_inner_involution [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U A X : Subgroup G} (hUh : IsHyperplane V U)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U)
    (hc : subgroupCorank V A = 2) (hX : CentralizerComponent A X)
    (hfixed : V ⊓ centralizer (X : Set G) = A) (b : BorelAlternative M V A X 2) :
    ∃ t : X, (t : G) ∈ U ∧ t ∉ center X ∧ t ^ 2 = 1 := by
  have hVN := (component_sylow_action h hA hX rfl).1
  let W : Subgroup G := ⁅V, X ⊓ M⁆
  have hWX : W ≤ X :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp hVN)
  have hd := b.decomposition (by decide)
  rw [hfixed] at hd
  have hWV : W ≤ V := le_sup_left.trans hd.1.le
  have hnUA : ¬ U ≤ A := by
    intro hh
    have := subgroupCorank_antitone (V := V) hh
    rw [hc, hUh.2] at this
    omega
  obtain ⟨u, hu, huA⟩ := Set.not_subset.mp hnUA
  have hs : W.subgroupOf V ⊔ A.subgroupOf V = ⊤ := by
    rw [← subgroupOf_sup hWV hA.1]
    change (W ⊔ A).subgroupOf V = ⊤
    rw [hd.1, subgroupOf_self]
  let _ : (A.subgroupOf V).Normal := normal_of_isMulCommutative _
  obtain ⟨w, hw, a, ha, hwa⟩ := mem_sup_of_normal_right.mp
    (show (⟨u, hUh.1 hu⟩ : V) ∈ W.subgroupOf V ⊔ A.subgroupOf V by rw [hs]; trivial)
  have hwG : (w : G) * (a : G) = u := congrArg Subtype.val hwa
  have hwU : (w : G) ∈ U := by
    have he : (w : G) = u * (a : G)⁻¹ := eq_mul_inv_iff_mul_eq.mpr hwG
    rw [he]
    exact U.mul_mem hu (U.inv_mem (hAU ha))
  refine ⟨⟨w, hWX hw⟩, hwU, ?_, ?_⟩
  · intro hwZ
    have hwC : (w : G) ∈ centralizer (X : Set G) := by
      intro x hx
      exact congrArg Subtype.val (mem_center_iff.mp hwZ ⟨x, hx⟩)
    have hwA : (w : G) ∈ A := hfixed ▸ ⟨w.property, hwC⟩
    exact huA (hwG ▸ A.mul_mem hwA ha)
  · apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) w w.property

/-- The actual small block embeds in the full centralizer of an element of U. -/
private def smallBlockCentralizerMap {U L X : Subgroup G} (hL : SmallBlock U L)
    (hLX : L ≤ X) (t : X) (htU : (t : G) ∈ U) :
    L →* centralizer ({t} : Set X) where
  toFun l := ⟨⟨l, hLX l.property⟩, mem_centralizer_singleton_iff.mpr (by
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hL.1 l.property) t htU).symm)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
private theorem smallBlockCentralizerMap_injective {U L X : Subgroup G} (hL : SmallBlock U L)
    (hLX : L ≤ X) (t : X) (htU : (t : G) ∈ U) :
    Function.Injective (smallBlockCentralizerMap hL hLX t htU) := by
  intro x y hh
  exact Subtype.ext (congrArg (fun z : centralizer ({t} : Set X) => (z.val : G)) hh)

/-- The original embedded block forces three to divide the full centralizer. -/
theorem smallBlock_three_dvd_centralizer {U L X : Subgroup G} (hL : SmallBlock U L)
    (hLX : L ≤ X) (t : X) (htU : (t : G) ∈ U) :
    3 ∣ Nat.card (centralizer ({t} : Set X)) := by
  have h3 : 3 ∣ Nat.card L := hL.2.2.elim
    (fun hh => three_dvd_card_alternating_block L hh (Or.inl rfl))
    (fun hh => three_dvd_card_alternating_block L hh (Or.inr rfl))
  exact h3.trans (card_dvd_of_injective (smallBlockCentralizerMap hL hLX t htU)
    (smallBlockCentralizerMap_injective hL hLX t htU))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
