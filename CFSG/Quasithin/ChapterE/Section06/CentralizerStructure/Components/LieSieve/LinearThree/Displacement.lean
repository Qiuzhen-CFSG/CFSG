module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# Displacement bounds before the PSL₃ Borel calculation

The obstruction residual gives a coprime splitting for the actual action of
L ∩ M. This makes its displacement disjoint from Z(L), even before the fixed
space is identified with C_V(L). The displacement lies in the center of the
marked Sylow subgroup. In an ordinary PSL₃ model that center has order 2ⁿ;
in a central cover, the displacement injects into the corresponding center
in the quotient. Thus both branches have the same displacement bound.

Only the independent Sylow-center containment from `BorelActions.Reduction`
is used here. No Borel alternative, torus complement or exact corank is
assumed. In particular the quotient argument permits the trivial center.

Source: Aschbacher–Smith, E.6.8, printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- Coprime splitting separates the displacement from the entire component center. -/
theorem displacement_disjoint_component_center
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    ⁅V, L ⊓ M⁆ ⊓ (center L).map L.subtype = ⊥ := by
  have hd := intersection_decomposition h hU hL
  apply le_bot_iff.mp
  rintro _ ⟨hw, z, hz, rfl⟩
  have hzC : (z : G) ∈ centralizer ((L ⊓ M : Subgroup G) : Set G) := by
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl.1⟩)
  have hwV : (z : G) ∈ V := (le_sup_left.trans hd.1.le) hw
  exact hd.2.1 ▸ ⟨hw, hwV, hzC⟩

/-- The ordinary bound uses the actual Sylow center, without Borel placement. -/
theorem displacement_card_le_linear_three
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    Nat.card (⁅V, L ⊓ M⁆ : Subgroup G) ≤ 2 ^ n := by
  obtain ⟨hnorm, S, hS, _⟩ := component_sylow_action h hU hL rfl
  have hW := BorelActions.displacement_le_center h hU hL hnorm rfl
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  have hc := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (by omega) hF e S
  have hcenter : ((center S).map (S : Subgroup L).subtype).map L.subtype =
      (center ↥(L ⊓ sylowCentralizer (T : Subgroup G) V)).map
        (L ⊓ sylowCentralizer (T : Subgroup G) V).subtype := by
    rw [map_subgroup_center_eq L.subtype L.subtype_injective, hS]
  have hcard := card_le_of_le hW
  rw [← hcenter, card_map_of_injective L.subtype_injective,
    card_map_of_injective (S : Subgroup L).subtype_injective, hc] at hcard
  exact hcard

/-- The displacement injects into the quotient Sylow center. No restriction on
the size of the covering center is imposed. -/
theorem displacement_card_le_quotient_linear_three
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n)
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n)) :
    Nat.card (⁅V, L ⊓ M⁆ : Subgroup G) ≤ 2 ^ n := by
  let W : Subgroup G := ⁅V, L ⊓ M⁆
  let q := QuotientGroup.mk' (center L)
  obtain ⟨hnorm, S, hS, _⟩ := component_sylow_action h hU hL rfl
  have hW := BorelActions.displacement_le_center h hU hL hnorm rfl
  have hWL : W ≤ L := hW.trans ((map_subtype_le _).trans inf_le_left)
  have hcenter : ((center S).map (S : Subgroup L).subtype).map L.subtype =
      (center ↥(L ⊓ sylowCentralizer (T : Subgroup G) V)).map
        (L ⊓ sylowCentralizer (T : Subgroup G) V).subtype := by
    rw [map_subgroup_center_eq L.subtype L.subtype_injective, hS]
  have hWZ : W.subgroupOf L ≤ (center S).map (S : Subgroup L).subtype := by
    intro w hw
    obtain ⟨s, hs, he⟩ := hcenter.symm ▸ hW hw
    exact L.subtype_injective he ▸ hs
  have hker : W.subgroupOf L ⊓ q.ker = ⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨hxW, hxq⟩
    have hxZ : x ∈ center L := (QuotientGroup.ker_mk' (center L)) ▸ hxq
    have hh : (x : G) ∈ W ⊓ (center L).map L.subtype :=
      ⟨hxW, mem_map_of_mem L.subtype hxZ⟩
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp
      (displacement_disjoint_component_center h hU hL ▸ hh)))
  have hinj : Function.Injective (q.subgroupMap (W.subgroupOf L)) := by
    intro x y hxy
    apply inv_mul_eq_one.mp
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hker]
    refine ⟨(W.subgroupOf L).mul_mem ((W.subgroupOf L).inv_mem x.property) y.property, ?_⟩
    change q ((x : L)⁻¹ * (y : L)) = 1
    rw [map_mul, map_inv, show q (x : L) = q (y : L) from congrArg Subtype.val hxy]
    exact inv_mul_cancel _
  have he : Nat.card ((W.subgroupOf L).map q) = Nat.card W := by
    rw [← Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap (W.subgroupOf L))
      ⟨hinj, q.subgroupMap_surjective _⟩).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv
  have hi := (map_mono (f := q) hWZ).trans (map_subgroup_center_le q (S : Subgroup L))
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective (center L))
  have hc : Nat.card (center ((S : Subgroup L).map q)) = 2 ^ n :=
    Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (by omega) hF e R
  have hh := card_le_of_le hi
  rw [he, card_map_of_injective ((S : Subgroup L).map q).subtype_injective, hc] at hh
  exact hh

/-- Binary dimension version of the ordinary displacement bound. -/
theorem displacement_dimension_le_linear_three
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    subgroupCorank ⁅V, L ⊓ M⁆ ⊥ ≤ n := by
  simpa only [subgroupCorank, relIndex_bot_left, Nat.log_pow (by decide : 1 < 2)] using
    Nat.log_mono_right (b := 2) (displacement_card_le_linear_three h hU hL hn iso)

/-- Every central cover of PSL₃(4) has displacement dimension at most two;
this includes the trivial covering center. -/
theorem displacement_dimension_le_linear_three_cover
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    subgroupCorank ⁅V, L ⊓ M⁆ ⊥ ≤ 2 := by
  simpa only [subgroupCorank, relIndex_bot_left, Nat.log_pow (by decide : 1 < 2)] using
    Nat.log_mono_right (b := 2)
      (displacement_card_le_quotient_linear_three h hU hL (n := 2) (by decide) iso)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree
