module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Nonbinary.Realization
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.Normalizers

/-!
# The escaping intermediate subgroup in the nonbinary Borel case

Pull the long root back through the actual matrix model and call it D.
For W = [V,L ∩ M] and C = C_V(L), the source decomposition is V = W × C.
When W maps onto the central root plane, |W| = q² and |D| = q. Thus
A = D × C has index q in V. The action-corank bound forces U < A,
and its positive corank forces A < V. The full long-root centralizer
escapes the Borel and centralizes A, giving C_L(A) ≰ M.

Source: Aschbacher–Smith E.6.8(2a), printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour

open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}
variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
/-- The long-root factor supplies the strict intermediate subgroup in E.6.8(2a). -/
theorem centralPlane_escape
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B)
    (hF : Nat.card F = 2 ^ n) (e : L ≃* Sp F)
    (hplane : ((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom =
      (CentralRootGeometry.parameter (F := F)).range)
    (hJ : ((L ⊓ M).subgroupOf L).map e.toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.borel) :
    ∃ A : Subgroup G, U < A ∧ A < V ∧ subgroupCorank V A = n ∧
      ¬ L ⊓ centralizer (A : Set G) ≤ M := by
  let W := ⁅V, L ⊓ M⁆
  let C := V ⊓ centralizer (L : Set G)
  let R := (RootSubgroup.group (F := F) 0).map e.symm.toMonoidHom
  let D := R.map L.subtype
  let A := D ⊔ C
  have hd := decomposition hclass h hU hL hn hm hB
  have hWL : W ≤ L := displacement_le_component h hU hL
  have hWV : W ≤ V := hd.1 ▸ le_sup_left
  have hRimage : R.map e.toMonoidHom = RootSubgroup.group 0 := by
    simp [R, map_map]
  have h0Z : RootSubgroup.group (F := F) 0 ≤ (CentralRootGeometry.parameter (F := F)).range := by
    intro x hx
    obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 0 x).mp hx
    refine ⟨(Multiplicative.ofAdd t, Multiplicative.ofAdd 0), ?_⟩
    simp [CentralRootGeometry.parameter_apply, RootSubgroup.element_zero]
  have hRW : R ≤ W.subgroupOf L := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hRimage, hplane]
    exact h0Z
  have hDW : D ≤ W := by
    have hh := map_mono (f := L.subtype) hRW
    rwa [map_subgroupOf_eq_of_le hWL] at hh
  have hAV : A ≤ V := sup_le (hDW.trans hWV) inf_le_left
  have hUC : U ≤ C := fixedSpace_contains hU.1 hL.1
  have hCW : C ≤ centralizer (W : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hd.2.2)
  have hWC : Disjoint W C := disjoint_iff.mpr hd.2.1
  have hDC : Disjoint D C := hWC.mono_left hDW
  have hcD : Nat.card D = 2 ^ n := by
    rw [card_map_of_injective L.subtype_injective,
      card_map_of_injective e.symm.injective, RootSubgroup.card, hF]
  have hcW : Nat.card W = (2 ^ n) ^ 2 := by
    calc
      Nat.card W = Nat.card (W.subgroupOf L) :=
        (Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv).symm
      _ = Nat.card ((W.subgroupOf L).map e.toMonoidHom) :=
        (card_map_of_injective e.injective).symm
      _ = (2 ^ n) ^ 2 := by rw [hplane, BorelActionGeometry.card_centralPlane, hF]
  have hcV : Nat.card V = (2 ^ n) ^ 2 * Nat.card C := by
    calc
      Nat.card V = Nat.card (W ⊔ C : Subgroup G) := congrArg (fun H : Subgroup G => Nat.card H) hd.1.symm
      _ = Nat.card W * Nat.card C := card_sup_eq_mul_of_normalizes_of_disjoint W C
        (hCW.trans (centralizer_le_normalizer W)) hWC
      _ = _ := by rw [hcW]
  have hcA : Nat.card A = 2 ^ n * Nat.card C := by
    calc
      Nat.card A = Nat.card D * Nat.card C := card_sup_eq_mul_of_normalizes_of_disjoint D C
        ((hCW.trans (centralizer_le hDW)).trans (centralizer_le_normalizer D)) hDC
      _ = _ := by rw [hcD]
  have hi : A.relIndex V = 2 ^ n := by
    have ht := relIndex_mul_relIndex (⊥ : Subgroup G) A V bot_le hAV
    simp only [relIndex_bot_left] at ht
    rw [hcA, hcV, pow_two] at ht
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos (by decide : 0 < 2) n) (show 0 < Nat.card C from Nat.card_pos))
    exact ht.trans (by ac_rfl)
  have hcod : subgroupCorank V A = n := by
    rw [subgroupCorank, hi, Nat.log_pow (by decide : 1 < 2)]
  have hdim := actionCorank_of_centralPlane_image hclass h hU hL hn hm hB hF e hplane
  have hbound := fixedSpace_corank_le hU.1 hL.1
  change actionCorank V L ≤ subgroupCorank V U at hbound
  rw [hdim] at hbound
  refine ⟨A, lt_of_le_of_ne (hUC.trans le_sup_right) ?_, lt_of_le_of_ne hAV ?_, hcod, ?_⟩
  · intro he
    rw [he, hcod] at hbound
    omega
  · intro he
    rw [he, subgroupCorank, relIndex_self] at hcod
    norm_num at hcod
    omega
  · intro hesc
    apply BorelActionGeometry.centralizer_zero_not_le_borel (F := F)
    intro x hx
    rw [← hJ]
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    refine ⟨(e.symm x).property, hesc ⟨(e.symm x).property, ?_⟩⟩
    have hxD : (e.symm x : G) ∈ centralizer (D : Set G) := by
      apply mem_centralizer_iff.mpr
      rintro d ⟨r, hr, rfl⟩
      change ((r * e.symm x : L) : G) = ((e.symm x * r : L) : G)
      apply congrArg (fun z : L => (z : G))
      apply e.injective
      have hr' : e r ∈ RootSubgroup.group 0 := hRimage ▸ mem_map_of_mem e.toMonoidHom hr
      simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_iff.mp hx (e r) hr'
    have hxC : (e.symm x : G) ∈ centralizer (C : Set G) :=
      (le_centralizer_iff.mpr (show C ≤ centralizer (L : Set G) from inf_le_right))
        (e.symm x).property
    change (e.symm x : G) ∈ centralizer ((D ⊔ C : Subgroup G) : Set G)
    have hs : D ⊔ C ≤ centralizer ({(e.symm x : G)} : Set G) := sup_le
      (fun d hd => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxD d hd))
      (fun c hc => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxC c hc))
    exact mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (hs ha)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
