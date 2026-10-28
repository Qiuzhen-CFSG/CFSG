module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Carrier
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Nonbinary.Reduction
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.DisplacementRealization.Geometry
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Nonbinary.Realization.Transfers

/-!
# The actual displacement in nonbinary symplectic coordinates

The supplied Borel selects a Sylow two-subgroup of L. The obstruction's
prime-to-two residual inside L ∩ M makes that Sylow centralize V. Hence the
two-subgroup [V,L ∩ M] lies in its center. Sylow conjugacy aligns it with the
standard unipotent center, and normalization by L ∩ M supplies the diagonal
torus invariance. The intrinsic two-weight calculation then gives either
central root or the whole central root plane. The source decomposition and
L ≰ M exclude the trivial subgroup.

The imported transfers give the exact ranks n and 2n and the literal
root-action equality on Sp₄(F)′. Semilinear coverage and Borel containment
are the explicit inputs supplied by this task's contract; no normalizer
maximality or completed SymplecticAlternative is used here.

Source: Aschbacher–Smith E.6.8(2), printed pp.247–248
(PDF pp.258–259 of refs/quasithin.pdf).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open BorelActionGeometry.DisplacementRealization CentralRootGeometry
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L B : Subgroup G} {n : ℕ}

omit [Finite G] in
/-- Relative residual containment makes every Sylow subgroup in the local intersection centralize V. -/
theorem sylow_centralizes_of_le_intersection
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype ≤ L ⊓ M) :
    (S : Subgroup L).map L.subtype ≤ centralizer (V : Set G) := by
  have hp := (S.isPGroup'.map L.subtype).comap_subtype (K := L ⊓ M)
  have hr := le_primeToResidual_of_isPGroup hp
  intro x hx
  exact (component_intersection_residual hU hL.1
    (mem_map_of_mem (L ⊓ M).subtype (hr (show
      (⟨x, hS hx⟩ : ↥(L ⊓ M)) ∈ ((S : Subgroup L).map L.subtype).subgroupOf (L ⊓ M)
      from hx)))).2

/-- The actual displacement lies in the selected Sylow center, without a coordinate assumption. -/
theorem displacement_le_sylow_center
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype ≤ L ⊓ M) :
    (⁅V, L ⊓ M⁆).subgroupOf L ≤ (center S).map (S : Subgroup L).subtype := by
  let _ := h.elementary
  have hWV : ⁅V, L ⊓ M⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp
    (component_intersection_normalizes h hU hL.1)
  have hp := ((IsElementaryAbelian.isPGroup 2 V).to_le hWV).comap_subtype (K := L)
  apply pGroup_le_sylow_center S _ hp
  intro w hw
  apply mem_centralizer_iff.mpr
  intro s hs
  have hc := sylow_centralizes_of_le_intersection hU hL S hS
    (mem_map_of_mem L.subtype hs)
  exact Subtype.ext ((mem_centralizer_iff.mp hc) w (hWV hw)).symm

/-- A trivial moving factor would put L in the normalizer of V, hence in M. -/
theorem displacement_ne_bot
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) :
    ⁅V, L ⊓ M⁆ ≠ ⊥ := by
  intro hw
  have hd := (decomposition hclass h hU hL hn hm hB).1
  rw [hw, bot_sup_eq] at hd
  have hVC : V ≤ centralizer (L : Set G) := hd ▸ inf_le_right
  exact component_not_le h earlier hU hL
    ((le_centralizer_iff.mpr hVC).trans
      ((centralizer_le_normalizer V).trans h.normalizer_le))

/-- Choose actual field and matrix coordinates placing the Borel and classifying the nonzero displacement. -/
theorem exists_displacement_realization
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ ∃ e : L ≃* Sp F,
      Theory.SpecificGroups.SymplecticFour.borel (F := F) ≤ ((L ⊓ M).subgroupOf L).map e.toMonoidHom ∧
      ((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom ≠ ⊥ ∧
      (((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom = RootSubgroup.group 0 ∨
       ((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom = RootSubgroup.group 4 ∨
       ((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom =
         (CentralRootGeometry.parameter (F := F)).range) := by
  obtain ⟨F, _, _, _, hF, ⟨e₀⟩⟩ := exists_full_model hn hm
  obtain ⟨B, hBJ, hBorel⟩ := hB
  obtain ⟨S, hSB⟩ := exists_sylow_normalizer_of_borel (model_center_eq_bot hn hm) hBorel
  obtain ⟨e, hSU, hNB⟩ := align_sylow hF (by omega) e₀ S
  have hSJ : (S : Subgroup L).map L.subtype ≤ L ⊓ M := by
    calc
      _ ≤ (B.subgroupOf L).map L.subtype := map_mono (hSB.symm ▸ le_normalizer)
      _ = B := map_subgroupOf_eq_of_le hBorel.1
      _ ≤ _ := hBJ
  have hBM : Theory.SpecificGroups.SymplecticFour.borel (F := F) ≤ ((L ⊓ M).subgroupOf L).map e.toMonoidHom := by
    rw [← hNB, ← hSB]
    exact map_mono (subgroupOf_mono L hBJ)
  let W := ⁅V, L ⊓ M⁆
  let A := (W.subgroupOf L).map e.toMonoidHom
  have hA : A ≤ (CentralRootGeometry.parameter (F := F)).range := by
    have hz := map_mono (f := e.toMonoidHom) (displacement_le_sylow_center h hU hL S hSJ)
    have he := map_subgroup_center_eq e.toMonoidHom e.injective (S : Subgroup L)
    rw [hSU] at he
    rw [he, ← CentralRootGeometry.parameter_range] at hz
    exact hz
  have hnW : (L ⊓ M).subgroupOf L ≤ normalizer (W.subgroupOf L : Set L) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro w
    exact mem_normalizer_iff.mp (normalizer_commutator_ge_right V (L ⊓ M) hx) w
  have hT : (diagonalTorusHom (F := F)).range ≤ normalizer (A : Set (Sp F)) := by
    rintro x ⟨c, rfl⟩
    have hx := hBM (diagonalTorus_mem_borel c.1 c.2)
    exact (W.subgroupOf L).le_normalizer_map e.toMonoidHom ((map_mono hnW) hx)
  have hne : A ≠ ⊥ := by
    intro ha
    have hWL : W.subgroupOf L = ⊥ := (map_eq_bot_iff_of_injective _ e.injective).mp ha
    have hW : W = ⊥ := by
      calc
        W = (W.subgroupOf L).map L.subtype :=
          (map_subgroupOf_eq_of_le (displacement_le_component h hU hL)).symm
        _ = ⊥ := by rw [hWL, Subgroup.map_bot]
    exact displacement_ne_bot hclass h earlier hU hL hn hm ⟨B, hBJ, hBorel⟩ hW
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by decide : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, e, hBM, hne, ?_⟩
  exact (BorelActionGeometry.invariant_subgroup_cases hlarge A hA hT).resolve_left hne

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
