module
public import CFSG.Quasithin.ChapterG.Section10.Reducible.Solvable
public import CFSG.Quasithin.ChapterG.Section10.TwoCore
public import Theory.Representation.NormalComponentConstituents
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Component constituents in the original G.10 action

For a nonsolvable G.10 actor, G.10.5 gives irreducibility and G.10.3 gives
trivial two-core. A nontrivial part of X centralizing the Fitting subgroup
therefore moves an actual component. Its literal normal orbit has zero fixed
space and full commutator space, and supplies an irreducible constituent of
degree greater than two with spanning conjugates, trivial intersections,
and an isotropic or nondegenerate restricted form.

The Fitting-centralizer intersection is the input from G.11.5. This module
proves the G.10.6--7 constituent reduction; it does not assume the later list
of component models. Source: Aschbacher--Smith, printed pp.359--360, 366.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- G.11.5's nontrivial Fitting-centralizer intersection selects the actual
component and constructs the G.10.7 constituent on its normal orbit. -/
theorem exists_moved_component_constituents (hn : ¬ Group.IsSolvable G)
    (hF : X ⊓ centralizer (fittingSubgroup G : Set G) ≠ ⊥) :
    ∃ L : Subgroup G, IsComponent G L ∧ ⁅L, X⁆ ≠ ⊥ ∧
      ComponentOrbitConstituents ρ B L := by
  obtain ⟨L,hL,hm⟩ := exists_component_moved_of_centralizes_fitting 2
    (X ⊓ centralizer (fittingSubgroup G : Set G))
    ((IsElementaryAbelian.isPGroup 2 X).to_le inf_le_left) hF h.twoCore_eq_bot inf_le_right
  refine ⟨L,hL,?_,componentOrbit_constituents ρ h.faithful
    (h.irreducible_of_not_solvable hn) B h.alternating h.preserves hL⟩
  intro hb
  exact hm (le_bot_iff.mp ((commutator_mono le_rfl inf_le_left).trans hb.le))

/-- The chosen homogeneous member has an independent orbit under the literal
source X. No faithfulness on the chosen constituent is assumed. -/
theorem exists_moved_component_selection (hn : ¬ Group.IsSolvable G)
    (hF : X ⊓ centralizer (fittingSubgroup G : Set G) ≠ ⊥) :
    ∃ L : Subgroup G, IsComponent G L ∧ ⁅L, X⁆ ≠ ⊥ ∧
      ComponentOrbitSelection ρ B L X := by
  obtain ⟨L,hL,hm,_⟩ := h.exists_moved_component_constituents hn hF
  exact ⟨L,hL,hm,componentOrbit_selection ρ h.faithful
    (h.irreducible_of_not_solvable hn) B h.alternating h.preserves hL
    (IsElementaryAbelian.isPGroup 2 X)⟩

/-- The forward direction of G.10.11: the common nonzero marked vector
forces X to stabilize a constituent, because distinct translates are disjoint. -/
theorem stabilizes_constituent_of_point_mem (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ H I) (hv : v ∈ I) : X ≤ subspaceStabilizer ρ I := by
  intro x hx
  apply (subspace_map_eq_iff ρ I x).mp
  rcases hI.eq_or_disjoint_conjugate_of_normal_restriction ρ hi H x with he | hd
  · exact he
  · have hvm : v ∈ I.map (ρ x) := ⟨v,hv,h.fixes_point hx⟩
    exact (h.point_ne_zero (Submodule.disjoint_def.mp hd v hvm hv)).elim

/-- G.10.12(1) follows from the literal full transvection action and TI:
a constituent avoiding the marked point meets W in at most a line. -/
theorem constituent_inter_W_finrank_le_one (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ H I) (hv : v ∉ I) : finrank (ZMod 2) (I ⊓ W : Submodule (ZMod 2) V) ≤ 1 := by
  classical
  by_cases hz : I ⊓ W = ⊥
  · rw [hz]
    simp
  obtain ⟨a,ha,ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
  have hle : I ⊓ W ≤ Submodule.span (ZMod 2) {a} := by
    intro b hb
    have hbspan : b ∈ Submodule.span (ZMod 2) {v} ⊔ Submodule.span (ZMod 2) {a} := by
      by_contra hnot
      obtain ⟨f,hfb,hfk⟩ := (Submodule.span (ZMod 2) {v} ⊔
        Submodule.span (ZMod 2) {a}).exists_le_ker_of_notMem hnot
      have hfv : f v = 0 := hfk (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
      have hfa : f a = 0 := hfk (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a))
      obtain ⟨x,hx⟩ := h.full_transvections (f.comp W.subtype) hfv
      have hxa : ρ x a = a := by
        have he := hx ⟨a,ha.2⟩
        change ρ x a = a + f a • v at he
        simpa only [hfa, zero_smul, add_zero] using he
      have hxI : I.map (ρ (x : G)) = I := by
        rcases hI.eq_or_disjoint_conjugate_of_normal_restriction ρ hi H x with he | hd
        · exact he
        · exact (ha0 (Submodule.disjoint_def.mp hd a ⟨a,ha.1,hxa⟩ ha.1)).elim
      have hxb : ρ x b ∈ I := hxI ▸ (show ρ x b ∈ I.map (ρ (x : G)) from ⟨b,hb.1,rfl⟩)
      have hdiff := I.sub_mem hxb hb.1
      have he := hx ⟨b,hb.2⟩
      change ρ x b = b + f b • v at he
      rw [he,add_sub_cancel_left] at hdiff
      exact hv ((I.smul_mem_iff hfb).mp hdiff)
    obtain ⟨c,hc,d,hd,he⟩ := Submodule.mem_sup.mp hbspan
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hc
    have hcI : c ∈ I := by
      have hdI : d ∈ I := (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ha.1)) hd
      have he' : c = b - d := by rw [← he]; abel
      rw [he']
      exact I.sub_mem hb.1 hdI
    have hr0 : r = 0 := by
      by_contra hr0
      exact hv ((I.smul_mem_iff hr0).mp (hr.symm ▸ hcI))
    have hc0 : c = 0 := by simpa only [hr0,zero_smul] using hr.symm
    rw [hc0,zero_add] at he
    exact he ▸ hd
  exact (Submodule.finrank_mono hle).trans (by simpa using finrank_span_le_card ({a} : Set V))

end CFSG.Quasithin.ChapterG.Section10.Hypothesis


namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The original terminal action satisfies G.10.12(1) on every selected
constituent of its normal component orbit. -/
theorem terminal_constituent_inter_W_finrank_le_one (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (h : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    (H : Subgroup F.TerminalHdot) [H.Normal]
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation H I) (hv : v ∉ I) :
    Module.finrank (ZMod 2) (I ⊓ hatSpace F (F.E g) : Submodule (ZMod 2) (Additive F.Uhat)) ≤ 1 :=
  h.constituent_inter_W_finrank_le_one (h.irreducible_of_not_solvable hn) H hI hv

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
