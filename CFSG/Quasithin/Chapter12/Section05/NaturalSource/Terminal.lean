module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Subgroups
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Rigidity
public import Theory.GroupTheory.ElementFusionTransport
public import Theory.GroupTheory.PCoreRestriction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The terminal commutator argument for 12.5.1

Write A = Vᵍ, Q_H = O₂(L₁H), B = A ∩ Q_H and U_H = ⟨V₇ᴴ⟩.
Once U_H normalizes A, its commutator with B lies both in A and in V₁.
If that commutator is nontrivial, V₁ lies in A. Point fusion and V ≤ O₂(G₁)
then put A in O₂(G₁) ∩ H ≤ O₂(H), contradicting its choice.
Thus U_H centralizes B. The actual E.3.6 centralizer-rigidity theorem,
applied below s(G,A), makes U_H centralize A. The faithful local action
kernel again puts A in O₂(H), giving the final contradiction.

The records below are explicit obligations for the preceding source
arguments. Their existence is not asserted here. In particular the local
component, fusion, corank and escaping-subgroup constructions still have
to supply them before this proves the exterior exclusion.

Source: Aschbacher--Smith, proof of 12.5.1, printed p.822. The kernel bound
retained here is the consequence on U_H of the faithful action on U_H/V₁.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The precise point geometry, core and fusion consequences used at the end. -/
structure PointControl (a : ExteriorMarking D) : Prop where
  line_card : Nat.card (a.Vi 1) = 2
  point_mem : a.z ∈ a.Vi 1
  point_centralizer : a.Gi 1 = centralizer ({a.z} : Set G)
  seed_core : V ≤ (a.Gi 1).pCoreIn 2
  fusion : ∀ x : G, MulAut.conj x a.z ∈ V →
    ∃ l ∈ L, MulAut.conj x a.z = MulAut.conj l a.z

/-- The original final two-core, with its inclusion into G. -/
def terminalCore (a : ExteriorMarking D) (H : Subgroup G) : Subgroup G :=
  (a.Li 1 ⊔ H).pCoreIn 2

/-- The actual intersection B = A ∩ Q_H; it is not an arbitrary small kernel. -/
def terminalIntersection (a : ExteriorMarking D) (H : Subgroup G) (g : G) : Subgroup G :=
  V.map (MulAut.conj g).toMonoidHom ⊓ terminalCore a H

/-- The source construction on p.822, prior to the final commutator argument. -/
structure TerminalConfiguration (a : ExteriorMarking D) where
  H : Subgroup G
  sylow_le : (T : Subgroup G) ≤ H
  point_le : H ≤ a.Gi 1
  g : G
  conjugate_le : V.map (MulAut.conj g).toMonoidHom ≤ H
  escapes_core : ¬ V.map (MulAut.conj g).toMonoidHom ≤ H.pCoreIn 2
  span_two : IsPGroup 2 (a.UH H)
  span_normalizes : a.UH H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)
  commutator_line : ⁅a.UH H, terminalIntersection a H g⁆ ≤ a.Vi 1
  small_corank : let := D.elementary
    let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj g).toMonoidHom
    (ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (terminalIntersection a H g) : ℕ∞) <
        ChapterE.globalS (V.map (MulAut.conj g).toMonoidHom)
  action_kernel : H ⊓ centralizer (a.UH H : Set G) ≤ terminalCore a H

omit [Finite G] in
/-- Fusion and core restriction kill the possible commutator line. -/
theorem terminal_commutator_eq_bot (a : ExteriorMarking D) (p : PointControl a)
    (d : TerminalConfiguration a) :
    ⁅a.UH d.H, terminalIntersection a d.H d.g⁆ = ⊥ := by
  let C := ⁅a.UH d.H, terminalIntersection a d.H d.g⁆
  have hC : C ≤ a.Vi 1 := d.commutator_line
  let : Fact (Nat.card (a.Vi 1)).Prime := ⟨by rw [p.line_card]; exact Nat.prime_two⟩
  rcases (C.subgroupOf (a.Vi 1)).eq_bot_or_eq_top_of_prime_card with hb | ht
  · apply le_bot_iff.mp
    exact (le_inf le_rfl hC).trans (disjoint_iff_inf_le.mp (subgroupOf_eq_bot.mp hb))
  · have hline : a.Vi 1 ≤ C := subgroupOf_eq_top.mp ht
    have hCA : C ≤ V.map (MulAut.conj d.g).toMonoidHom :=
      (commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp d.span_normalizes)
    have hz : a.z ∈ V.map (MulAut.conj d.g).toMonoidHom :=
      hCA (hline p.point_mem)
    have hcoreNorm : centralizer ({a.z} : Set G) ≤
        normalizer ((a.Gi 1).pCoreIn 2 : Set G) := by
      rw [← p.point_centralizer]
      exact (a.Gi 1).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (a.Gi 1) (pCore 2 (a.Gi 1)))
    have hcore : V.map (MulAut.conj d.g).toMonoidHom ≤ (a.Gi 1).pCoreIn 2 := by
      apply conjugate_le_of_element_fusion_of_normalized ?_ p.seed_core hcoreNorm hz
      intro x hx
      obtain ⟨l, hl, he⟩ := p.fusion x hx
      exact ⟨l, D.normalizes hl, he.symm⟩
    exact (d.escapes_core ((le_inf d.conjugate_le hcore).trans
      (inf_pCoreIn_le_of_le 2 d.point_le))).elim

/-- The final deduction uses E.3.6 itself, with the literal A, B and U_H.
Existence of the two source records remains an obligation of the assembly. -/
theorem exterior_contradiction_of_point_and_terminal
    (a : ExteriorMarking D) (p : PointControl a) (d : TerminalConfiguration a) : False := by
  let := D.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj d.g).toMonoidHom
  have hUB : a.UH d.H ≤ centralizer (terminalIntersection a d.H d.g : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (terminal_commutator_eq_bot a p d)
  have he := ChapterE.centralizer_inf_eq_of_corank_lt_globalS
    (show terminalIntersection a d.H d.g ≤ V.map (MulAut.conj d.g).toMonoidHom
      from inf_le_left) d.small_corank d.span_two
  have hUA : a.UH d.H ≤ centralizer (V.map (MulAut.conj d.g).toMonoidHom : Set G) := by
    intro x hx
    exact (he.le ⟨hx, hUB hx⟩).2
  have hAcore := (le_inf d.conjugate_le (le_centralizer_iff.mp hUA)).trans d.action_kernel
  exact d.escapes_core ((le_inf d.conjugate_le hAcore).trans
    (inf_pCoreIn_le_of_le 2 (show d.H ≤ a.Li 1 ⊔ d.H from le_sup_right)))

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
