module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Completion
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus

/-!
# Corank and normalization in the terminal exterior argument

The commutator with each u in U_H takes B into the central point V₁.
Its kernel therefore has index at most two in B. Adding coranks gives
corank at most three in A, so r(G,A)>3 forces u to normalize A. The
separate equality s(G,A)=3 gives the strict corank-two bound for E.3.6.

Source: Aschbacher--Smith, proof of 12.5.1, printed p.822. The quotient
and faithful-action construction supplying B's corank bound is provided
in the later KernelCorank and Completion leaves. No incorrect inequality
s(G,A)>3 is used here.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

private theorem central_commutator_index (B Z : Subgroup G) [IsMulCommutative Z]
    (u : G) (hc : ∀ b ∈ B, ⁅b,u⁆ ∈ Z) (hz : Z ≤ centralizer (B : Set G)) :
    (B ⊓ centralizer ({u} : Set G)).relIndex B ≤ Nat.card Z := by
  let f : B →* Z := {
    toFun b := ⟨⁅(b : G),u⁆, hc b b.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change ⁅(a : G) * b,u⁆ = ⁅(a : G),u⁆ * ⁅(b : G),u⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_centralizer_iff.mp (hz (hc b b.property)) a a.property,
        mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (⟨⁅(b : G),u⁆,hc b b.property⟩ : Z)
        ⟨⁅(a : G),u⁆,hc a a.property⟩) }
  have hk : f.ker = (centralizer ({u} : Set G)).subgroupOf B := by
    ext b
    change (⟨⁅(b : G),u⁆,_⟩ : Z) = 1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅(b : G),u⁆ = 1 ↔ (b : G) ∈ centralizer ({u} : Set G)
    rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]
  rw [inf_relIndex_left]
  change ((centralizer ({u} : Set G)).subgroupOf B).index ≤ _
  rw [← hk, index_ker]
  exact Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective

namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
include h structural

omit h structural in
/-- The centralizer of u in the literal B has corank at most three in A. -/
theorem terminal_centralizer_corank_le_three {H : Subgroup G} {g : G}
    (hHG : H ≤ s.marking.Gi 1)
    (hAH : V.map (MulAut.conj g).toMonoidHom ≤ H)
    (hcomm : ⁅s.marking.UH H, terminalIntersection s.marking H g⁆ ≤ s.marking.Vi 1)
    (hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (terminalIntersection s.marking H g) ≤ 2)
    {u : G} (hu : u ∈ s.marking.UH H) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (terminalIntersection s.marking H g ⊓ centralizer ({u} : Set G)) ≤ 3 := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := terminalIntersection s.marking H g
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (s.marking.Vi 1) :=
    IsElementaryAbelian.of_le (s.marking.subspace_le _)
  have hBA : B ≤ A := inf_le_left
  have hBZ : B ≤ centralizer (s.marking.Vi 1 : Set G) := by
    intro b hb z hz
    have hbG := hHG (hAH (hBA hb))
    rw [s.marking.Gi_one_eq_centralizer] at hbG
    rcases (s.marking.mem_V₁ z).mp hz with rfl | rfl
    · simp
    · exact (mem_centralizer_singleton_iff.mp hbG).symm
  have hi := central_commutator_index B (s.marking.Vi 1) u
    (fun b hb => hcomm (by
      rw [commutator_comm]
      exact commutator_mem_commutator hb hu)) (le_centralizer_iff.mp hBZ)
  rw [s.marking.card_V₁] at hi
  have hc : subgroupCorank B (B ⊓ centralizer ({u} : Set G)) ≤ 1 := by
    exact (Nat.log_mono_right hi).trans (by decide)
  rw [offender_corank_add inf_le_left hBA]
  exact (Nat.add_le_add hcor hc).trans (by decide)

/-- The source's r-bound, rather than its s-bound, promotes U_H to N_G(A). -/
theorem terminal_span_normalizes_of_corank_two {H : Subgroup G} {g : G}
    (hHG : H ≤ s.marking.Gi 1)
    (hAH : V.map (MulAut.conj g).toMonoidHom ≤ H)
    (hcomm : ⁅s.marking.UH H, terminalIntersection s.marking H g⁆ ≤ s.marking.Vi 1)
    (hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (terminalIntersection s.marking H g) ≤ 2) :
    s.marking.UH H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  intro u hu
  let C := terminalIntersection s.marking H g ⊓ centralizer ({u} : Set G)
  have hCA : C ≤ V.map (MulAut.conj g).toMonoidHom := inf_le_left.trans inf_le_left
  have hbound := s.terminal_centralizer_corank_le_three hHG hAH hcomm hcor hu
  have hr : (3 : ℕ∞) < globalR (V.map (MulAut.conj g).toMonoidHom) := by
    rw [globalR_map_equiv]
    exact (s.exteriorFusion_from_source h structural).parameters.1
  apply centralizer_le_normalizer_of_corank_lt_globalR hCA
    ((show (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) C : ℕ∞) ≤ 3 by
      exact_mod_cast hbound).trans_lt hr)
  intro c hc
  exact mem_centralizer_singleton_iff.mp hc.2

/-- Conjugation invariance and s(G,V)=3 discharge the strict terminal bound. -/
theorem terminal_corank_lt_globalS {H : Subgroup G} {g : G}
    (hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (terminalIntersection s.marking H g) ≤ 2) :
    let := D.elementary
    let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj g).toMonoidHom
    (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (terminalIntersection s.marking H g) : ℕ∞) <
        globalS (V.map (MulAut.conj g).toMonoidHom) := by
  dsimp only
  let := D.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj g).toMonoidHom
  rw [globalS_map_equiv, (s.exteriorFusion_from_source h structural).parameters.2.2]
  exact (show (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
    (terminalIntersection s.marking H g) : ℕ∞) ≤ 2 by exact_mod_cast hcor).trans_lt (by decide)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
