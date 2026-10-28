module
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralMovingLayer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualCubicIndex
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralChiefCount

/-!
# The alternating-four residual at a radius-one endpoint

A noncentral binary chief layer inside Ω₁(Z(O₂(H))) forces the actual
two-residual to be A₄ when the complete noncentral chief count is at most
one. The generic central-layer estimate bounds the cubic commutator, and
the existing small-residual theorem gives C₃ or A₄. A cubic residual would
centralize the normal two-subgroup W, contradicting its specified action.

The endpoint application uses the literal stabilizer and chief bound of
the original track. Constructing the moving W from the central labels is
the remaining geometric premise of that application.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.5),
printed p.398, final paragraph, followed by the (4.2) alternative.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {H : Type*} [Group H] [Finite H]

/-- The central elementary source layer excludes the cubic residual and
recognizes the literal two-residual as A₄. -/
theorem residual_alternatingFour_of_central_noncentral_chief
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (s : ChiefSeries H) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (hc : s.noncentralTwoCount ≤ 1)
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (hWQ : W ≤ pCore 2 H) (hWcentral : W ≤ centralizer (pCore 2 H : Set H))
    (hw : ⁅W, pResidual 2 H⁆ ≠ ⊥) :
    Nonempty ((pResidual 2 H) ≃* alternatingGroup (Fin 4)) := by
  have hthree : 3 ∣ Nat.card H := by
    rw [SymmetricThreeTwoCore.card_eq e]
    exact dvd_mul_of_dvd_left (by decide : 3 ∣ 6) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 hthree
  have hX : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hsmall := NoncentralChiefRefinement.central_cubic_commutator_card_le_four
    e s h0 h1 hc W hWQ hWcentral hw (zpowers x) hX
  rcases residual_cubic_or_alternatingFour_of_small_cubic_commutator e x hx hsmall with hR | hR
  · obtain ⟨j⟩ := hR
    have hRcard : Nat.card (pResidual 2 H) = 3 := by
      rw [Nat.card_congr j.toEquiv]
      simp
    have hWtwo : IsPGroup 2 W := pCore_isPGroup.to_le hWQ
    obtain ⟨n, hn⟩ := hWtwo.exists_card_eq
    have hcop : Nat.Coprime (Nat.card W) (Nat.card (pResidual 2 H)) := by
      rw [hn, hRcard]
      exact (by decide : Nat.Coprime 2 3).pow_left n
    exact (hw (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hcop))).elim
  · exact hR

open SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The radius-one right endpoint in the original track has alternating-four
two-residual once its actual central elementary layer is moved. -/
theorem CubicTreeAction.centralInterval_right_residual_alternatingFour
    (h : CubicTreeAction F) (t : Track (RankTwo.graph F) G)
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z)
    (e : ((RankTwo.stabilizer F (t.vertex d.fixedRight)) ⧸
      pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight))) ≃* Equiv.Perm (Fin 3))
    (hself : centralizer (pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight)) : Set _) ≤
      pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight)))
    (hr : d.rightMargin = 1)
    (W : Subgroup (RankTwo.stabilizer F (t.vertex d.fixedRight)))
    [W.Normal] [IsElementaryAbelian 2 W]
    (hWQ : W ≤ pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight)))
    (hWcentral : W ≤ centralizer
      (pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight)) : Set _))
    (hw : ⁅W, pResidual 2 (RankTwo.stabilizer F (t.vertex d.fixedRight))⁆ ≠ ⊥) :
    Nonempty ((pResidual 2 (RankTwo.stabilizer F (t.vertex d.fixedRight))) ≃*
      alternatingGroup (Fin 4)) := by
  let : ∀ i, Finite (F i) := h.finite
  obtain ⟨s, h0, h1⟩ := exists_chiefSeries
    (⊥ : NormalNode (RankTwo.stabilizer F (t.vertex d.fixedRight))) ⊤ bot_le
  have hc := (h.centralInterval_right_chiefBounds t hz d e hself).1 s h0 h1
  rw [hr] at hc
  exact residual_alternatingFour_of_central_noncentral_chief
    e s h0 h1 hc W hWQ hWcentral hw

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
