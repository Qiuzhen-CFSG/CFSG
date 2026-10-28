module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Geometry
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Passing the original actor to the automorphisms of a square

Distinct commuting components have trivial intersection when the first is
centerless. Their actual multiplication map then identifies their join
with a direct product. Quasiequivalence supplies the isomorphism between
the factors, so the irreducible action embeds the elementary actor into
`Aut(L × L)` without assuming that it normalizes either factor separately.

The automorphism rank of the square and the model-specific component bound
remain explicit inputs to the last lemma. These are group-theoretic
obligations, not conclusions of this module.

Source: Aschbacher--Smith, G.9.3, printed p.356.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents

open Subgroup Theory.GroupTheory

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L L₂ H : Subgroup G} {m : ℕ}

omit [Finite G] in
/-- Centerlessness makes the commuting component product a direct product. -/
theorem component_pair_disjoint_of_center_eq_bot
    (hL : IsComponent G L) (hL₂ : IsComponent G L₂) (hne : L ≠ L₂)
    (hZ : center L = ⊥) : Disjoint L L₂ := by
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (hL.commutator_eq_bot_of_ne hL₂ hne)
  apply disjoint_def.mpr
  intro x hx hx₂
  have hz : (⟨x, hx⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hc y.property) x hx₂).symm
  exact congrArg (fun y : L => (y : G)) (mem_bot.mp (hZ ▸ hz))

/-- The actor may permute the factors; it still embeds in the automorphism
group of their square. The source's quasiequivalence supplies `e`. -/
theorem actor_rank_le_square_automorphisms
    (h : ComponentHypothesis K ρ A L H m)
    (hL₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (e : L ≃* L₂) (hZ : center L = ⊥) :
    m ≤ primeRank 2 (MulAut (L × L)) := by
  have hc := h.component.commutator_eq_bot_of_ne hL₂ hne
  let ep : (L × L) ≃* H :=
    ((MulEquiv.prodCongr (MulEquiv.refl L) e).trans
      (productEquiv hc (component_pair_disjoint_of_center_eq_bot h.component hL₂ hne hZ))).trans
      (MulEquiv.subgroupCongr hH.symm)
  have hr := actor_rank_le_join_automorphisms h
  rw [← primeRank_equiv 2 (MulAut.congr ep)] at hr
  exact hr

/-- Applying the two independent automorphism estimates retains the original
actor, even when the source proof chooses a larger one inside the join. -/
theorem actor_rank_bound_of_square_bound
    (h : ComponentHypothesis K ρ A L H m)
    (hL₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (e : L ≃* L₂) (hZ : center L = ⊥)
    (hsquare : primeRank 2 (MulAut (L × L)) ≤ 2 * primeRank 2 (MulAut L))
    (hfactor : primeRank 2 (MulAut L) ≤ primeRank 2 L) :
    m ≤ 2 * primeRank 2 L :=
  (actor_rank_le_square_automorphisms h hL₂ hH hne e hZ).trans
    (hsquare.trans (Nat.mul_le_mul_left 2 hfactor))

end CFSG.Quasithin.ChapterG.Section09.TwoComponents
