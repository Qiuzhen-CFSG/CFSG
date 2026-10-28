module
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Normality of a centerless component with large prime rank

Distinct conjugate components commute. A centerless subgroup in the component
and its conjugate then intersect trivially, so their generated subgroup has
twice the witness subgroup's prime rank. A strict ambient rank bound forces
every component conjugate to coincide with the original component.

Source: the commuting-component theorem, GLS vol.2, Theorem 3.5; applied to
the invariant-component step in Aschbacher–Smith E.6.8, printed p.247.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem IsComponent.normal_of_centerless_subgroup_of_primeRank {L A : Subgroup G}
    (hL : IsComponent G L) (hAL : A ≤ L) (hZ : center A = ⊥) (p : ℕ) [Fact p.Prime]
    (hr : primeRank p G < 2 * primeRank p A) : L.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  have hcL : L ≤ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (hL.commutator_eq_bot_of_ne (hL.map_conj g) (Ne.symm hne))
  have hc : A ≤ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) :=
    hAL.trans (hcL.trans (centralizer_le (map_mono hAL)))
  have hd : Disjoint A (A.map (MulAut.conj g).toMonoidHom) := by
    apply disjoint_def.mpr
    intro x hx hy
    have hz : (⟨x, hx⟩ : A) ∈ center A := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hc y.property x hy).symm
    have hx1 : (⟨x, hx⟩ : A) = 1 := mem_bot.mp (hZ ▸ hz)
    exact congrArg (fun y : A => (y : G)) hx1
  have he := A.primeRank_sup_eq_add_of_disjoint_commuting
    (A.map (MulAut.conj g).toMonoidHom) hd hc p
  have hconj : primeRank p A = primeRank p (A.map (MulAut.conj g).toMonoidHom) :=
    primeRank_equiv p ((MulAut.conj g).subgroupMap A)
  rw [← hconj] at he
  have hb := primeRank_le_of_injective p
    (A ⊔ A.map (MulAut.conj g).toMonoidHom).subtype Subtype.val_injective
  rw [he] at hb
  omega

/-- The component itself may supply the centerless rank witness. -/
theorem IsComponent.normal_of_centerless_of_primeRank {L : Subgroup G}
    (hL : IsComponent G L) (hZ : center L = ⊥) (p : ℕ) [Fact p.Prime]
    (hr : primeRank p G < 2 * primeRank p L) : L.Normal :=
  hL.normal_of_centerless_subgroup_of_primeRank le_rfl hZ p hr

end Theory.GroupTheory
