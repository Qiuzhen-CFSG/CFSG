module

public import Theory.Mathieu.M22.Properties.Order
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Index

/-!
# The degree-100 permutation geometry in Higman--Sims recognition

This is the intermediate permutation-group statement in the type-HS
recognition argument: a transitive faithful action of degree 100, with an
actual M₂₂ point stabilizer and three suborbits, one of length 22. The
permutation subgroup is arbitrary; no identification with HS is included.

The construction from the two local subgroups and the uniqueness of the
resulting permutation group are independent mathematical steps. Their
assembly belongs to `qt-i48-hs-recognition`. This module asserts neither step.

Source: Aschbacher--Smith, I.4.8, printed p.418, and its discussion of the
rank-three characterization and Wales's uniqueness theorem; Aschbacher,
"A 2-local characterization of the Higman--Sims group", J. Algebra 260
(2003), 16--32, DOI 10.1016/S0021-8693(02)00619-1.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS
open MulAction

/-- Intrinsic permutation geometry, with the actual Mathieu carrier. -/
structure RankThreeData (P : Subgroup (Equiv.Perm (Fin 100))) : Prop where
  transitive : IsPretransitive P (Fin 100)
  stabilizer_model : Nonempty ((stabilizer P (0 : Fin 100)) ≃* Sporadic.Mathieu.M22)
  rank_three : Nat.card (orbitRel.Quotient (stabilizer P (0 : Fin 100)) (Fin 100)) = 3
  subdegree_twenty_two : ∃ x : Fin 100,
    Nat.card (orbit (stabilizer P (0 : Fin 100)) x) = 22

/-- A faithful realization of an arbitrary group in the degree-100 geometry.
The range is not assumed to equal any specified permutation subgroup. -/
def HasRankThreeAction (G : Type*) [Group G] : Prop :=
  ∃ f : G →* Equiv.Perm (Fin 100), Function.Injective f ∧ RankThreeData f.range

/-- Orbit--stabilizer computes the order once the geometric construction is supplied. -/
theorem RankThreeData.card {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : Nat.card P = 44352000 := by
  let := h.transitive
  obtain ⟨e⟩ := h.stabilizer_model
  have hc : Nat.card (stabilizer P (0 : Fin 100)) = 443520 :=
    (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m22_order
  have he := (stabilizer P (0 : Fin 100)).index_mul_card
  rw [index_stabilizer_of_transitive, Nat.card_fin, hc] at he
  omega

/-- Faithfulness transfers the permutation-group order to the original group. -/
theorem HasRankThreeAction.card {G : Type*} [Group G]
    (h : HasRankThreeAction G) : Nat.card G = 44352000 := by
  obtain ⟨f, hf, hP⟩ := h
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).trans hP.card

end Sporadic.LeechRelated.HS
