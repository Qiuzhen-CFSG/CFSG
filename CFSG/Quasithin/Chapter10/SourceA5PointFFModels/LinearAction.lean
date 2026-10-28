module
public import Theory.SpecificGroups.PSL3.FourScalar
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import CFSG.Quasithin.Chapter4.Defs

/-!
# Moving cubics in the actual linear-three FF action

An action equivalence pulls the fixed-point-free central scalar of SL₃(4)
back to the given actor. The same scalar works on any number of repeated
natural summands, including the double-three row of B.5.1. Centrality puts
it in the literal section centralizer of every subgroup. Thus the specified
nonzero vector supplies movement for the original-group torus-lift consumer.

Source: Aschbacher–Smith, B.5.1 and 10.2.9, pp.99–103 and 751–752.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter10
open ChapterB.QuasisimpleSource Chapter4
noncomputable section
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

private theorem center_section (B : Subgroup D) : center D ≤ sectionCentralizer B := by
  apply le_commutatorPreimage (center_le_normalizer _)
  exact (commutator_eq_bot_iff_le_centralizer.mpr (center_le_centralizer _)).le.trans bot_le

private theorem pull_scalar {F : BinaryField} {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) W}
    (e : ActionEquiv ρ σ)
    (x : Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (ho : orderOf x = 3) (hc : x ∈ center _)
    (hm : ∀ w, σ x w = w → w = 0) (B : Subgroup D) {v : V} (hv : v ≠ 0) :
    ∃ y : D, orderOf y = 3 ∧ y ∈ sectionCentralizer B ∧ ρ y v ≠ v := by
  refine ⟨e.groupEquiv.symm x,(e.groupEquiv.symm.orderOf_eq x).trans ho,
    center_section B (centerCongr e.groupEquiv.symm ⟨x,hc⟩).property,?_⟩
  intro hh
  apply hv
  apply e.linearEquiv.injective
  rw [map_zero]
  apply hm
  have hh' := e.intertwines (e.groupEquiv.symm x) v
  rw [hh,e.groupEquiv.apply_symm_apply] at hh'
  exact hh'.symm

theorem source_a5_point_linear_natural_cubic
    {F : BinaryField} (hF : Nat.card F.Carrier = 4)
    (e : ActionEquiv ρ (linearNatural F 3)) (B : Subgroup D)
    {v : V} (hv : v ≠ 0) :
    ∃ x : D, orderOf x = 3 ∧ x ∈ sectionCentralizer B ∧ ρ x v ≠ v := by
  obtain ⟨x,ho,hc,hm⟩ := Theory.SpecificGroups.PSL3.FourScalar.exists_central_cubic_moving hF
  exact pull_scalar e x ho hc hm B hv

theorem source_a5_point_linear_repeated_cubic
    {F : BinaryField} (hF : Nat.card F.Carrier = 4) {r : ℕ}
    (e : ActionEquiv ρ (repeated (linearNatural F 3) r)) (B : Subgroup D)
    {v : V} (hv : v ≠ 0) :
    ∃ x : D, orderOf x = 3 ∧ x ∈ sectionCentralizer B ∧ ρ x v ≠ v := by
  obtain ⟨x,ho,hc,hm⟩ := Theory.SpecificGroups.PSL3.FourScalar.exists_central_cubic_moving hF
  apply pull_scalar e x ho hc _ B hv
  intro w hw
  funext i
  apply hm
  exact congrFun hw i
end
end CFSG.Quasithin.Chapter10
