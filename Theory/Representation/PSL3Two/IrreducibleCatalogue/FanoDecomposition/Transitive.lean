module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Flags as cosets of a Sylow two-subgroup

The marked flag is e₀ inside the plane v₂ = 0. Its stabilizer is the actual
upper triangular subgroup of SL₃(2), of order eight. Every flag is a translate,
so the orbit map identifies the twenty-one flags with its left cosets.

Source: the set Ω = L/T in Aschbacher–Smith H.6, combined manuscript of
1 March 2004, printed pp.386–387.
-/

@[expose] public section
open Matrix Representation
namespace BinaryLinearThree.FanoDecomposition

/-- The actual flag permutation homomorphism as a group action. -/
instance flagMulAction : MulAction Group Flag := MulAction.compHom Flag flagPerm

@[simp] theorem smul_flag (g : Group) (f : Flag) : g • f = flagPerm g f := rfl

/-- The standard incident point-line pair used by the coordinate parabolics. -/
def markedFlag : Flag :=
  ⟨(Matrix.PSL3Two.flagPoint, Matrix.PSL3Two.flagLine), Matrix.PSL3Two.flag_incident⟩

/-- Equality of translated flags expressed entirely in matrix coordinates. -/
theorem flagPerm_eq_iff (g : Group) (f h : Flag) : flagPerm g f = h ↔
    g.val *ᵥ f.val.1.val = h.val.1.val ∧
      g.val.adjugate.transpose *ᵥ f.val.2.normal.val = h.val.2.normal.val := by
  constructor
  · intro he
    constructor
    · exact congrArg (fun f : Flag => f.val.1.val) he
    · exact congrArg (fun f : Flag => f.val.2.normal.val) he
  · rintro ⟨hp, hl⟩
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext hp
    · exact congrArg Matrix.PSL3Two.Fano.Line.mk (Subtype.ext hl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem markedFlag_reachable : ∀ f : Flag, ∃ g : Group, flagPerm g markedFlag = f := by
  simp only [flagPerm_eq_iff, Matrix.adjugate_fin_three]
  decide +kernel

/-- The actual flag action is transitive. -/
instance flagPretransitive : MulAction.IsPretransitive Group Flag where
  exists_smul_eq f h := by
    obtain ⟨g, hg⟩ := markedFlag_reachable f
    obtain ⟨k, hk⟩ := markedFlag_reachable h
    refine ⟨k * g⁻¹, ?_⟩
    change flagPerm (k * g⁻¹) f = h
    rw [map_mul, Equiv.Perm.mul_apply, ← hg, map_inv,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    exact hk

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem marked_stabilizer_certificate : ∀ g : Group,
    flagPerm g markedFlag = markedFlag ↔ g ∈ Matrix.PSL3Two.borelSL := by
  simp only [flagPerm_eq_iff, Matrix.adjugate_fin_three, Matrix.PSL3Two.mem_borelSL_iff]
  decide +kernel

/-- The stabilizer agrees with the existing concrete upper triangular subgroup. -/
theorem markedFlag_stabilizer :
    MulAction.stabilizer Group markedFlag = Matrix.PSL3Two.borelSL := by
  ext g
  exact marked_stabilizer_certificate g

theorem card_markedFlag_stabilizer : Nat.card (MulAction.stabilizer Group markedFlag) = 8 := by
  rw [markedFlag_stabilizer, Matrix.PSL3Two.card_borelSL]

/-- The marked stabilizer as an actual Sylow two-subgroup of SL₃(2). -/
noncomputable def flagSylow : Sylow 2 Group :=
  Sylow.ofCard (MulAction.stabilizer Group markedFlag) (by
    rw [card_markedFlag_stabilizer, Matrix.PSL3Two.card_SL]
    decide +kernel)

@[simp] theorem flagSylow_coe :
    (flagSylow : Subgroup Group) = MulAction.stabilizer Group markedFlag := rfl

/-- The genuine flag/coset identification given by gT ↦ g·markedFlag. -/
noncomputable def cosetEquiv : Group ⧸ MulAction.stabilizer Group markedFlag ≃ Flag :=
  Equiv.ofBijective (MulAction.ofQuotientStabilizer Group markedFlag)
    ⟨MulAction.injective_ofQuotientStabilizer Group markedFlag, by
      intro f
      obtain ⟨g, hg⟩ := markedFlag_reachable f
      exact ⟨(g : Group ⧸ MulAction.stabilizer Group markedFlag), hg⟩⟩

@[simp] theorem cosetEquiv_apply (g : Group) :
    cosetEquiv (g : Group ⧸ MulAction.stabilizer Group markedFlag) = flagPerm g markedFlag := rfl

/-- Equivariance of the coset identification for the actual left actions. -/
theorem cosetEquiv_smul (g : Group) (q : Group ⧸ MulAction.stabilizer Group markedFlag) :
    cosetEquiv (g • q) = g • cosetEquiv q :=
  MulAction.ofQuotientStabilizer_smul Group markedFlag g q

end BinaryLinearThree.FanoDecomposition
