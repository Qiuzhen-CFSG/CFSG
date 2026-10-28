module
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.InvolutionBound
public import Theory.Representation.BinaryOffender.PerfectMoved
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Dimension of the whole moved module of a binary SL₃(2) subgroup

Restrict to the literal displacement subspace of a perfect factor and
identify its full commutator span. Transport the three-involution dimension
bound through a marking of that factor, and compare its involution
displacement with the original ambient representation. No semisimplicity
or irreducibility of the ambient module is assumed.

Source application: Aschbacher--Smith 13.1.9, printed p.871, lifting the
nine-dimensional tensor chief section to the whole moved module.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree
variable {Q V : Type*} [_root_.Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Three conjugate involutions bound the whole moved module of an original
SL₃(2) subgroup, without a semisimplicity or irreducibility hypothesis. -/
theorem moved_finrank_le_three_mul_fixedCodim
    (ρ : Representation (ZMod 2) Q V) (K : Subgroup Q)
    (e : K ≃* Matrix.PSL3Two.SL) (a : K) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K) ≤
      3 * fixedCodim ρ (zpowers (a : Q)) := by
  let U := subspaceCommutator ρ ⊤ K
  let I : Subrepresentation (ρ.comp K.subtype) :=
    ⟨U,fun k v hv => (subspaceCommutator_invariant ρ ⊤ K k.property v).2 hv⟩
  let σ := I.toRepresentation.comp e.symm.toMonoidHom
  let : _root_.Group.IsPerfect Matrix.PSL3Two.SL := Atlas.sl_perfect 3 (by decide)
  let : _root_.Group.IsPerfect K := _root_.Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hfull : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    change subspaceCommutator (I.toRepresentation.comp e.symm.toMonoidHom) ⊤ ⊤ = ⊤
    rw [subspaceCommutator_comp_map,map_top_of_surjective _ e.symm.surjective]
    apply Submodule.map_injective_of_injective U.subtype_injective
    have hh := subspaceCommutator_map_embedding (ρ.comp K.subtype) I.toRepresentation
      (MonoidHom.id K) U.subtype (fun _ _ => rfl) ⊤ ⊤
    rw [Subgroup.map_id,Submodule.map_top,Submodule.range_subtype] at hh
    rw [←hh,Submodule.map_top,Submodule.range_subtype,subspaceCommutator_comp_map,
      ←MonoidHom.range_eq_map,range_subtype]
    exact subspaceCommutator_idempotent_of_perfect ρ K
  have hb := ResidualFFForms.ConstituentBudget.finrank_le_three_mul_involution_fixedCodim
    σ hfull (e a) (by rw [←map_pow,ha,map_one]) (by simpa using hne)
  have hcod : fixedCodim σ (zpowers (e a)) ≤ fixedCodim ρ (zpowers (a : Q)) := by
    have hI := fixedCodim_subrepresentation_le (ρ.comp K.subtype) I (zpowers a)
    have heq : fixedCodim σ (zpowers (e a)) = fixedCodim I.toRepresentation (zpowers a) := by
      unfold fixedCodim
      rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
      change fixedCodim I.toRepresentation (zpowers (e.symm (e a))) = _
      rw [e.symm_apply_apply]
      rfl
    have heq' : fixedCodim (ρ.comp K.subtype) (zpowers a) =
        fixedCodim ρ (zpowers (a : Q)) := by
      unfold fixedCodim
      rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
      rfl
    exact heq.le.trans (hI.trans_eq heq')
  exact hb.trans (Nat.mul_le_mul_left 3 hcod)
end BinaryLinearThree
