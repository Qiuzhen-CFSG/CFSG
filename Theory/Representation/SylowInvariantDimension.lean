module
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Invariant dimensions on Sylow subgroups

Restrictions of a representation to any two Sylow p-subgroups of a finite
group have invariant subspaces of equal dimension. The field has arbitrary
characteristic; neither semisimplicity nor finite dimension is assumed.

Sylow conjugacy identifies one subgroup with the conjugate of the other.
The representation operator at the conjugating element carries fixed
vectors to fixed vectors, and the inverse group element gives the inverse
linear map. Thus the actual invariant submodules are linearly equivalent.
This transfers a concrete unipotent fixed-space computation to any Sylow
subgroup in the equality case of ABG II.4 Lemma18.
-/

namespace Representation

open MulAction

variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]

private theorem finrank_invariants_map_conj (ρ : Representation F G V)
    (P : Subgroup G) (g : G) :
    Module.finrank F (invariants (ρ.comp P.subtype)) =
      Module.finrank F (invariants (ρ.comp (P.map (MulAut.conj g).toMonoidHom).subtype)) := by
  let Q := P.map (MulAut.conj g).toMonoidHom
  have hinv (x : V) : ρ g⁻¹ (ρ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (x : V) : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hforward (v : invariants (ρ.comp P.subtype)) :
      ρ g v ∈ invariants (ρ.comp Q.subtype) := by
    intro q
    obtain ⟨a, ha, hqa⟩ := q.property
    have hv : ρ a v = v := v.property ⟨a, ha⟩
    change ρ (q : G) (ρ g v) = ρ g v
    rw [← hqa]
    change ρ (g * a * g⁻¹) (ρ g v) = _
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, hinv, hv]
  have hback (v : invariants (ρ.comp Q.subtype)) :
      ρ g⁻¹ v ∈ invariants (ρ.comp P.subtype) := by
    intro a
    have hmem : g * (a : G) * g⁻¹ ∈ Q := ⟨a, a.property, rfl⟩
    have hv : ρ (g * (a : G) * g⁻¹) v = v := v.property ⟨_, hmem⟩
    change ρ (a : G) (ρ g⁻¹ v) = ρ g⁻¹ v
    have h := congrArg (fun x : V => ρ g⁻¹ x) hv
    rw [map_mul, map_mul] at h
    simpa only [Module.End.mul_apply, hinv] using h
  let e : invariants (ρ.comp P.subtype) ≃ₗ[F] invariants (ρ.comp Q.subtype) :=
    { toFun := fun v => ⟨ρ g v, hforward v⟩
      invFun := fun v => ⟨ρ g⁻¹ v, hback v⟩
      left_inv := fun v => Subtype.ext (hinv v)
      right_inv := fun v => Subtype.ext (hginv v)
      map_add' := fun v w => Subtype.ext (map_add (ρ g) (v : V) (w : V))
      map_smul' := fun c v => Subtype.ext (map_smul (ρ g) c (v : V)) }
  exact e.finrank_eq

public theorem finrank_invariants_sylow_eq [Finite G] (ρ : Representation F G V)
    (p : ℕ) [Fact p.Prime] (P Q : Sylow p G) :
    Module.finrank F (invariants (ρ.comp P.toSubgroup.subtype)) =
      Module.finrank F (invariants (ρ.comp Q.toSubgroup.subtype)) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G P Q
  have he : (MulDistribMulAction.toMonoidEnd (MulAut G) G) (MulAut.conj g) =
      (MulAut.conj g).toMonoidHom := by
    ext x
    rfl
  have hsub : (g • P).toSubgroup = P.toSubgroup.map (MulAut.conj g).toMonoidHom := by
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact congrArg (fun f : G →* G => P.toSubgroup.map f) he
  rw [hsub]
  exact finrank_invariants_map_conj ρ P.toSubgroup g

end Representation
