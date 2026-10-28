module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.Reduction
public import Theory.Mathieu.M12.Properties.Transitivity

/-!
# The fixed-vector branch of the M₁₂ restriction argument

A vector fixed by the literal M₁₁ point subgroup gives an equivariant map
from the twelve-point permutation module by orbit transport. Irreducibility
makes a nonzero map surjective. In dimension greater than one its restriction
to the augmentation core is still surjective and kills the constant line.
Consequently the target has dimension at most ten.

The point embedding, stabilizer identification and inverse-permutation action
are the existing native ones. This branch requires no degree window.
Source context: James, J. Algebra 27 (1973), 57–111; the ordinary module input
to Aschbacher–Smith Chapter K, printed pp.451 and 457.
-/

public section
namespace Representation.MathieuSmall.M12DegreeGap
open Sporadic.Mathieu M12Recognition BinaryPermutation
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem finrank_le_ten_of_permutation_quotient
    (ρ : Representation (ZMod 2) M12 V) [ρ.IsIrreducible]
    (hd : 1 < Module.finrank (ZMod 2) V)
    (f : Representation.IntertwiningMap ((representation (Fin 12)).comp M12.subtype) ρ)
    (hf : f ≠ 0) : Module.finrank (ZMod 2) V ≤ 10 := by
  let perm : Representation (ZMod 2) M12 (Full (Fin 12)) :=
    (representation (Fin 12)).comp M12.subtype
  let coreR : Representation (ZMod 2) M12 (core (Fin 12)) :=
    (coreRepresentation (Fin 12)).comp M12.subtype
  let j : coreR.IntertwiningMap perm := ⟨(core (Fin 12)).subtype, fun _ => rfl⟩
  let fc := f.comp j
  have hs := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  have hr := f.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, finrank_full, Fintype.card_fin] at hr
  have hfc : fc ≠ 0 := by
    intro hz
    have hle : core (Fin 12) ≤ LinearMap.ker f.toLinearMap := by
      intro v hv
      exact congrArg (fun k : coreR.IntertwiningMap ρ => k ⟨v, hv⟩) hz
    have hdim := Submodule.finrank_mono hle
    rw [finrank_core, Fintype.card_fin] at hdim
    omega
  have hsc := (IsIrreducible.surjective_or_eq_zero fc).resolve_right hfc
  let C : Subrepresentation perm :=
    ⟨constants (Fin 12), fun g _ hv => constants_invariant _ g.val hv⟩
  let c : C.toRepresentation.IntertwiningMap perm := ⟨C.toSubmodule.subtype, fun _ => rfl⟩
  have hc : f.comp c = 0 := by
    rcases IsIrreducible.surjective_or_eq_zero (f.comp c) with hs | hz
    · have hh := LinearMap.finrank_le_finrank_of_surjective hs
      change Module.finrank (ZMod 2) V ≤ Module.finrank (ZMod 2) (constants (Fin 12)) at hh
      rw [finrank_constants] at hh
      omega
    · exact hz
  have hone : allOne (Fin 12) ∈ core (Fin 12) := by
    change augmentation (Fin 12) (allOne (Fin 12)) = 0
    rw [augmentation_allOne]
    decide
  let u : core (Fin 12) := ⟨allOne (Fin 12), hone⟩
  have hu : u ≠ 0 := fun h => allOne_ne_zero (Fin 12) (congrArg Subtype.val h)
  have huk : u ∈ LinearMap.ker fc.toLinearMap := by
    exact congrArg (fun k : C.toRepresentation.IntertwiningMap ρ =>
      k ⟨allOne (Fin 12), Submodule.subset_span (Set.mem_singleton _)⟩) hc
  have hkpos : 0 < Module.finrank (ZMod 2) (LinearMap.ker fc.toLinearMap) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have he := Submodule.finrank_eq_zero.mp hz
    have : u = 0 := by simpa only [he, Submodule.mem_bot] using huk
    exact hu this
  have hrc := fc.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsc, finrank_top] at hrc
  change Module.finrank (ZMod 2) V + _ = Module.finrank (ZMod 2) (core (Fin 12)) at hrc
  rw [finrank_core, Fintype.card_fin] at hrc
  omega

theorem finrank_le_ten_of_point_fixed
    (ρ : Representation (ZMod 2) M12 V) [ρ.IsIrreducible]
    (hd : 1 < Module.finrank (ZMod 2) V)
    (hfixed : Representation.invariants (ρ.comp pointEmbedding) ≠ ⊥) :
    Module.finrank (ZMod 2) V ≤ 10 := by
  classical
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfixed
  have hsurj : Function.Surjective m11ToM12PointStabilizer :=
    (m11ToM12PointStabilizer_injective.bijective_of_nat_card_le
      (Nat.card_congr m11EquivM12PointStabilizer.toEquiv).ge).surjective
  have hstab (g : M12) (hg : g ∈ MulAction.stabilizer M12 (12 : Fin 12)) : ρ g v = v := by
    obtain ⟨x, hx⟩ := hsurj ⟨g, hg⟩
    have he : pointEmbedding x = g := congrArg Subtype.val hx
    simpa only [MonoidHom.comp_apply, he] using hv x
  have htrans (i : Fin 12) : ∃ g : M12, g • (12 : Fin 12) = i :=
    MulAction.exists_smul_eq M12 12 i
  let lift (i : Fin 12) : M12 := Classical.choose (htrans i)
  have hlift (i : Fin 12) : lift i • (12 : Fin 12) = i := Classical.choose_spec (htrans i)
  let value (i : Fin 12) : V := ρ (lift i) v
  have hvalue (g : M12) (i : Fin 12) (hg : g • (12 : Fin 12) = i) : value i = ρ g v := by
    have hm : (lift i)⁻¹ * g ∈ MulAction.stabilizer M12 (12 : Fin 12) := by
      change ((lift i)⁻¹ * g) • (12 : Fin 12) = 12
      rw [mul_smul, hg]
      exact (congrArg (fun j => (lift i)⁻¹ • j) (hlift i).symm).trans (inv_smul_smul _ _)
    have he := congrArg (ρ (lift i)) (hstab _ hm)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
    exact he.symm
  have hvalue_o : value 12 = v := by simpa using hvalue 1 12 (one_smul _ _)
  have hvalue_act (g : M12) (i : Fin 12) : value (g • i) = ρ g (value i) := by
    rw [hvalue (g * lift i) _ (by rw [mul_smul, hlift]), map_mul]
    rfl
  let perm : Representation (ZMod 2) M12 (Full (Fin 12)) :=
    (representation (Fin 12)).comp M12.subtype
  let f : perm.IntertwiningMap ρ := {
    toLinearMap := {
      toFun a := ∑ i : Fin 12, a i • value i
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ i : Fin 12, a (g.val.symm i) • value i) = ρ g (∑ i : Fin 12, a i • value i)
      rw [map_sum]
      simp only [map_smul, ← hvalue_act]
      exact (Equiv.sum_comp g.val (fun i => a (g.val.symm i) • value i)).symm.trans (by
        simp only [_root_.Equiv.symm_apply_apply, MulAction.subgroup_smul_def, Equiv.Perm.smul_def]) }
  have hf : f (Pi.single 12 1) = v := by
    change (∑ i : Fin 12, (Pi.single 12 (1 : ZMod 2) : Fin 12 → ZMod 2) i • value i) = v
    calc
      _ = value (12 : Fin 12) := by simp
      _ = v := hvalue_o
  apply finrank_le_ten_of_permutation_quotient ρ hd f
  intro hz
  exact hv0 (hf.symm.trans (congrArg (fun k : perm.IntertwiningMap ρ => k (Pi.single 12 1)) hz))

end Representation.MathieuSmall.M12DegreeGap
