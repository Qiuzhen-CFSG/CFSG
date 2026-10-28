module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Full generation of the natural point-perpendicular by its residual

In the natural binary six-letter module, the two-residual of a point
stabilizer generates the entire perpendicular by commutators. In addition
to the two cubic displacements, the double transposition (01)(23) moves
v₀₂ by v₄₅. Thus the fixed point itself lies in the commutator subspace.
Permutation transport retains the literal point and its stabilizer.

Source: Aschbacher–Smith, proof of 13.7.5(2), printed p.938,
using the natural module of §B.3, printed pp.83–85.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualGeneration

open BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

private def pairCore (i j : Ω) : core Ω :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib]; decide⟩

private theorem form_pair (i j k l : Ω) :
    form (pairVector i j) (pairVector k l) =
      ∑ a : Ω, ((Pi.single i 1 + Pi.single j 1) : Ω → ZMod 2) a *
        ((Pi.single k 1 + Pi.single l 1) : Ω → ZMod 2) a := by
  exact naturalPairing_apply_core (Fin 6) (pairCore i j) (pairCore k l)

private theorem pair_triangle (i j k : Ω) :
    pairVector i j + pairVector j k = pairVector i k := by
  apply Subtype.ext
  change (constants Ω).mkQ _ + (constants Ω).mkQ _ = (constants Ω).mkQ _
  rw [← map_add]
  congr 1
  ext a
  simp only [Pi.add_apply]
  have h : ∀ x : ZMod 2, x + x = 0 := CharTwo.add_self_eq_zero
  linear_combination h ((Pi.single j 1 : Ω → ZMod 2) a)

private theorem pair_complement (i j k l : Ω)
    (h : (Pi.single i (1 : ZMod 2) + Pi.single j 1) -
      ((Pi.single k 1 + Pi.single l 1) + (Pi.single 4 1 + Pi.single 5 1)) =
        allOne Ω) :
    pairVector i j = pairVector k l + pairVector 4 5 := by
  apply Subtype.ext
  change (constants Ω).mkQ _ = (constants Ω).mkQ _ + (constants Ω).mkQ _
  rw [← map_add]
  apply (Submodule.Quotient.eq (constants Ω)).2
  rw [h]
  exact Submodule.subset_span (by simp)

private theorem pair_perp (i j : Ω)
    (h : form (pairVector 4 5) (pairVector i j) = 0) :
    pairVector i j ∈ form.orthogonal canonicalLine := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  simp [h]

/-- Cubic and double-transposition displacements generate the entire perpendicular. -/
private theorem canonical_displacement :
    form.orthogonal canonicalLine ≤
      subspaceCommutator (naturalRepresentation Ω) (form.orthogonal canonicalLine) K := by
  let W := subspaceCommutator (naturalRepresentation Ω) (form.orthogonal canonicalLine) K
  have h45 : pairVector 4 5 ∈ W := by
    let a : Equiv.Perm Ω := Equiv.swap 0 1 * Equiv.swap 2 3
    have h : naturalRepresentation Ω a (pairVector 0 2) - pairVector 0 2 ∈ W :=
      Submodule.subset_span ⟨a, by decide, pairVector 0 2,
        pair_perp 0 2 (by rw [form_pair]; decide), rfl⟩
    rw [pairVector_map] at h
    change pairVector 1 3 - pairVector 0 2 ∈ W at h
    rw [pair_complement 1 3 0 2 (by ext i; fin_cases i <;> decide),
      ZModModule.sub_eq_add, add_right_comm, ZModModule.add_self, zero_add] at h
    exact h
  have hd (v : V) (hv : v ∈ form.orthogonal canonicalLine) :
      naturalRepresentation Ω cycle012 v - v ∈ W := by
    exact Submodule.subset_span ⟨cycle012, by decide, v, hv, rfl⟩
  have ht : pairVector 0 1 + pairVector 1 2 = pairVector 0 2 := pair_triangle 0 1 2
  have h02 : pairVector 0 2 ∈ W := by
    have h := hd (pairVector 0 1) (pair_perp 0 1 (by rw [form_pair]; decide))
    rw [pairVector_map] at h
    change pairVector 1 2 - pairVector 0 1 ∈ W at h
    simpa only [ZModModule.sub_eq_add, add_comm, ht] using h
  have h12 : pairVector 1 2 ∈ W := by
    have h := hd (pairVector 0 2) (pair_perp 0 2 (by rw [form_pair]; decide))
    rw [pairVector_map] at h
    change pairVector 1 0 - pairVector 0 2 ∈ W at h
    rw [pairVector_comm 1 0, ZModModule.sub_eq_add, ← ht] at h
    simpa only [← add_assoc, ZModModule.add_self, zero_add] using h
  have h01 : pairVector 0 1 ∈ W := by
    have h := W.add_mem h02 h12
    rw [← ht, add_assoc, ZModModule.add_self, add_zero] at h
    exact h
  have h03 : pairVector 0 3 ∈ W := by
    rw [pair_complement 0 3 1 2 (by ext a; fin_cases a <;> decide)]
    exact W.add_mem h12 h45
  have h13 : pairVector 1 3 ∈ W := by
    rw [pair_complement 1 3 0 2 (by ext a; fin_cases a <;> decide)]
    exact W.add_mem h02 h45
  have h23 : pairVector 2 3 ∈ W := by
    rw [pair_complement 2 3 0 1 (by ext a; fin_cases a <;> decide)]
    exact W.add_mem h01 h45
  intro v hv
  rcases vector_cases v with rfl | ⟨⟨⟨i,j⟩, hij⟩, rfl⟩
  · exact W.zero_mem
  have h := hv (pairVector 4 5) (Submodule.subset_span (by simp))
  change form (pairVector 4 5) (pairVector i j) = 0 at h
  rw [form_pair] at h
  change pairVector i j ∈ W
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals first
    | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23 | exact h45
    | exact False.elim ((of_decide_eq_false rfl) h)

private def duadMover (d : NaturalGeometry.Duad) : Equiv.Perm Ω :=
  Equiv.swap ((Equiv.swap 4 d.val.1) 5) d.val.2 * Equiv.swap 4 d.val.1

set_option maxRecDepth 4096 in
private theorem duadMover_apply : ∀ d : NaturalGeometry.Duad,
    duadMover d 4 = d.val.1 ∧ duadMover d 5 = d.val.2 := by decide

private theorem line_is_image (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) :
    ∃ g : Equiv.Perm Ω, canonicalLine.map (naturalRepresentation Ω g) = P := by
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hP
    contradiction
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff P).mp hP0
  obtain ⟨d, rfl⟩ := (vector_cases v).resolve_left hv0
  refine ⟨duadMover d, ?_⟩
  rw [canonicalLine, Submodule.map_span, Set.image_singleton, pairVector_map,
    (duadMover_apply d).1, (duadMover_apply d).2]
  exact (eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0).symm

private theorem orthogonal_map (g : Equiv.Perm Ω) (P : Submodule (ZMod 2) V) :
    (form.orthogonal P).map (naturalRepresentation Ω g) =
      form.orthogonal (P.map (naturalRepresentation Ω g)) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [form_invariant]
    exact hv w hw
  · have hfin (D : Submodule (ZMod 2) V) :
        Module.finrank (ZMod 2) (D.map (naturalRepresentation Ω g)) =
          Module.finrank (ZMod 2) D :=
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((naturalRepresentation Ω).asGroupHom g)).finrank_map_eq D
    rw [hfin, LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      LinearMap.BilinForm.finrank_orthogonal form_nondegenerate, hfin]

private theorem conjugate_stabilizes (g : Equiv.Perm Ω) (h : L1) :
    g * h.val * g⁻¹ ∈ subspaceStabilizer (naturalRepresentation Ω)
      (canonicalLine.map (naturalRepresentation Ω g)) := by
  apply (mem_stabilizer_iff_map _ _).mpr
  have hh := canonicalLine_map_of_mem h.property.1
  simp only [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  rw [← Submodule.map_comp (naturalRepresentation Ω g) (naturalRepresentation Ω g⁻¹),
    ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_eq_id, Submodule.map_id, hh]

/-- Transport the actual residual of `L1`, using only the alternating containment in `S`. -/
private theorem conjugate_K_le_residual (S : Subgroup (Equiv.Perm Ω))
    (hS : alternatingGroup Ω ≤ S) (g : Equiv.Perm Ω) :
    K.map (MulAut.conj g).toMonoidHom ≤
      (pResidual 2 (S ⊓ subspaceStabilizer (naturalRepresentation Ω)
        (canonicalLine.map (naturalRepresentation Ω g)) : Subgroup (Equiv.Perm Ω))).map
          (S ⊓ subspaceStabilizer (naturalRepresentation Ω)
            (canonicalLine.map (naturalRepresentation Ω g))).subtype := by
  let M := S ⊓ subspaceStabilizer (naturalRepresentation Ω)
    (canonicalLine.map (naturalRepresentation Ω g))
  let f : L1 →* M := ((MulAut.conj g).toMonoidHom.comp L1.subtype).codRestrict M (by
    intro h
    refine ⟨hS ?_, conjugate_stabilizes g h⟩
    change Equiv.Perm.sign (g * h.val * g⁻¹) = 1
    have hh : Equiv.Perm.sign h.val = 1 := h.property.2
    simp only [map_mul, map_inv, hh, mul_one, mul_inv_cancel])
  rintro _ ⟨k, hk, rfl⟩
  rw [← residual_L1] at hk
  obtain ⟨x, hx, rfl⟩ := hk
  exact ⟨f x, Subgroup.map_pResidual_le 2 f ⟨x, hx, rfl⟩, rfl⟩

private theorem displacement_map_le (g : Equiv.Perm Ω) (D : Submodule (ZMod 2) V)
    (A : Subgroup (Equiv.Perm Ω)) :
    (subspaceCommutator (naturalRepresentation Ω) D A).map (naturalRepresentation Ω g) ≤
      subspaceCommutator (naturalRepresentation Ω) (D.map (naturalRepresentation Ω g))
        (A.map (MulAut.conj g).toMonoidHom) := by
  rw [subspaceCommutator, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨a, ha, w, hw, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨g * a * g⁻¹, ⟨a, ha, rfl⟩, naturalRepresentation Ω g w,
    Submodule.mem_map_of_mem hw, ?_⟩
  rw [map_sub]
  congr 1
  simp only [map_mul, Module.End.mul_apply]
  rw [← Module.End.mul_apply (naturalRepresentation Ω g⁻¹), ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply]

private theorem displacement_mono (D : Submodule (ZMod 2) V)
    {A B : Subgroup (Equiv.Perm Ω)} (hAB : A ≤ B) :
    subspaceCommutator (naturalRepresentation Ω) D A ≤
      subspaceCommutator (naturalRepresentation Ω) D B := by
  apply Submodule.span_mono
  rintro v ⟨a, ha, w, hw, hv⟩
  exact ⟨a, hAB ha, w, hw, hv⟩

/-- For every line in the natural augmentation quotient, the point stabilizer's
actual two-residual generates the entire perpendicular. -/
theorem point_residual_generates (S : Subgroup (Equiv.Perm (Fin 6)))
    (hS : alternatingGroup (Fin 6) ≤ S)
    (P : Submodule (ZMod 2) (natural (Fin 6)))
    (hP : Module.finrank (ZMod 2) P = 1) :
    let M := S ⊓ subspaceStabilizer (naturalRepresentation (Fin 6)) P
    let R := (pResidual 2 M).map M.subtype
    form.orthogonal P ≤
      subspaceCommutator (naturalRepresentation (Fin 6)) (form.orthogonal P) R := by
  obtain ⟨g, rfl⟩ := line_is_image P hP
  dsimp only
  rw [← orthogonal_map]
  have h := Submodule.map_mono (f := naturalRepresentation Ω g) canonical_displacement
  refine h.trans ?_
  exact (displacement_map_le g _ K).trans
    (displacement_mono _ (conjugate_K_le_residual S hS g))
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualGeneration
