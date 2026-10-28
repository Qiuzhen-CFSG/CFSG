module

public import Theory.Representation.PSL3Two.SteinbergStructure.LocalActions.Coordinates
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.Transitive
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Sylow fixed vectors and parabolic commutators on the Steinberg module

For the marked flag Sylow, the unique nonzero fixed vector is E₀₂ and its
full group stabilizer is precisely that Sylow subgroup. Sylow conjugacy
transports both assertions to every Sylow two-subgroup. Explicit displacement
certificates for the eight adjoint coordinates prove that each marked
parabolic has full commutator space; conjugation gives the same result for
all their conjugates.

Source: Aschbacher–Smith H.6.3(4–5), printed pp.387–388, combined manuscript
of 1 March 2004. The stabilizer is C_L(m), as in the source proof; the printed
C_M(m) in the statement is a typo. All actions and commutators here are those
of the literal trace-zero representation `BinaryLinearThree.S`.
-/

open Matrix Representation
open BinaryLinearThree.IrreducibleCatalogue
open Matrix.PSL3Two Representation.BinaryOffender
namespace BinaryLinearThree.SteinbergStructure.LocalActions
public noncomputable section
open scoped Pointwise

private theorem action_conj (g h : Group) (v : Steinberg) :
    S (g * h * g⁻¹) (S g v) = S g (S h v) := by
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]

private theorem conjugate_fixed_iff (H : Subgroup Group) (g : Group) (v : Steinberg) :
    (∀ h ∈ H.map (MulAut.conj g).toMonoidHom, S h (S g v) = S g v) ↔
      ∀ h ∈ H, S h v = v := by
  constructor
  · intro h a ha
    have hf := h (g * a * g⁻¹) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    rw [action_conj] at hf
    exact (S.apply_bijective g).injective hf
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    change S (g * b * g⁻¹) (S g v) = _
    rw [action_conj, h b hb]

private theorem conjugate_stabilizer_iff (H : Subgroup Group) (g : Group) (v : Steinberg)
    (hv : ∀ h, S h v = v ↔ h ∈ H) (h : Group) :
    S h (S g v) = S g v ↔ h ∈ H.map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro hf
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * h * g, (hv _).mp ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have he := congrArg (S g⁻¹) hf
    simpa only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] using he
  · intro hh
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hh
    change S (g * a * g⁻¹) (S g v) = _
    rw [action_conj, (hv a).mpr ha]

private theorem full_commutator_conjugate (H : Subgroup Group) (g : Group)
    (hH : subspaceCommutator S ⊤ H = ⊤) :
    subspaceCommutator S ⊤ (H.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  apply top_unique
  intro v _
  have hv : S g⁻¹ v ∈ subspaceCommutator S ⊤ H := by rw [hH]; trivial
  have ht : ∀ w ∈ subspaceCommutator S ⊤ H,
      S g w ∈ subspaceCommutator S ⊤ (H.map (MulAut.conj g).toMonoidHom) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, u, _, rfl⟩ := hw
      rw [map_sub]
      apply Submodule.subset_span
      refine ⟨g * a * g⁻¹, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩,
        S g u, Submodule.mem_top, ?_⟩
      rw [action_conj]
    | zero => simp
    | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa using Submodule.smul_mem _ c ha
  simpa only [Representation.self_inv_apply] using ht _ hv

private theorem commutator_eq_top_of_basis_displacements (H : Subgroup Group)
    (hdisp : ∀ i : Fin 8, ∃ g ∈ H, ∃ v : Steinberg,
      S g v - v = coordinates.symm (Pi.single i 1)) :
    subspaceCommutator S ⊤ H = ⊤ := by
  have hb (i : Fin 8) : coordinates.symm (Pi.single i 1) ∈ subspaceCommutator S ⊤ H := by
    obtain ⟨g, hg, v, hv⟩ := hdisp i
    exact Submodule.subset_span ⟨g, hg, v, Submodule.mem_top, hv.symm⟩
  apply top_unique
  intro v _
  have he : v = ∑ i, (coordinates v i) • coordinates.symm (Pi.single i 1) := by
    simpa only [LinearEquiv.symm_apply_apply, map_sum, map_smul] using
      congrArg coordinates.symm (pi_eq_sum_univ' (coordinates v))
  rw [he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)

/-- H.6.3(5): the marked point parabolic generates the whole commutator space. -/
theorem point_commutator_eq_top : subspaceCommutator S ⊤ pointParabolicSL = ⊤ :=
  commutator_eq_top_of_basis_displacements _ point_basis_displacement

/-- H.6.3(5): the marked line parabolic generates the whole commutator space. -/
theorem line_commutator_eq_top : subspaceCommutator S ⊤ lineParabolicSL = ⊤ :=
  commutator_eq_top_of_basis_displacements _ line_basis_displacement

/-- H.6.3(4): the unique nonzero Sylow-fixed vector and its full group stabilizer. -/
theorem sylow_fixedVector (T : Sylow 2 Group) :
    ∃ m : Steinberg, m ≠ 0 ∧ (∀ g : Group, S g m = m ↔ g ∈ T) ∧
      ∀ n : Steinberg, n ≠ 0 → (∀ g ∈ T, S g n = n) → n = m := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Group FanoDecomposition.flagSylow T
  have hT : ((g • FanoDecomposition.flagSylow : Sylow 2 Group) : Subgroup Group) =
      borelSL.map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, FanoDecomposition.flagSylow_coe,
      FanoDecomposition.markedFlag_stabilizer]
    rfl
  refine ⟨S g rootVector, ?_, ?_, ?_⟩
  · intro hz
    exact rootVector_ne_zero ((S.apply_bijective g).injective (by simpa using hz))
  · intro h
    change S h (S g rootVector) = S g rootVector ↔ h ∈
      ((g • FanoDecomposition.flagSylow : Sylow 2 Group) : Subgroup Group)
    rw [hT]
    exact conjugate_stabilizer_iff borelSL g rootVector rootVector_stabilizer h
  · intro n hn hf
    have hfn : ∀ a ∈ borelSL, S a (S g⁻¹ n) = S g⁻¹ n := by
      apply (conjugate_fixed_iff borelSL g (S g⁻¹ n)).mp
      intro a ha
      have hat : a ∈ (g • FanoDecomposition.flagSylow : Sylow 2 Group) := by
        change a ∈ ((g • FanoDecomposition.flagSylow : Sylow 2 Group) : Subgroup Group)
        rw [hT]
        exact ha
      simpa only [Representation.self_inv_apply] using hf a hat
    rcases (borel_fixed_iff _).mp hfn with hz | hr
    · exact (hn ((S.apply_bijective g⁻¹).injective (by simpa using hz))).elim
    · simpa only [Representation.self_inv_apply] using congrArg (S g) hr

/-- Every Sylow two-subgroup fixes exactly one nonzero Steinberg vector. -/
theorem sylow_existsUnique_nonzero_fixed (T : Sylow 2 Group) :
    ∃! m : Steinberg, m ≠ 0 ∧ ∀ g ∈ T, S g m = m := by
  obtain ⟨m, hm, hs, hu⟩ := sylow_fixedVector T
  exact ⟨m, ⟨hm, fun g hg => (hs g).mpr hg⟩, fun n hn => hu n hn.1 hn.2⟩

/-- The full group stabilizer of a nonzero Sylow-fixed vector is that Sylow subgroup. -/
theorem sylow_fixed_stabilizer (T : Sylow 2 Group) (m : Steinberg)
    (hm : m ≠ 0) (hfixed : ∀ g ∈ T, S g m = m) (g : Group) :
    S g m = m ↔ g ∈ T := by
  obtain ⟨n, _, hs, hu⟩ := sylow_fixedVector T
  rw [hu m hm hfixed]
  exact hs g

/-- Full point-parabolic commutation holds for every conjugate. -/
theorem point_conjugate_commutator_eq_top (g : Group) :
    subspaceCommutator S ⊤ (pointParabolicSL.map (MulAut.conj g).toMonoidHom) = ⊤ :=
  full_commutator_conjugate _ g point_commutator_eq_top

/-- Full line-parabolic commutation holds for every conjugate. -/
theorem line_conjugate_commutator_eq_top (g : Group) :
    subspaceCommutator S ⊤ (lineParabolicSL.map (MulAut.conj g).toMonoidHom) = ⊤ :=
  full_commutator_conjugate _ g line_commutator_eq_top

end
end BinaryLinearThree.SteinbergStructure.LocalActions
