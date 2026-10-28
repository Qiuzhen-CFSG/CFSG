module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Geometry
/-!
# Equivariance of stabilizers and fixed spaces

Conjugation transports the actual point stabilizer and fixed submodule.
These identities keep the chosen Sylow, fixed line, and actor in the same
coordinates when assembling the adapted-pair argument for H.9.1(4).
-/

public section

namespace BinaryNaturalDual.AdaptedPair
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : G →* (V ≃ₗ[ZMod 2] V))
theorem conjugate_apply (g h : G) (v : V) : ρ (MulAut.conj g h) (ρ g v) = ρ g (ρ h v) := by
  simp only [MulAut.conj_apply, map_mul, map_inv, LinearEquiv.mul_apply,
    LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
theorem pointStabilizer_map_conj (g : G) (v : V) :
    (pointStabilizer ρ v).map (MulAut.conj g).toMonoidHom =
      pointStabilizer ρ (ρ g v) := by
  let : MulAction G V := MulAction.compHom V ρ
  exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj g v).symm
theorem fixedVectors_map_conj (g : G) (H : Subgroup G) :
    (fixedVectors ρ H).map (ρ g).toLinearMap =
      fixedVectors ρ (H.map (MulAut.conj g).toMonoidHom) := by
  have he (a b : G) (v : V) : ρ (MulAut.conj a b) (ρ a v) = ρ a (ρ b v) := by
    simp only [MulAut.conj_apply, map_mul, map_inv, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  apply le_antisymm
  · rintro w ⟨u, hu, rfl⟩
    change ∀ h ∈ H, ρ h u = u at hu
    rintro h ⟨h, hh, rfl⟩
    change ρ (MulAut.conj g h) (ρ g u) = ρ g u
    rw [he, hu h hh]
  · intro w hw
    refine ⟨(ρ g).symm w, ?_, (ρ g).apply_symm_apply w⟩
    change ∀ h ∈ H, ρ h ((ρ g).symm w) = (ρ g).symm w
    intro h hh
    apply (ρ g).injective
    rw [← he, LinearEquiv.apply_symm_apply]
    exact hw _ (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hh)
/-- In particular, the dimension of the fixed space is unchanged. -/
theorem finrank_fixedVectors_conj (g : G) (H : Subgroup G) :
    Module.finrank (ZMod 2) (fixedVectors ρ (H.map (MulAut.conj g).toMonoidHom)) =
      Module.finrank (ZMod 2) (fixedVectors ρ H) := by
  rw [← fixedVectors_map_conj]
  exact (ρ g).finrank_map_eq _

/-- Noncentralization by the inner point stabilizer transports together
with the point and the fixed space. -/
theorem moves_fixedVectors_conj (L H : Subgroup G) (g : G) (hg : g ∈ L) (v : V)
    (hmoves : ∃ a ∈ L, ρ a v = v ∧ ∃ z ∈ fixedVectors ρ H, ρ a z ≠ z) :
    ∃ a ∈ L, ρ a (ρ g v) = ρ g v ∧
      ∃ z ∈ fixedVectors ρ (H.map (MulAut.conj g).toMonoidHom), ρ a z ≠ z := by
  obtain ⟨a, ha, hav, z, hz, haz⟩ := hmoves
  refine ⟨MulAut.conj g a, L.mul_mem (L.mul_mem hg ha) (L.inv_mem hg), ?_,
    ρ g z, ?_, ?_⟩
  · rw [conjugate_apply, hav]
  · rw [← fixedVectors_map_conj]
    exact Submodule.mem_map_of_mem hz
  · rw [conjugate_apply]
    exact fun h => haz ((ρ g).injective h)

/-- An inner actor preserves the geometric interpretation of the moving space. -/
theorem movingSpace_map_innerActor {n : ℕ} (d : CoordinateAction n)
    (g : MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) (hg : g ∈ innerGroup n)
    (v : CoordinateSpace n) :
    (movingSpace v).map (linearAction d g).toLinearMap = movingSpace (linearAction d g v) := by
  obtain ⟨a, rfl⟩ := hg
  have he : linearAction d (MulAut.conj a) = BinaryLinear.NaturalDualFlag.action a := by
    apply LinearEquiv.ext
    intro x
    exact linearAction_inner d a x
  rw [he, movingSpace_map_inner]

/-- Transport the fixed vectors in the moving space by the same inner actor
that transports the point and its subgroup. -/
theorem movingSpace_fixedVectors_map_inner {n : ℕ} (d : CoordinateAction n)
    (g : MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) (hg : g ∈ innerGroup n)
    (H : Subgroup (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)))
    (v : CoordinateSpace n) :
    ((movingSpace v) ⊓ fixedVectors (linearAction d) (H ⊓ pointStabilizer (linearAction d) v)).map
        (linearAction d g).toLinearMap =
      movingSpace (linearAction d g v) ⊓ fixedVectors (linearAction d)
        (H.map (MulAut.conj g).toMonoidHom ⊓ pointStabilizer (linearAction d) (linearAction d g v)) := by
  rw [Submodule.map_inf _ (linearAction d g).injective,
    movingSpace_map_innerActor d g hg, fixedVectors_map_conj,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, pointStabilizer_map_conj]

/-- Evaluation remains one under every inner transporter. -/
theorem quadratic_innerActor {n : ℕ} (d : CoordinateAction n)
    (g : MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) (hg : g ∈ innerGroup n)
    (v : CoordinateSpace n) : quadratic (linearAction d g v) = quadratic v := by
  obtain ⟨a, rfl⟩ := hg
  rw [linearAction_inner, quadratic_apply]
  simp only [BinaryLinear.NaturalDualFlag.action_fst,
    BinaryLinear.NaturalDualFlag.action_snd, LinearEquiv.symm_apply_apply, quadratic_apply]

end BinaryNaturalDual.AdaptedPair
