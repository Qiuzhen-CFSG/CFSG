module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.PlaneTransport
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes

/-!
# Cubic actors in the natural plane stabilizer

The canonical syntheme rotation (024)(135) fixes no nonzero natural
vector. Its conjugate lies in the actual plane stabilizer's two-residual,
so its displacements span the whole module and no hyperplane is invariant.
Sylow conjugacy and the unique binary flag supply the coordinate change.

Source: Aschbacher–Smith, Notation 13.2.1, p.877 and the proof of 13.8.6,
p.948; the concrete augmentation quotient and flag of §B.3, pp.83–85.
-/

@[expose] public section
open Subgroup Module BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.PlaneGeometry
noncomputable section
local notation "r" => naturalRepresentation (Fin 6)

/-- Exchange the two distinguished duads while preserving the standard syntheme. -/
private def coordinateSwap : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 5

private theorem map_flag_borel :
    (H1 ⊓ H2).map (MulAut.conj coordinateSwap).toMonoidHom = borel := by
  have hp : coordinateSwap • pair 4 5 = pair 0 1 := by decide
  have hs : coordinateSwap • baseSyntheme = baseSyntheme := by decide
  rw [Subgroup.map_inf _ _ _ (MulAut.conj coordinateSwap).injective]
  change (MulAction.stabilizer S (pair 4 5)).map _ ⊓
    (MulAction.stabilizer S baseSyntheme).map _ = borel
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hp, hs]
  rfl

/-- The alternating flag group lies in a conjugate of the standard symmetric Borel. -/
private theorem T0_isPGroup : IsPGroup 2 T0 := by
  have hb : IsPGroup 2 borel := borelSylow.isPGroup'
  have hm : (H1 ⊓ H2) ≤ borel.comap (MulAut.conj coordinateSwap).toMonoidHom := by
    exact Subgroup.map_le_iff_le_comap.mp map_flag_borel.le
  exact (hb.comap_of_injective _ (MulAut.conj coordinateSwap).injective).to_le
    (inf_le_left.trans hm)

/-- Embed the canonical two-group in a Sylow of `S`, then conjugate that Sylow to `Q`. -/
theorem exists_conjugate_T0_le (S : Subgroup (Equiv.Perm (Fin 6)))
    (hS : alternatingGroup (Fin 6) ≤ S) (Q : Sylow 2 S) :
    ∃ g : S, T0.map (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom ≤
      (Q : Subgroup S).map S.subtype := by
  have hT : T0 ≤ S := inf_le_right.trans hS
  obtain ⟨R, hR⟩ := (T0_isPGroup.comap_subtype (K := S)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S R Q
  have hc : (R : Subgroup S).map (MulAut.conj g).toMonoidHom = Q :=
    congrArg (fun U : Sylow 2 S => (U : Subgroup S)) hg
  refine ⟨g, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  let tS : S := ⟨t, hT ht⟩
  have htR : tS ∈ R := hR ht
  have htQ : g * tS * g⁻¹ ∈ Q := by
    change g * tS * g⁻¹ ∈ (Q : Subgroup S)
    rw [← hc]
    exact Subgroup.mem_map_of_mem _ htR
  exact ⟨g * tS * g⁻¹, htQ, rfl⟩


/-- Pull a Sylow-stable subspace back to the canonical flag coordinates. -/
theorem aligned_invariant (S : Subgroup (Equiv.Perm (Fin 6)))
    (Q : Sylow 2 S) (g : S)
    (hg : T0.map (MulAut.conj g.val).toMonoidHom ≤ (Q : Subgroup S).map S.subtype)
    (W : Submodule (ZMod 2) V)
    (hW : (Q : Subgroup S).map S.subtype ≤ subspaceStabilizer r W) :
    ∀ t ∈ T0, (W.map (r g.val⁻¹)).map (r t) = W.map (r g.val⁻¹) := by
  intro t ht
  have hc := (mem_stabilizer_iff_map W _).mp (hW (hg (mem_map_of_mem _ ht)))
  change W.map (r (g.val * t * g.val⁻¹)) = W at hc
  have he : t * g.val⁻¹ = g.val⁻¹ * (g.val * t * g.val⁻¹) := by group
  rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, he,
    map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hc]

private def rotation : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5)

private theorem rotation_cube : rotation ^ 3 = 1 := by decide
private theorem rotation_even : rotation ∈ alternatingGroup (Fin 6) := by
  change Equiv.Perm.sign rotation = 1
  decide
private theorem rotation_plane : rotation ∈ H2 := by decide

private theorem rotation_fixed (v : V) (h : r rotation v = v) : v = 0 := by
  rcases vector_cases v with hv | ⟨⟨⟨i,j⟩, hij⟩, rfl⟩
  · exact hv
  · change r rotation (pairVector i j) = pairVector i j at h
    rw [pairVector_map] at h
    have he := (pairVector_eq_iff (rotation.injective.ne (ne_of_lt hij)) (ne_of_lt hij)).mp h
    have hc : ∀ i j : Fin 6, i < j →
        pair (rotation i) (rotation j) ≠ pair i j := by decide
    exact (hc i j hij he).elim

/-- The genuine residual of each Sylow-stable plane contains a fixed-point-free
cubic actor. No residual-image marking is assumed. -/
theorem plane_residual_actor (S : Subgroup (Equiv.Perm (Fin 6)))
    (hS : alternatingGroup (Fin 6) ≤ S) (Q : Sylow 2 S)
    (P : Submodule (ZMod 2) V) (hP : Module.finrank (ZMod 2) P = 2)
    (hPi : (Q : Subgroup S).map S.subtype ≤ subspaceStabilizer r P) :
    ∃ c ∈ residual (S ⊓ subspaceStabilizer r P), ∀ v, r c v = v → v = 0 := by
  obtain ⟨g, hg⟩ := exists_conjugate_T0_le S hS Q
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv ((naturalRepresentation (Fin 6)).asGroupHom g.val⁻¹)
  have hPc : P.map (r g.val⁻¹) = canonicalPlane :=
    canonicalPlane_unique _ ((e.finrank_map_eq P).trans hP)
      (aligned_invariant S Q g hg P hPi)
  have hback : canonicalPlane.map (r g.val) = P := by
    rw [← hPc, ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_eq_id, Submodule.map_id]
  let c := g.val * rotation * g.val⁻¹
  have hcP : c ∈ subspaceStabilizer r P := by
    apply (mem_stabilizer_iff_map _ _).mpr
    rw [← hback]
    change (canonicalPlane.map (r g.val)).map (r (g.val * rotation * g.val⁻¹)) = _
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul]
    have hm : (g.val * rotation * g.val⁻¹) * g.val = g.val * rotation := by group
    rw [hm, map_mul, Module.End.mul_eq_comp, Submodule.map_comp,
      (canonicalPlane_stabilizer rotation).mpr rotation_plane]
  have hcS : c ∈ S := S.mul_mem (S.mul_mem g.property (hS rotation_even)) (S.inv_mem g.property)
  let C := S ⊓ subspaceStabilizer r P
  let cC : C := ⟨c, hcS, hcP⟩
  have hc3 : cC ^ 3 = 1 := by
    apply Subtype.ext
    change (g.val * rotation * g.val⁻¹) ^ 3 = 1
    rw [← MulAut.conj_apply, ← map_pow, rotation_cube, map_one]
  refine ⟨c, ⟨cC, mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hc3)), rfl⟩, ?_⟩
  intro v hv
  have heq : r rotation (r g.val⁻¹ v) = r g.val⁻¹ v := by
    have hh := congrArg (r g.val⁻¹) hv
    change r g.val⁻¹ (r (g.val * rotation * g.val⁻¹) v) = _ at hh
    rw [← Module.End.mul_apply, ← map_mul] at hh
    have hm : g.val⁻¹ * (g.val * rotation * g.val⁻¹) = rotation * g.val⁻¹ := by group
    simpa only [hm, map_mul, Module.End.mul_apply] using hh
  have hz := rotation_fixed _ heq
  exact e.injective (hz.trans (map_zero e).symm)

/-- The fixed-point-free actor makes its displacement map surjective. -/
theorem displacement_top (A : Subgroup (Equiv.Perm (Fin 6)))
    (c : Equiv.Perm (Fin 6)) (hc : c ∈ A)
    (hf : ∀ v, r c v = v → v = 0) : subspaceCommutator r ⊤ A = ⊤ := by
  let f : V →ₗ[ZMod 2] V := r c - LinearMap.id
  have hi : Function.Injective f := LinearMap.ker_eq_bot.mp (by
    apply eq_bot_iff.mpr
    intro v hv
    exact hf v (sub_eq_zero.mp hv))
  have hs := LinearMap.surjective_of_injective hi
  apply top_unique
  intro v _
  obtain ⟨w, rfl⟩ := hs v
  exact Submodule.subset_span ⟨c, hc, w, Submodule.mem_top, rfl⟩

/-- A fixed-point-free symplectic actor cannot preserve a binary hyperplane. -/
theorem hyperplane_orbit_top (A : Subgroup (Equiv.Perm (Fin 6)))
    (c : Equiv.Perm (Fin 6)) (hc : c ∈ A)
    (hf : ∀ v, r c v = v → v = 0)
    (D : Submodule (ZMod 2) V) (hD : Module.finrank (ZMod 2) D = 3) :
    Submodule.span (ZMod 2) {v : V | ∃ a ∈ A, ∃ w ∈ D, r a w = v} = ⊤ := by
  let W := Submodule.span (ZMod 2) {v : V | ∃ a ∈ A, ∃ w ∈ D, r a w = v}
  have hDW : D ≤ W := by
    intro w hw
    exact Submodule.subset_span ⟨1, A.one_mem, w, hw, by simp⟩
  have hstable : W.map (r c) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · change (Submodule.span (ZMod 2) {v : V | ∃ a ∈ A, ∃ w ∈ D, r a w = v}).map (r c) ≤ W
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨a, ha, w, hw, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨c * a, A.mul_mem hc ha, w, hw,
        by rw [map_mul, Module.End.mul_apply]⟩
    · exact (LinearMap.GeneralLinearGroup.toLinearEquiv ((naturalRepresentation (Fin 6)).asGroupHom c)).finrank_map_eq W
  by_contra hn
  change W ≠ ⊤ at hn
  have hdW := Submodule.finrank_mono hDW
  have hdW' := Submodule.finrank_lt hn
  rw [hD] at hdW
  rw [finrank_natural_even (Fin 6) (by decide)] at hdW'
  norm_num only [Fintype.card_fin] at hdW'
  have hW3 : Module.finrank (ZMod 2) W = 3 := by omega
  let P := form.orthogonal W
  have hP : Module.finrank (ZMod 2) P = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even (Fin 6) (by decide), hW3]
    rfl
  have hPn : P ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hP
    contradiction
  obtain ⟨v, hv, hv0⟩ := Submodule.ne_bot_iff P |>.mp hPn
  have hPi : P.map (r c) = P := orthogonal_invariant W c hstable
  have hcv : r c v ∈ P := hPi ▸ Submodule.mem_map_of_mem hv
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0] at hcv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hcv
  have ha01 : a = 0 ∨ a = 1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases ha01 with rfl | rfl
  · rw [zero_smul] at ha
    exact hv0 ((LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation (Fin 6)).asGroupHom c)).injective (ha.symm.trans (map_zero _).symm))
  · rw [one_smul] at ha
    exact hv0 (hf v ha.symm)

/-- Both model calculations needed by the ambient plane transport. -/
theorem plane_generation (S : Subgroup (Equiv.Perm (Fin 6)))
    (hS : alternatingGroup (Fin 6) ≤ S) (Q : Sylow 2 S)
    (P D : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hD : Module.finrank (ZMod 2) D = 3)
    (hPi : (Q : Subgroup S).map S.subtype ≤ subspaceStabilizer r P) :
    subspaceCommutator r ⊤ (residual (S ⊓ subspaceStabilizer r P)) = ⊤ ∧
    Submodule.span (ZMod 2) {v : V |
      ∃ a ∈ residual (S ⊓ subspaceStabilizer r P), ∃ w ∈ D, r a w = v} = ⊤ := by
  obtain ⟨c, hc, hf⟩ := plane_residual_actor S hS Q P hP hPi
  exact ⟨displacement_top _ c hc hf, hyperplane_orbit_top _ c hc hf D hD⟩

end
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.PlaneGeometry
