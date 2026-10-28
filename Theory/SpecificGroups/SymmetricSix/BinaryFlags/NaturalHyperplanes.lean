module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

/-!
# Sylow-stable hyperplanes in the natural six-letter module

Let `A₆ ≤ S ≤ S₆` and let `Q` be a Sylow two-subgroup of `S`. On the actual
binary augmentation quotient, any `Q`-stable line and `Q`-stable hyperplane
are perpendicular under the descended coordinate form.

The permutation `(04)(15)` takes the flag fixing `{4,5}` to the standard
Borel flag fixing `{0,1}`. This proves that the canonical alternating flag
group `T0` is a two-group. Embed it in a Sylow of `S` and conjugate that
Sylow to `Q`. Pullback under this permutation reduces uniqueness of the
`Q`-stable line to `NaturalGeometry.canonicalLine_unique`. The perpendicular
of the hyperplane is another invariant line, so nondegeneracy gives the
claimed equality. The proof does not require the line to lie in the hyperplane.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§B.3, printed pp.83–85, and Notation 13.2.1, printed p.877.
-/

public section

open BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes

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
private theorem exists_conjugate_T0_le (S : Subgroup (Equiv.Perm (Fin 6)))
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

/-- Pullback by the conjugating permutation reduces uniqueness to the canonical flag. -/
private theorem sylow_invariant_line_eq (S : Subgroup (Equiv.Perm (Fin 6)))
    (hS : alternatingGroup (Fin 6) ≤ S) (Q : Sylow 2 S)
    (P E : Submodule (ZMod 2) (natural (Fin 6)))
    (hP : Module.finrank (ZMod 2) P = 1)
    (hE : Module.finrank (ZMod 2) E = 1)
    (hPi : (Q : Subgroup S).map S.subtype ≤
      subspaceStabilizer (naturalRepresentation (Fin 6)) P)
    (hEi : (Q : Subgroup S).map S.subtype ≤
      subspaceStabilizer (naturalRepresentation (Fin 6)) E) : P = E := by
  obtain ⟨g, hg⟩ := exists_conjugate_T0_le S hS Q
  let r := naturalRepresentation (Fin 6)
  let f := r (g : Equiv.Perm (Fin 6))⁻¹
  have hinv (W : Submodule (ZMod 2) (natural (Fin 6)))
      (hW : (Q : Subgroup S).map S.subtype ≤ subspaceStabilizer r W) :
      ∀ t ∈ T0, (W.map f).map (r t) = W.map f := by
    intro t ht
    have hc := (mem_stabilizer_iff_map W _).mp
      (hW (hg (Subgroup.mem_map_of_mem _ ht)))
    change W.map (r ((g : Equiv.Perm (Fin 6)) * t * (g : Equiv.Perm (Fin 6))⁻¹)) = W at hc
    change (W.map (r (g : Equiv.Perm (Fin 6))⁻¹)).map (r t) =
      W.map (r (g : Equiv.Perm (Fin 6))⁻¹)
    have he : t * (g : Equiv.Perm (Fin 6))⁻¹ =
        (g : Equiv.Perm (Fin 6))⁻¹ *
          ((g : Equiv.Perm (Fin 6)) * t * (g : Equiv.Perm (Fin 6))⁻¹) := by group
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, he,
      map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hc]
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv
    (r.asGroupHom (g : Equiv.Perm (Fin 6))⁻¹)
  have hPe : Module.finrank (ZMod 2) (P.map f) = 1 := (e.finrank_map_eq P).trans hP
  have hEe : Module.finrank (ZMod 2) (E.map f) = 1 := (e.finrank_map_eq E).trans hE
  apply Submodule.map_injective_of_injective e.injective
  exact (canonicalLine_unique _ hPe (hinv P hPi)).trans
    (canonicalLine_unique _ hEe (hinv E hEi)).symm

/-- Every Sylow-stable hyperplane in the natural six-letter module is the
perpendicular of the Sylow-stable line. No coordinate marking is required. -/
theorem sylow_invariant_hyperplane_eq_orthogonal
    (S : Subgroup (Equiv.Perm (Fin 6)))
    (hS : alternatingGroup (Fin 6) ≤ S) (Q : Sylow 2 S)
    (P D : Submodule (ZMod 2) (natural (Fin 6)))
    (hP : Module.finrank (ZMod 2) P = 1)
    (hD : Module.finrank (ZMod 2) D = 3)
    (hPi : (Q : Subgroup S).map S.subtype ≤
      subspaceStabilizer (naturalRepresentation (Fin 6)) P)
    (hDi : (Q : Subgroup S).map S.subtype ≤
      subspaceStabilizer (naturalRepresentation (Fin 6)) D) :
    D = form.orthogonal P := by
  have hd : Module.finrank (ZMod 2) (form.orthogonal D) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even (Fin 6) (by decide), hD]
    rfl
  have he : form.orthogonal D = P :=
    sylow_invariant_line_eq S hS Q _ P hd hP
      (hDi.trans (stabilizer_le_orthogonal_stabilizer D)) hPi
  rw [← he, LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes
