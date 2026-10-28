module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry

/-!
# Natural flags for arbitrary six-letter Sylow two-subgroups

Conjugation acts simultaneously on the permutation subgroups and on the
actual binary natural module. The canonical even Borel determines its
unique invariant line and plane. For A₆ ≤ H ≤ S₆, embed that Borel in a
Sylow of H and conjugate to the prescribed Sylow. Pulling subspaces back
then gives the same marking for both source subspaces. Containment in a
Sylow of S₆ also proves existence, without assuming an invariant flag.

The stabilizers below are the library's actual representation stabilizers.
Their full and alternating two-cores are transported by the literal
conjugation map, preserving the point/plane and residual/intersection
conventions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.3.4, printed pp.84–85, and Notation 13.2.1, printed p.877.
The overgroup Sylow argument extends the existing line argument in
`BinaryFlags.NaturalHyperplanes` to both members of the flag.
-/

@[expose] public section

open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

abbrev move (g : S) (W : Submodule (ZMod 2) V) := W.map (naturalRepresentation Ω g)

@[simp] theorem move_one (W : Submodule (ZMod 2) V) : move 1 W = W := by
  simp only [move, map_one, Module.End.one_eq_id, Submodule.map_id]

theorem move_mul (g h : S) (W : Submodule (ZMod 2) V) :
    move (g * h) W = move g (move h W) := by
  simp only [move, map_mul, Module.End.mul_eq_comp, Submodule.map_comp]

@[simp] theorem move_inv (g : S) (W : Submodule (ZMod 2) V) :
    move g⁻¹ (move g W) = W := by rw [← move_mul, inv_mul_cancel, move_one]

@[simp] theorem move_inv' (g : S) (W : Submodule (ZMod 2) V) :
    move g (move g⁻¹ W) = W := by rw [← move_mul, mul_inv_cancel, move_one]

theorem move_injective (g : S) : Function.Injective (move g) := by
  intro W U h
  have := congrArg (move g⁻¹) h
  simpa using this

theorem move_finrank (g : S) (W : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (move g W) = Module.finrank (ZMod 2) W := by
  exact (LinearMap.GeneralLinearGroup.toLinearEquiv
    ((naturalRepresentation Ω).asGroupHom g)).finrank_map_eq W

theorem move_conjugate (g h : S) (W : Submodule (ZMod 2) V) :
    move ((MulAut.conj g) h) (move g W) = move g (move h W) := by
  change move (g * h * g⁻¹) (move g W) = _
  rw [move_mul, move_mul, move_inv]

/-- The library's setwise stabilizer, on the actual natural representation. -/
abbrev flagStabilizer (W : Submodule (ZMod 2) V) : Subgroup S :=
  Representation.BinaryOffender.subspaceStabilizer (naturalRepresentation Ω) W

theorem flagStabilizer_line : flagStabilizer canonicalLine = H1 := by
  ext g
  exact (NaturalPairing.mem_stabilizer_iff_map _ _).trans (canonicalLine_stabilizer g)

theorem flagStabilizer_plane : flagStabilizer canonicalPlane = H2 := by
  ext g
  exact (NaturalPairing.mem_stabilizer_iff_map _ _).trans (canonicalPlane_stabilizer g)

theorem flagStabilizer_move (g : S) (W : Submodule (ZMod 2) V) :
    flagStabilizer (move g W) = (flagStabilizer W).map (MulAut.conj g).toMonoidHom := by
  ext x
  obtain ⟨h, rfl⟩ := (MulAut.conj g).surjective x
  rw [mem_map_equiv]
  simp only [flagStabilizer, NaturalPairing.mem_stabilizer_iff_map, MulEquiv.symm_apply_apply]
  change move ((MulAut.conj g) h) (move g W) = move g W ↔ move h W = W
  rw [move_conjugate, (move_injective g).eq_iff]

/-- Transport uniqueness using the even canonical Borel, not just a chosen
fixed vector in an unrelated coordinate representation. -/
theorem invariant_unique_conjugate (B : Subgroup S) (hB : T0 ≤ B) (g : S)
    (W : Submodule (ZMod 2) V)
    (hW : ∀ x ∈ B.map (MulAut.conj g).toMonoidHom, move x W = W) :
    (Module.finrank (ZMod 2) W = 1 → W = move g canonicalLine) ∧
    (Module.finrank (ZMod 2) W = 2 → W = move g canonicalPlane) := by
  have hb : ∀ x ∈ T0, move x (move g⁻¹ W) = move g⁻¹ W := by
    intro x hx
    apply move_injective g
    rw [← move_conjugate, move_inv']
    exact hW _ ⟨x, hB hx, rfl⟩
  constructor
  · intro hd
    have he := canonicalLine_unique (move g⁻¹ W) ((move_finrank _ _).trans hd) hb
    have := congrArg (move g) he
    simpa using this
  · intro hd
    have he := canonicalPlane_unique (move g⁻¹ W) ((move_finrank _ _).trans hd) hb
    have := congrArg (move g) he
    simpa using this

noncomputable def canonicalSylow : Sylow 2 S := flagRelabel • borelSylow

theorem canonicalSylow_coe : (canonicalSylow : Subgroup S) = H1 ⊓ H2 := by
  change borel.map (MulAut.conj flagRelabel).toMonoidHom = _
  rw [borel, map_inf _ _ _ (MulAut.conj flagRelabel).injective, flagRelabel_duad]
  exact congrArg (H1 ⊓ ·) flagRelabel_syntheme

/-- Every Sylow two-subgroup of S₆ determines precisely the transported
canonical invariant line and plane. -/
theorem sylow_flag (T : Sylow 2 S) : ∃ g : S,
    (H1 ⊓ H2).map (MulAut.conj g).toMonoidHom = (T : Subgroup S) ∧
    ∀ W : Submodule (ZMod 2) V,
      (∀ x ∈ (T : Subgroup S), move x W = W) →
      (Module.finrank (ZMod 2) W = 1 → W = move g canonicalLine) ∧
      (Module.finrank (ZMod 2) W = 2 → W = move g canonicalPlane) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S canonicalSylow T
  have ht : (H1 ⊓ H2).map (MulAut.conj g).toMonoidHom = (T : Subgroup S) := by
    rw [← canonicalSylow_coe]
    exact congrArg (fun P : Sylow 2 S => (P : Subgroup S)) hg
  refine ⟨g, ht, fun W hW => invariant_unique_conjugate _ inf_le_left g W ?_⟩
  simpa only [ht] using hW

/-- Embed the canonical alternating Borel in a Sylow of the actual overgroup.
The conjugator belongs to that overgroup. -/
theorem exists_conjugate_T0_le (H : Subgroup S)
    (hH : alternatingGroup Ω ≤ H) (T : Sylow 2 H) :
    ∃ g : H, T0.map (MulAut.conj (g : S)).toMonoidHom ≤
      (T : Subgroup H).map H.subtype := by
  have hp : IsPGroup 2 T0 := by
    have hb : IsPGroup 2 ↥(H1 ⊓ H2) := canonicalSylow_coe ▸ canonicalSylow.isPGroup'
    exact hb.to_le inf_le_left
  have hT : T0 ≤ H := inf_le_right.trans hH
  obtain ⟨R, hR⟩ := (hp.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H R T
  have hc : (R : Subgroup H).map (MulAut.conj g).toMonoidHom = T :=
    congrArg (fun U : Sylow 2 H => (U : Subgroup H)) hg
  refine ⟨g, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  let tH : H := ⟨t, hT ht⟩
  have htR : tH ∈ R := hR ht
  have htT : g * tH * g⁻¹ ∈ T := by
    change g * tH * g⁻¹ ∈ (T : Subgroup H)
    rw [← hc]
    exact Subgroup.mem_map_of_mem _ htR
  exact ⟨g * tH * g⁻¹, htT, rfl⟩

/-- Simultaneously identify the two subspaces chosen in B.3.4 and 13.2.1,
for a Sylow of any actual permutation overgroup of A₆. -/
theorem sylow_flag_of_between (H : Subgroup S) (hH : alternatingGroup Ω ≤ H)
    (T : Sylow 2 H) (P Q : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) (hQ : Module.finrank (ZMod 2) Q = 2)
    (hPi : ∀ x ∈ (T : Subgroup H).map H.subtype, move x P = P)
    (hQi : ∀ x ∈ (T : Subgroup H).map H.subtype, move x Q = Q) :
    ∃ g : H, P = move (g : S) canonicalLine ∧ Q = move (g : S) canonicalPlane := by
  obtain ⟨g, hg⟩ := exists_conjugate_T0_le H hH T
  exact ⟨g, (invariant_unique_conjugate T0 le_rfl g P (fun x hx => hPi x (hg hx))).1 hP,
    (invariant_unique_conjugate T0 le_rfl g Q (fun x hx => hQi x (hg hx))).2 hQ⟩

/-- The two invariant subspaces form an incident flag, as in the source. -/
theorem sylow_line_le_plane (H : Subgroup S) (hH : alternatingGroup Ω ≤ H)
    (T : Sylow 2 H) (P Q : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) (hQ : Module.finrank (ZMod 2) Q = 2)
    (hPi : ∀ x ∈ (T : Subgroup H).map H.subtype, move x P = P)
    (hQi : ∀ x ∈ (T : Subgroup H).map H.subtype, move x Q = Q) : P ≤ Q := by
  obtain ⟨g, rfl, rfl⟩ := sylow_flag_of_between H hH T P Q hP hQ hPi hQi
  exact Submodule.map_mono canonicalLine_le_canonicalPlane

/-- Existence as well as uniqueness: a Sylow of the actual overgroup fixes
an incident line-plane flag in the natural module. -/
theorem sylow_flag_exists (H : Subgroup S) (hH : alternatingGroup Ω ≤ H)
    (T : Sylow 2 H) : ∃ g : H,
    ∀ x ∈ (T : Subgroup H).map H.subtype,
      move x (move (g : S) canonicalLine) = move (g : S) canonicalLine ∧
      move x (move (g : S) canonicalPlane) = move (g : S) canonicalPlane := by
  obtain ⟨U, hU⟩ := (T.isPGroup'.map H.subtype).exists_le_sylow
  obtain ⟨s, hs, _⟩ := sylow_flag U
  have hi : ∀ x ∈ (T : Subgroup H).map H.subtype,
      move x (move s canonicalLine) = move s canonicalLine ∧
      move x (move s canonicalPlane) = move s canonicalPlane := by
    intro x hx
    have hxU := hU hx
    rw [← hs] at hxU
    obtain ⟨y, hy, rfl⟩ := hxU
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, move_conjugate]
    exact ⟨congrArg (move s) ((canonicalLine_stabilizer y).mpr hy.1),
      congrArg (move s) ((canonicalPlane_stabilizer y).mpr hy.2)⟩
  obtain ⟨g, hP, hQ⟩ := sylow_flag_of_between H hH T
    (move s canonicalLine) (move s canonicalPlane)
    ((move_finrank s canonicalLine).trans canonicalLine_finrank)
    ((move_finrank s canonicalPlane).trans canonicalPlane_finrank)
    (fun x hx => (hi x hx).1) (fun x hx => (hi x hx).2)
  refine ⟨g, ?_⟩
  simpa only [hP, hQ] using hi

/-- The full line core in the chosen natural-module coordinates. -/
theorem line_core_of_marking (g : S) :
    (flagStabilizer (move g canonicalLine)).pCoreIn 2 =
      pointCore.map (MulAut.conj g).toMonoidHom := by
  rw [flagStabilizer_move, flagStabilizer_line,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective, H1_core_eq_pointCore]

/-- The full plane core in the chosen natural-module coordinates. -/
theorem plane_core_of_marking (g : S) :
    (flagStabilizer (move g canonicalPlane)).pCoreIn 2 =
      D.map (MulAut.conj g).toMonoidHom := by
  rw [flagStabilizer_move, flagStabilizer_plane,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective, H2_core_eq_D]

/-- The alternating line core, transported through the actual ambient map. -/
theorem alternating_line_core_of_marking (g : S) :
    (flagStabilizer (move g canonicalLine) ⊓ alternatingGroup Ω).pCoreIn 2 =
      pointCoreEven.map (MulAut.conj g).toMonoidHom := by
  rw [flagStabilizer_move, flagStabilizer_line, ← conjugate_alternating g,
    ← map_inf _ _ _ (MulAut.conj g).injective,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  rw [show H1 ⊓ alternatingGroup Ω = L1 from rfl, L1_core_eq_pointCoreEven]

/-- The alternating plane core is the marked even cube. -/
theorem alternating_plane_core_of_marking (g : S) :
    (flagStabilizer (move g canonicalPlane) ⊓ alternatingGroup Ω).pCoreIn 2 =
      D0.map (MulAut.conj g).toMonoidHom := by
  rw [flagStabilizer_move, flagStabilizer_plane, ← conjugate_alternating g,
    ← map_inf _ _ _ (MulAut.conj g).injective,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  rw [show H2 ⊓ alternatingGroup Ω = L2 from rfl, L2_core_eq_D0]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
