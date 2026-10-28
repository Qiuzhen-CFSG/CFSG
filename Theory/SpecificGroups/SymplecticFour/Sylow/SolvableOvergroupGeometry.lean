module

public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableParabolic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus

/-!
# From orthogonal root orbits to symplectic Sylow normalization

If the orbit of the standard vector under a subgroup is orthogonal to that
vector, its span is a nonzero invariant totally isotropic subspace. A genuine
symplectic change of coordinates therefore puts the subgroup inside one of
the two full parabolics. The existing rank-one quotient calculations imply
that a solvable Sylow overgroup in either parabolic normalizes that Sylow.

The last theorem isolates the remaining root calculation: in a solvable
subgroup containing the standard unipotent group, the orbit of the
standard vector must be orthogonal. This premise is explicit here; this
module does not claim to have proved it. Sylow conjugacy and both geometric
transports are fully discharged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
15.3.49 after (k), printed p.1144; full-parabolic calculations as in the
characteristic-two paragraph of Proposition 1.3.4, printed p.511.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
open TwoLocalCover
variable {F : Type*} [Field F]

private theorem conjugate_le_stabilizer (H : Subgroup (Sp F))
    (W P : Submodule F (Vector F)) (g : Sp F)
    (hH : H ≤ stabilizer W) (himage : W.map (toLinear g).toLinearMap = P) :
    H.map (MulAut.conj g).toMonoidHom ≤ stabilizer P := by
  rintro z ⟨m, hm, rfl⟩
  rw [mem_stabilizer_iff]
  intro x hx
  rw [← himage] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : m • y ∈ W := (mem_stabilizer_iff W m).mp (hH hm) y hy
  have h : g • (m • y) ∈ P := by
    rw [← himage]
    exact ⟨m • y, hy', rfl⟩
  change (g * m * g⁻¹) • (g • y) ∈ P
  simpa only [mul_smul, inv_smul_smul] using h

/-- Pairwise orthogonality of the point orbit gives an invariant isotropic subspace. -/
theorem parabolic_cover_of_orthogonal_point_orbit (H : Subgroup (Sp F))
    (ho : ∀ g ∈ H, form F (e 0) (g • e 0) = 0) :
    ∃ k : Sp F, H.map (MulAut.conj k).toMonoidHom ≤ pointParabolic ∨
      H.map (MulAut.conj k).toMonoidHom ≤ planeParabolic := by
  let O : Set (Vector F) := {v | ∃ g ∈ H, g • e 0 = v}
  let W := Submodule.span F O
  have he : e (F := F) 0 ∈ W := Submodule.subset_span ⟨1, H.one_mem, one_smul _ _⟩
  have hne : W ≠ ⊥ := by
    intro h
    have hz : e (F := F) 0 = 0 := by simpa only [h, Submodule.mem_bot] using he
    have := congrFun hz (.inl 0)
    simp [e] at this
  have hp (x y : Vector F) (hx : x ∈ O) (hy : y ∈ O) : form F x y = 0 := by
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨h, hh, rfl⟩ := hy
    have hv := preserves_form g (e 0) ((g⁻¹ * h) • e 0)
    simpa only [mul_smul, smul_inv_smul] using
      hv.trans (ho (g⁻¹ * h) (H.mul_mem (H.inv_mem hg) hh))
  have hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0 := by
    intro x hx y hy
    apply Submodule.span_induction₂ hp (fun _ _ => by simp) (fun _ _ => by simp)
      (fun _ _ _ _ _ _ hx hy => by simp [map_add, hx, hy])
      (fun _ _ _ _ _ _ hx hy => by simp [map_add, hx, hy])
      (fun _ _ _ _ _ h => by simp [map_smul, h])
      (fun _ _ _ _ _ h => by simp [map_smul, h]) hx hy
  have hHW : H ≤ stabilizer W := by
    intro g hg
    rw [mem_stabilizer_iff]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, H.mul_mem hg hh, mul_smul _ _ _⟩
    | zero =>
      change toLinear g 0 ∈ W
      rw [map_zero]
      exact W.zero_mem
    | add x y _ _ hx hy =>
      change toLinear g (x + y) ∈ W
      rw [map_add]
      exact W.add_mem hx hy
    | smul a x _ hx =>
      change toLinear g (a • x) ∈ W
      rw [map_smul]
      exact W.smul_mem a hx
  obtain ⟨k, hk | hk⟩ := isotropic_subspace_conjugate_standard W hne hW
  · exact ⟨k, Or.inl (conjugate_le_stabilizer H W (point F) k hHW hk)⟩
  · exact ⟨k, Or.inr (conjugate_le_stabilizer H W (plane F) k hHW hk)⟩

variable [Finite F] [CharP F 2]

/-- Parabolic containment, even after conjugation, suffices for Sylow normalization. -/
theorem solvable_conjugate_parabolic_le_normalizer
    (hF : 2 < Nat.card F) (S : Sylow 2 (Sp F)) (H : Subgroup (Sp F))
    (hsol : Group.IsSolvable H) (hSH : (S : Subgroup (Sp F)) ≤ H)
    (hpar : ∃ k : Sp F, H.map (MulAut.conj k).toMonoidHom ≤ pointParabolic ∨
      H.map (MulAut.conj k).toMonoidHom ≤ planeParabolic) :
    H ≤ normalizer (S : Set (Sp F)) := by
  obtain ⟨k, hk⟩ := hpar
  let a := MulAut.conj k
  let T := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let _ := hsol
  have hs : Group.IsSolvable (H.map a.toMonoidHom) :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective H)
  have hN := solvable_parabolic_le_normalizer hF T (H.map a.toMonoidHom) hs
    (map_mono hSH) hk
  change H.map a.toMonoidHom ≤ normalizer ((S : Subgroup (Sp F)).map a.toMonoidHom : Set (Sp F)) at hN
  rw [← map_equiv_normalizer_eq (S : Subgroup (Sp F)) a] at hN
  exact (map_le_map_iff_of_injective a.injective).mp hN

/-- The only missing matrix input is orthogonality of the standard point orbit.
This is a conditional reduction, not an unconditional placement theorem. -/
theorem solvable_overgroups_of_orthogonal_root_orbits
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hroot : ∀ (H : Subgroup (Sp F)), Group.IsSolvable H → unipotent ≤ H →
      ∀ g ∈ H, form F (e 0) (g • e 0) = 0)
    (S : Sylow 2 (Sp F)) (H : Subgroup (Sp F))
    (hsol : Group.IsSolvable H) (hSH : (S : Subgroup (Sp F)) ≤ H) :
    H ≤ normalizer (S : Set (Sp F)) := by
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF hn.le)
  let a := MulAut.conj k
  have hS : (S : Subgroup (Sp F)).map a.toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hk
  let _ := hsol
  have hs : Group.IsSolvable (H.map a.toMonoidHom) :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective H)
  have hUH : unipotent ≤ H.map a.toMonoidHom := hS ▸ map_mono hSH
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  have hN := solvable_conjugate_parabolic_le_normalizer hlarge
    (unipotentSylow hF hn.le) (H.map a.toMonoidHom) hs hUH
    (parabolic_cover_of_orthogonal_point_orbit _ (hroot _ hs hUH))
  change H.map a.toMonoidHom ≤ normalizer (unipotent (F := F) : Set (Sp F)) at hN
  rw [← hS, ← map_equiv_normalizer_eq (S : Subgroup (Sp F)) a] at hN
  exact (map_le_map_iff_of_injective a.injective).mp hN

end Theory.SpecificGroups.SymplecticFour
