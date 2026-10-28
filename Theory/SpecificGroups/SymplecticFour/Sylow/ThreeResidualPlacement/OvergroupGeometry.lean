module
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry.RootExtraction
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Proper Sylow overgroups in the symplectic four-space

Every proper overgroup of an ambient Sylow two-subgroup of Sp₄(F), for a
nonbinary finite field F of characteristic two, lies in a conjugate of the
full point or plane stabilizer.

After Sylow conjugacy, the subgroup contains the standard unipotent group.
The root-extraction calculation shows that a nonorthogonal image of e₀
would generate all of Sp₄. Thus its point orbit is orthogonal; the orbit
span is a nonzero invariant totally isotropic subspace. The existing
symplectic change-of-coordinates theorem puts that subspace at the standard
point or plane. No residual-solvability or two-local hypothesis is used.

This is the intrinsic geometric input to the symplectic case of
Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 15.3.28,
printed p.1131 (PDF p.1148), with 15.3.26–27 on pp.1130–1131 and the
model list in B.5.5–6, printed pp.104–105 (PDF pp.115–116).
The separate parent `ThreeResidualPlacement` owns the residual-normalization
assembly; this module does not import it.
-/

public section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement
variable {F : Type*} [Field F] [CharP F 2]

/-- Every vector in the point orbit of a proper unipotent overgroup is orthogonal to e₀. -/
theorem orthogonal_point_orbit_of_proper_unipotent_overgroup
    (H : Subgroup (Sp F)) (hUH : unipotent ≤ H) (hH : H ≠ ⊤) :
    ∀ g ∈ H, form F (e 0) (g • e 0) = 0 := by
  intro g hg
  have hz : g.val (.inr 0) (.inl 0) = 0 := by
    by_contra hz
    exact hH (OvergroupGeometry.eq_top_of_nonorthogonal_element H hUH g hg hz)
  simp [form_apply, e, smul_eq_mulVec, Fin.sum_univ_two, hz]

/-- A proper subgroup containing the standard unipotent subgroup preserves an
isotropic point or plane, after a symplectic change of coordinates. -/
theorem proper_unipotent_overgroup_parabolic_cover
    (H : Subgroup (Sp F)) (hUH : unipotent ≤ H) (hH : H ≠ ⊤) :
    ∃ g : Sp F, H.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      H.map (MulAut.conj g).toMonoidHom ≤ planeParabolic :=
  parabolic_cover_of_orthogonal_point_orbit H
    (orthogonal_point_orbit_of_proper_unipotent_overgroup H hUH hH)

/-- Every proper overgroup of an ambient Sylow two-subgroup of nonbinary Sp₄(F)
lies in a conjugate of a full point or plane parabolic. -/
theorem proper_sylow_overgroup_parabolic_cover [Finite F]
    (hF : 2 < Nat.card F) (Q : Sylow 2 (Matrix.symplecticGroup (Fin 2) F))
    (H : Subgroup (Matrix.symplecticGroup (Fin 2) F))
    (hQH : (Q : Subgroup _) ≤ H) (hH : H ≠ ⊤) :
    ∃ g : Matrix.symplecticGroup (Fin 2) F,
      H.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      H.map (MulAut.conj g).toMonoidHom ≤ planeParabolic := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hc : Nat.card F = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  have hn1 : 1 ≤ (n : ℕ) := by
    by_contra! hn1
    have hn0 : (n : ℕ) = 0 := by omega
    rw [hc, hn0, pow_zero] at hF
    omega
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (Sp F) Q (unipotentSylow hc hn1)
  let a := MulAut.conj k
  have hQ : (Q : Subgroup (Sp F)).map a.toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hk
  have hUH : unipotent ≤ H.map a.toMonoidHom := hQ ▸ map_mono hQH
  have hproper : H.map a.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    apply top_unique
    intro x _
    apply (Subgroup.mem_map_iff_mem (f := a.toMonoidHom) a.injective).mp
    rw [htop]
    exact mem_top _
  obtain ⟨g, hg⟩ := proper_unipotent_overgroup_parabolic_cover
    (H.map a.toMonoidHom) hUH hproper
  refine ⟨g * k, ?_⟩
  have he : (H.map a.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g * k)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [a, MulAut.conj_apply, mul_assoc]
  rwa [he] at hg

end Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement
