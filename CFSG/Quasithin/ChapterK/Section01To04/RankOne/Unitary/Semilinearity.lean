module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Model
public import Theory.SpecificGroups.SU3.EvenSemilinear.SpecialCoverage
public import Theory.Representation.FiniteSchurIntertwiner
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Coefficients

/-!
# The compatible coefficient action of the actual natural SU₃ module

The source layer is normal because it is F*(G). Its conjugation automorphisms,
transported through the marked equivalence with the full special unitary group,
have actual unitary-semilinear matrix representatives. Comparing those
representatives with the ambient binary action leaves a commuting intertwiner.
The finite Schur field makes that intertwiner F-linear, so the same field
automorphism controls both the ambient module action and the SU₃ matrices.
Uniqueness of the coefficient automorphism assembles them into a homomorphism.

The full SU₃ carrier and its possible cubic center are retained throughout.
This discharges the coefficient-action input to the unitary source assembly;
the independent assertion about linear involutions remains with its owner.
Source: Aschbacher–Smith, K.3.3, printed p.456 (1 March 2004 manuscript).
-/

public section

open Matrix BenderSuzuki.MatrixGroups Representation
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryModel
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (M : UnitaryModel J ρ L)

private def coefficientEquiv (σ : F ≃+* F) :
    (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F) :=
  { AddEquiv.piCongrRight (fun _ : Fin 3 => σ.toAddEquiv) with
    map_smul' := fun c v => by
      ext i
      exact ZMod.map_smul σ c (v i) }

private def semilinearEquiv (σ : F ≃+* F) (u : GL (Fin 3) F) :
    (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F) :=
  (coefficientEquiv σ).trans ((GeneralLinearGroup.toLin u).toLinearEquiv.restrictScalars (ZMod 2))

private theorem semilinearEquiv_apply (σ : F ≃+* F) (u : GL (Fin 3) F)
    (v : Fin 3 → F) : semilinearEquiv σ u v = u.val *ᵥ (σ ∘ v) := rfl

private theorem semilinearEquiv_smul (σ : F ≃+* F) (u : GL (Fin 3) F)
    (c : F) (v : Fin 3 → F) :
    semilinearEquiv σ u (c • v) = σ c • semilinearEquiv σ u v := by
  simp only [semilinearEquiv_apply]
  have hv : σ ∘ (c • v) = σ c • (σ ∘ v) := by
    ext i
    exact σ.map_mul c (v i)
  rw [hv, Matrix.mulVec_smul]

private theorem semilinearEquiv_intertwines (σ : F ≃+* F) (u X Y : GL (Fin 3) F)
    (hY : Y = u * GeneralLinearGroup.map σ.toRingHom X * u⁻¹)
    (v : Fin 3 → F) :
    semilinearEquiv σ u (X.val *ᵥ v) = Y.val *ᵥ semilinearEquiv σ u v := by
  have hm : σ ∘ (X.val *ᵥ v) =
      (GeneralLinearGroup.map σ.toRingHom X).val *ᵥ (σ ∘ v) := by
    ext i
    exact σ.toRingHom.map_mulVec X.val v i
  have he : Y * u = u * GeneralLinearGroup.map σ.toRingHom X := by
    rw [hY]
    group
  rw [semilinearEquiv_apply, hm, semilinearEquiv_apply,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun A : GL (Fin 3) F => A.val *ᵥ (σ ∘ v)) he.symm

variable [Finite F] [Finite G]

omit [Finite F] [Finite G] in
private theorem coordinate_irreducible (h : SourceHypotheses ρ L) :
    IsIrreducible (M.coordinateAction.comp L.subtype) := by
  let e : Representation.Equiv (ρ.comp L.subtype) (M.coordinateAction.comp L.subtype) :=
    Representation.Equiv.mk M.coordinates (by
      intro l
      apply LinearMap.ext
      intro v
      exact (M.coordinateAction_apply l v).symm)
  exact (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv e)).mp h.irreducible

/-- The coefficient supplied by actual matrix coverage also acts on the column module. -/
theorem exists_semilinear_and_conjugation (h : SourceHypotheses ρ L)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s)) (g : G) :
    let : L.Normal := h.layer_normal
    ∃ σ : F ≃+* F,
      (∀ (c : F) (v : Fin 3 → F),
        M.coordinateAction g (c • v) = σ c • M.coordinateAction g v) ∧
      ∃ u : J.unitarySubgroup, ∀ l : L,
        (M.groupEquiv (MulAut.conjNormal g l)).val =
          u.val * GeneralLinearGroup.map σ.toRingHom (M.groupEquiv l).val * u.val⁻¹ := by
  let : L.Normal := h.layer_normal
  let a : MulAut J.specialSubgroup :=
    M.groupEquiv.symm.trans ((MulAut.conjNormal g).trans M.groupEquiv)
  obtain ⟨σ, u, hu⟩ := HermitianForm.EvenSemilinear.special_semilinear_coverage
    J hJ hs hcard hconj a
  have hg (l : L) :
      (M.groupEquiv (MulAut.conjNormal g l)).val =
        u.val * GeneralLinearGroup.map σ.toRingHom (M.groupEquiv l).val * u.val⁻¹ := by
    simpa only [a, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hu (M.groupEquiv l)
  refine ⟨σ, ?_, u, hg⟩
  let τ := M.coordinateAction.comp L.subtype
  let : IsIrreducible τ := M.coordinate_irreducible h
  have hτ (l : L) (c : F) (v : Fin 3 → F) : τ l (c • v) = c • τ l v := by
    change M.coordinateAction (l : G) (c • v) = c • M.coordinateAction (l : G) v
    rw [M.coordinateAction_natural, M.coordinateAction_natural, Matrix.mulVec_smul]
  intro c v
  apply FiniteSchurIntertwiner.semilinear_of_intertwining τ hτ
    (MulAut.conjNormal g) (M.coordinateAction g) (semilinearEquiv σ u.val) σ
  · intro l v
    change M.coordinateAction g (M.coordinateAction (l : G) v) =
      M.coordinateAction (MulAut.conjNormal g l : G) (M.coordinateAction g v)
    rw [MulAut.conjNormal_apply]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  · intro l v
    change semilinearEquiv σ u.val (M.coordinateAction (l : G) v) =
      M.coordinateAction (MulAut.conjNormal g l : G) (semilinearEquiv σ u.val v)
    rw [M.coordinateAction_natural, M.coordinateAction_natural]
    exact semilinearEquiv_intertwines σ u.val _ _ (hg l) v
  · exact semilinearEquiv_smul σ u.val

open SymplecticConjugatePair.Ambient.SemilinearCoefficients

/-- The actual ambient coefficient homomorphism, with the same coefficients on SU₃. -/
theorem exists_coefficientAction (h : SourceHypotheses ρ L)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s)) :
    let : L.Normal := h.layer_normal
    ∃ π : G →* (F ≃+* F),
      (∀ (g : G) (c : F) (v : Fin 3 → F),
        M.coordinateAction g (c • v) = π g c • M.coordinateAction g v) ∧
      ∀ g : G, ∃ u : J.unitarySubgroup, ∀ l : L,
        (M.groupEquiv (MulAut.conjNormal g l)).val =
          u.val * GeneralLinearGroup.map (π g).toRingHom (M.groupEquiv l).val * u.val⁻¹ := by
  let : L.Normal := h.layer_normal
  have hpoint := M.exists_semilinear_and_conjugation h hJ hs hcard hconj
  have hsemi : ∀ g : G, ∃ σ : F ≃+* F, ∀ (c : F) (v : Fin 3 → F),
      M.coordinateAction g (c • v) = σ c • M.coordinateAction g v :=
    fun g => ⟨(hpoint g).choose, (hpoint g).choose_spec.1⟩
  let π := coefficientHom M.coordinateAction hsemi
  have hπ := coefficientHom_smul M.coordinateAction hsemi
  refine ⟨π, hπ, fun g => ?_⟩
  obtain ⟨σ, hσ, u, hu⟩ := hpoint g
  have he : π g = σ := coefficient_unique M.coordinateAction g (hπ g) hσ
  exact ⟨u, fun l => by rw [he]; exact hu l⟩
end CFSG.Quasithin.ChapterK.RankOne.UnitaryModel
