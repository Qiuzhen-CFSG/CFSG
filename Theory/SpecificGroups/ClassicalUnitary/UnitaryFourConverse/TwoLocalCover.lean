module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover.Determinant
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover.PointTransport
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover.PlaneTransport
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport

/-!
# Reduction of the SU₄ two-local cover to adapted unitary bases

The radical of the common fixed space of a nonidentity two-subgroup is
nonzero, totally isotropic and invariant under its entire normalizer.
Its dimension is one or two. A genuine unitary matrix taking the coordinate
point or plane onto that radical can be corrected to determinant one by a
scalar, and the exact stabilizer conjugacy then gives the required cover.

The fixed-radical argument and determinant correction are proved in the
imported modules. The generic assembly theorem keeps the two adapted-basis
existence statements explicit, and the concrete theorem below discharges them
for the standard field involution hypotheses, including the field of four
elements.

Source: GLS3, Borel–Tits 3.1.3 and its classical fixed-space argument on
printed p.115 (`refs/KGroup/GLS3/chapter3.tex`), together with Witt extension
in Lemma 2.7.1 (`refs/KGroup/GLS3/chapter2.tex`, printed p.89). The intended
application includes every SU₄(2ⁿ) with n ≥ 1 and every two-local, without
requiring it to contain an ambient Sylow subgroup.
-/

open Matrix BenderSuzuki.MatrixGroups
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Transporting isotropic lines and planes by unitary matrices gives the full
parabolic cover. Both geometric existence assertions remain explicit here. -/
theorem twoLocal_parabolic_cover_of_unitary_transports
    (J : HermitianForm 4 F)
    (hpoint : ∀ W : Submodule F (Fin 4 → F), Module.finrank F W = 1 →
      W ≤ orthogonal J W → ∃ A : GL (Fin 4) F, A ∈ J.unitarySubgroup ∧
        W = (UnitaryFourFlag.pointSpace F).map A.val.mulVecLin)
    (hplane : ∀ W : Submodule F (Fin 4 → F), Module.finrank F W = 2 →
      W ≤ orthogonal J W → ∃ A : GL (Fin 4) F, A ∈ J.unitarySubgroup ∧
        W = (UnitaryFourFlag.planeSpace F).map A.val.mulVecLin)
    (M : Subgroup J.specialSubgroup) (hM : IsTwoLocal M) :
    ∃ g : J.specialSubgroup,
      M ≤ (UnitaryFourFlag.pointParabolicSU F J).map (MulAut.conj g).toMonoidHom ∨
      M ≤ (UnitaryFourFlag.planeParabolicSU F J).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨W, hn, hi, hd, hMW⟩ := twoLocal_stabilizes_isotropic J M hM
  rcases hd with hd | hd
  · obtain ⟨A, hA, hWA⟩ := hpoint W hd hi
    obtain ⟨g, hg⟩ := exists_special_same_subspace_images J A hA
    have hWg := hWA.trans (hg (UnitaryFourFlag.pointSpace F))
    rw [hWg, specialStabilizer_map_action, specialStabilizer_point] at hMW
    exact ⟨g, Or.inl hMW⟩
  · obtain ⟨A, hA, hWA⟩ := hplane W hd hi
    obtain ⟨g, hg⟩ := exists_special_same_subspace_images J A hA
    have hWg := hWA.trans (hg (UnitaryFourFlag.planeSpace F))
    rw [hWg, specialStabilizer_map_action, specialStabilizer_plane] at hMW
    exact ⟨g, Or.inr hMW⟩

/-- Every two-local in the even-characteristic unitary four-space model is
contained in a conjugate of one of the two full geometric parabolics.

The fixed-radical argument supplies a nonzero totally isotropic line or plane,
and the two transport theorems move that subspace to the corresponding
coordinate subspace.  The determinant correction from `Determinant` makes the
transport an actual special-unitary element, so the conclusion concerns the
existing `SU₄` parabolics rather than an abstract family tag.
-/
theorem twoLocal_parabolic_cover
    (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, σ x = x ^ (2 ^ n))
    (M : Subgroup (UnitaryFourFlag.form F σ hσ).specialSubgroup)
    (hM : IsTwoLocal M) :
    ∃ g : (UnitaryFourFlag.form F σ hσ).specialSubgroup,
      M ≤ (UnitaryFourFlag.pointParabolicSU F (UnitaryFourFlag.form F σ hσ)).map
          (MulAut.conj g).toMonoidHom ∨
      M ≤ (UnitaryFourFlag.planeParabolicSU F (UnitaryFourFlag.form F σ hσ)).map
          (MulAut.conj g).toMonoidHom := by
  let J := UnitaryFourFlag.form F σ hσ
  apply twoLocal_parabolic_cover_of_unitary_transports J
  · intro W hd hi
    exact exists_point_unitary_transport σ hσ n hn hcard hconj W hd hi
  · intro W hd hi
    exact exists_plane_unitary_transport σ hσ n hn hcard hconj W hd hi
  · exact hM

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
