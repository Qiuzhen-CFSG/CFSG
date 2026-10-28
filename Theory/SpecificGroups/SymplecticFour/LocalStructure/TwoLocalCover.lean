module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Every symplectic four-space two-local lies in a conjugate full parabolic

A two-local is the normalizer of a nonidentity two-subgroup Q. The radical
of the common fixed space of Q is a nonzero invariant totally isotropic
subspace. An actual symplectic matrix moves it to the standard point or
plane. Conjugation by that matrix therefore puts the entire normalizer
inside the corresponding full stabilizer from `Flag`.

The argument applies over every finite field of characteristic two. The
cardinality wrapper has the parameters of the PSp₄(2^f), f ≥ 2, converse;
it does not assume QT, K, E, or any parabolic coverage or rank statement.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(1), printed pp.3–4; repeated as Theorem 0.1.1(1), printed pp.481–482.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour
open TwoLocalCover
variable {F : Type*} [Field F]

private theorem conjugate_le_stabilizer (M : Subgroup (Sp F))
    (W P : Submodule F (Vector F)) (g : Sp F)
    (hM : M ≤ stabilizer W) (himage : W.map (toLinear g).toLinearMap = P) :
    M.map (MulAut.conj g).toMonoidHom ≤ stabilizer P := by
  rintro z ⟨m, hm, rfl⟩
  rw [mem_stabilizer_iff]
  intro x hx
  rw [← himage] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : m • y ∈ W := (mem_stabilizer_iff W m).mp (hM hm) y hy
  have h : g • (m • y) ∈ P := by
    rw [← himage]
    exact ⟨m • y, hy', rfl⟩
  change (g * m * g⁻¹) • (g • y) ∈ P
  simpa only [mul_smul, inv_smul_smul] using h

/-- Every two-local in Sp₄ over a finite field of characteristic two is
contained in a conjugate of one of the two full standard parabolics. -/
theorem twoLocal_parabolic_cover_of_charTwo [Finite F] [CharP F 2]
    (M : Subgroup (Sp F)) (hM : IsTwoLocal M) :
    ∃ g : Sp F, M.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      M.map (MulAut.conj g).toMonoidHom ≤ planeParabolic := by
  obtain ⟨W, hne, _, hW, hMW⟩ := twoLocal_stabilizes_isotropic M hM
  obtain ⟨g, hp | hl⟩ := isotropic_subspace_conjugate_standard W hne hW
  · exact ⟨g, Or.inl (conjugate_le_stabilizer M W (point F) g hMW hp)⟩
  · exact ⟨g, Or.inr (conjugate_le_stabilizer M W (plane F) g hMW hl)⟩

/-- Parabolic coverage with the exact finite-field parameters of the
PSp₄(2^f) converse. The parabolics are the full stabilizers from `Flag`. -/
theorem twoLocal_parabolic_cover [Finite F]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (_hf : 2 ≤ f)
    (M : Subgroup (Sp F)) (hM : IsTwoLocal M) :
    ∃ g : Sp F, M.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      M.map (MulAut.conj g).toMonoidHom ≤ planeParabolic := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact twoLocal_parabolic_cover_of_charTwo M hM

end Theory.SpecificGroups.SymplecticFour
