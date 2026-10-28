module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.Coordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies.InnerContainment

/-!
# Non-linear actors and their centralizers lie in the inner-field subgroup

Choose an involution of the elementary actor outside the linear kernel.
Projective Hilbert--90 conjugates it to the supplied pure field involution.
Its full centralizer lies in the canonical normal subgroup PSL₂(F)⟨σ⟩,
by fixed-field descent; normality carries this containment back. Triviality
of the ambient two-core then puts the literal ambient tau in that subgroup.
No equality between tau and a mixed four-group is asserted.

The rank-three field projection is surjective, so rank-three actors are also
non-linear. These facts feed the whole-family restriction in `MarkedActors`.
They include characteristics three and five and require no choice of an S₃
quotient image, prescribed centralizer Sylow intersection or local witness.

Source: Aschbacher--Smith, A.2.3(2), E.1.1--2 and E.1.14(6), printed pp.33,
209--210 and 214. The involution descent and marked centralizer are the proved
`projective_semilinear_involution_conj_inr` and `pureCentralizer_le_innerModel`.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.MarkedActors
variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

omit [Finite (PGammaL2 F)] in
/-- The full centralizer of any non-linear elementary actor is in the normal
inner-field subgroup, without a rank restriction on the actor. -/
theorem centralizer_le_innerModel_of_not_linear {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    (A : Subgroup (PGammaL2 F)) (hA : IsElementaryAbelian 2 A)
    (hlinear : ¬ A ≤ pGammaL2PGLRange F) :
    centralizer (A : Set (PGammaL2 F)) ≤ innerModel F σ := by
  classical
  let := hA
  let : (innerModel F σ).Normal := RankThreeFamilies.innerModel_normal hp hodd hF σ
  obtain ⟨x, hxA, hxL⟩ := SetLike.not_le_iff_exists.mp hlinear
  have hxfield : x.right ≠ 1 := by
    intro h
    apply hxL
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
    exact h
  have hxo : orderOf x = 2 := (orderOf_eq_prime_iff (x := x)).mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian x hxA,
      fun h => hxfield (by rw [h]; rfl)⟩
  have hxσ : x.right = σ := (fieldAut_eq_one_or hp hF σ hne x.right).resolve_left hxfield
  obtain ⟨c, hc⟩ := projective_semilinear_involution_conj_inr
    ⟨p, 2, hp, hodd, by decide, hF⟩ x hxo hxfield
  let e := MulAut.conj (SemidirectProduct.inl c : PGammaL2 F)⁻¹
  have hex : e x = SemidirectProduct.inr σ := by
    simpa only [e, MulAut.conj_apply, inv_inv, hxσ] using hc
  intro y hy
  have hyC : e y ∈ centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) := by
    rw [mem_centralizer_singleton_iff, ← hex, ← map_mul, ← map_mul]
    exact congrArg e (mem_centralizer_iff.mp hy x hxA).symm
  have hyN := RankThreeFamilies.pureCentralizer_le_innerModel hp hodd hF σ hsq hne hyC
  have hconj := (inferInstance : (innerModel F σ).Normal).conj_mem
    (e y) hyN (SemidirectProduct.inl c)
  simpa [e, MulAut.conj_apply, mul_assoc] using hconj

/-- Consequently the literal ambient tau also lies in the normal inner-field
subgroup. This is the E.1.8 input, and does not assert tau equals the actor. -/
theorem tau_le_innerModel_of_not_linear {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    (T A : Subgroup (PGammaL2 F)) (hA : IsElementaryAbelian 2 A)
    (hlinear : ¬ A ≤ pGammaL2PGLRange F) : tau T A ≤ innerModel F σ := by
  rw [full_tau_eq_inf_centralizer hp hodd hF hlarge]
  exact inf_le_right.trans
    (centralizer_le_innerModel_of_not_linear hp hodd hF σ hsq hne A hA hlinear)

/-- A rank-three elementary actor in the actual full group cannot be linear. -/
theorem rank_three_not_linear {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hne : σ ≠ 1)
    (A : Subgroup (PGammaL2 F)) (hA : IsElementaryAbelian 2 A)
    (hr : Group.rank A = 3) : ¬ A ≤ pGammaL2PGLRange F := by
  let e : PGammaL2 F ≃* (⊤ : Subgroup (PGammaL2 F)) := Subgroup.topEquiv.symm
  let B := A.map e.toMonoidHom
  let := hA
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  have hrB : Group.rank B = 3 :=
    (Group.rank_congr (A.equivMapOfInjective e.toMonoidHom e.injective)).symm.trans hr
  obtain ⟨x, hx⟩ := rank_three_fieldProjection_surjective hp hodd hF ⊤ le_top B hB hrB σ
  intro hlinear
  have hxA : (x.val : PGammaL2 F) ∈ A := by
    obtain ⟨a, ha, he⟩ := x.property
    exact congrArg (fun y : (⊤ : Subgroup (PGammaL2 F)) => (y : PGammaL2 F)) he ▸ ha
  have hxL := hlinear hxA
  rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom] at hxL
  exact hne (hx.symm.trans hxL)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.MarkedActors
