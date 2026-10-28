module

public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm
public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.ProjectiveField
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# A Frobenius actor in every standard outer four-group of PSL₃(4)

The concrete standard subgroup is covered by the linear–field subgroup and
its graph coset. Two distinct nonidentity actors in the graph coset have a
nonidentity difference in the linear–field subgroup. A purely linear
involution is inner: its cube has determinant one because GF(4)ˣ has order
three, and its cube is itself.

The remaining actor is linear times Frobenius. Conjugating by its linear
factor makes the new linear factor determinant one, since Frobenius squares
the determinant. Centerlessness of the actual quotient SL₃(4)/Z(SL₃(4))
turns the involution equation into a projective Frobenius cocycle. The
existing Sylow calculation makes that cocycle a coboundary and supplies
the final conjugator. No lifting through an exceptional central cover is
used. Coverage of arbitrary automorphisms is a separate theorem.

Source: the PSL₃(4) case in the proof of Aschbacher--Smith 15.3.38,
`refs/quasithin.pdf`, printed p.1137 (PDF p.1154); GLS3, Theorem 2.5.12
and the concrete matrix actions in §2.7, `refs/KGroup/GLS3/chapter2.tex`.
The imported ATLAS elementary-generation proof retains its source
attribution and license in `ExceptionalIsomorphisms/Elementary.lean`.
-/

public section

open scoped MatrixGroups
open Subgroup
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Four.OuterPlane.FieldOccurrence

private theorem coefficient_eq_one_or_frobenius (σ : F ≃+* F) :
    σ = 1 ∨ σ = fieldFrobenius := by
  classical
  let j : (F ≃+* F) → (F ≃ₐ[ZMod 2] F) := fun τ =>
    AlgEquiv.ofRingEquiv (f := τ) (fun z =>
      congrArg (fun f : ZMod 2 →+* F => f z)
        (Subsingleton.elim (τ.toRingHom.comp (algebraMap (ZMod 2) F))
          (algebraMap (ZMod 2) F)))
  have hj : Function.Injective j := fun τ υ h => RingEquiv.ext fun x =>
    congrArg (fun f : F ≃ₐ[ZMod 2] F => f x) h
  let : Finite (F ≃+* F) := Finite.of_injective j hj
  let : Fintype (F ≃+* F) := Fintype.ofFinite _
  have hc : Fintype.card (F ≃+* F) ≤ 2 := by
    have h := Nat.card_le_card_of_injective j hj
    rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank 2 (by decide),
      Nat.card_eq_fintype_card] at h
    exact h
  have hn : fieldFrobenius ≠ 1 := by
    intro he
    obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
    exact hx (congrArg (fun τ : F ≃+* F => τ x) he)
  by_contra! hs
  have hh := (Finset.card_le_univ ({1, fieldFrobenius, σ} : Finset (F ≃+* F))).trans hc
  simp [Ne.symm hs.1, Ne.symm hs.2, Ne.symm hn] at hh

private theorem frobenius_eq_fieldAction :
    pslFrobenius = PSL3.OuterSolvable.fieldAction F fieldFrobenius := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [pslFrobenius_mk, fieldAction_mk]
    rfl

private theorem congr_eq (d a : MulAut PSL) : MulAut.congr d a = d * a * d⁻¹ := rfl

private theorem unit_cube (u : Fˣ) : u ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := u)
  simpa only [Nat.card_units, card_F] using h

/-- A linear involution has trivial diagonal outer image. -/
theorem linear_involution_inner (m : GL (Fin 3) F)
    (hm : (linearConj F m) ^ 2 = 1) :
    linearConj F m ∈ MulAut.innerSubgroup PSL := by
  have hd : GeneralLinearGroup.det (m ^ 3) = 1 := by
    rw [map_pow, unit_cube]
  let x : SL := (slEquivDetKernel F).symm ⟨m ^ 3, hd⟩
  have hx : SpecialLinearGroup.toGL x = m ^ 3 := slEquivDetKernel_symm_toGL F _
  have he : linearConj F m = MulAut.conj (QuotientGroup.mk x) := by
    rw [← linearConj_toGL, hx, map_pow, pow_succ, hm, one_mul]
  exact ⟨QuotientGroup.mk x, he.symm⟩

private theorem det_frobenius (m : GL (Fin 3) F) :
    GeneralLinearGroup.det (GeneralLinearGroup.map fieldFrobenius.toRingHom m) =
      (GeneralLinearGroup.det m) ^ 2 := by
  apply Units.ext
  change (fieldFrobenius.toRingHom.mapMatrix m.val).det = m.val.det ^ 2
  rw [← RingHom.map_det]
  rfl

private theorem frobenius_linear (m : GL (Fin 3) F) :
    pslFrobenius * linearConj F m =
      linearConj F (GeneralLinearGroup.map fieldFrobenius.toRingHom m) * pslFrobenius := by
  rw [frobenius_eq_fieldAction]
  exact field_linearConj _ _

/-- Conjugating a linear–Frobenius actor removes its diagonal part. -/
theorem linear_frobenius_conjugate_inner (m : GL (Fin 3) F) :
    ∃ x : PSL, MulAut.congr (linearConj F m) (linearConj F m * pslFrobenius) =
      MulAut.conj x * pslFrobenius := by
  let n := m * m * (GeneralLinearGroup.map fieldFrobenius.toRingHom m)⁻¹
  have hn : GeneralLinearGroup.det n = 1 := by
    simp only [n, map_mul, map_inv, det_frobenius, pow_two]
    group
  let x : SL := (slEquivDetKernel F).symm ⟨n, hn⟩
  have hx : SpecialLinearGroup.toGL x = n := slEquivDetKernel_symm_toGL F _
  refine ⟨QuotientGroup.mk x, ?_⟩
  rw [congr_eq, ← linearConj_toGL, hx]
  change linearConj F m * (linearConj F m * pslFrobenius) * (linearConj F m)⁻¹ =
    linearConj F (m * m * (GeneralLinearGroup.map fieldFrobenius.toRingHom m)⁻¹) * pslFrobenius
  rw [map_mul, map_mul, map_inv]
  have hh := frobenius_linear m⁻¹
  simp only [map_inv] at hh
  calc
    _ = linearConj F m * linearConj F m *
        (pslFrobenius * (linearConj F m)⁻¹) := by group
    _ = _ := by rw [hh]; group

private theorem frobenius_conj (x : PSL) :
    pslFrobenius * MulAut.conj x = MulAut.conj (pslFrobenius x) * pslFrobenius := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

private theorem inner_frobenius_conjugate (x : PSL)
    (hx : (MulAut.conj x * pslFrobenius) ^ 2 = 1) :
    ∃ d : MulAut PSL, MulAut.congr d (MulAut.conj x * pslFrobenius) = pslFrobenius := by
  have he : (MulAut.conj x * pslFrobenius) ^ 2 =
      MulAut.conj (x * pslFrobenius x) := by
    rw [pow_two, mul_assoc, ← mul_assoc pslFrobenius, frobenius_conj]
    rw [mul_assoc, ← pow_two, pslFrobenius_sq, mul_one, ← map_mul]
  have hc : x * pslFrobenius x = 1 := by
    let := Atlas.sl_perfect (F := F) 3 (by decide)
    apply MulAut.conj_injective_of_center_eq_bot
      (Group.IsPerfect.center_quotient_center_eq_bot SL)
    rw [← he, hx, map_one]
  obtain ⟨b, hb⟩ := InvolutionClasses.projective_field_coboundary x hc
  refine ⟨(MulAut.conj b)⁻¹, ?_⟩
  rw [congr_eq, hb, map_mul, map_inv, inv_inv]
  calc
    _ = (MulAut.conj (pslFrobenius b))⁻¹ *
        (pslFrobenius * MulAut.conj b) := by group
    _ = pslFrobenius := by rw [frobenius_conj]; group

/-- Every involution in the full linear–Frobenius coset is conjugate to the
literal Frobenius automorphism of SL₃(4)/Z(SL₃(4)). -/
theorem linear_frobenius_involution_conjugate (m : GL (Fin 3) F)
    (hm : (linearConj F m * pslFrobenius) ^ 2 = 1) :
    ∃ d : MulAut PSL, MulAut.congr d (linearConj F m * pslFrobenius) = pslFrobenius := by
  obtain ⟨x, hx⟩ := linear_frobenius_conjugate_inner m
  have hx2 : (MulAut.conj x * pslFrobenius) ^ 2 = 1 := by
    rw [← hx, ← map_pow, hm, map_one]
  obtain ⟨d, hd⟩ := inner_frobenius_conjugate x hx2
  refine ⟨d * linearConj F m, ?_⟩
  rw [congr_eq] at hx hd ⊢
  calc
    _ = d * (linearConj F m * (linearConj F m * pslFrobenius) *
        (linearConj F m)⁻¹) * d⁻¹ := by group
    _ = pslFrobenius := by rw [hx]; exact hd

/-- The subgroup generated by linear and coefficient automorphisms. -/
noncomputable def linearField : Subgroup (MulAut PSL) :=
  innerDiagonal F ⊔ (PSL3.OuterSolvable.fieldAction F).range

private theorem linear_mul_field_mem (m : GL (Fin 3) F) (σ : F ≃+* F) :
    linearConj F m * PSL3.OuterSolvable.fieldAction F σ ∈ linearField :=
  linearField.mul_mem
    ((show innerDiagonal F ≤ linearField from le_sup_left) ⟨m, rfl⟩)
    ((show (PSL3.OuterSolvable.fieldAction F).range ≤ linearField from le_sup_right) ⟨σ, rfl⟩)

/-- The compatibility identities give a genuine factorization in the
linear–field subgroup. -/
theorem linearField_factorization (a : MulAut PSL) (ha : a ∈ linearField) :
    ∃ (m : GL (Fin 3) F) (σ : F ≃+* F),
      a = linearConj F m * PSL3.OuterSolvable.fieldAction F σ := by
  have hn : (PSL3.OuterSolvable.fieldAction F).range ≤
      normalizer (innerDiagonal F) := by
    rintro _ ⟨σ, rfl⟩
    exact fieldAction_mem_normalizer_innerDiagonal σ
  change a ∈ (↑(innerDiagonal F ⊔ (PSL3.OuterSolvable.fieldAction F).range) : Set _) at ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at ha
  obtain ⟨_, ⟨m, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩ := ha
  exact ⟨m, σ, rfl⟩

private theorem standard_two_cosets (a : MulAut PSL) (ha : a ∈ standard F) :
    a ∈ linearField ∨ ∃ b ∈ linearField, a = b * graph F := by
  obtain ⟨m, σ, h | h⟩ := PSL3.CartanActions.NormalizerForm.standard_factorization F
    field_linearConj graph_linearConj_exists field_commute_graph a ha
  · exact Or.inl (h ▸ linear_mul_field_mem m σ)
  · exact Or.inr ⟨_, linear_mul_field_mem m σ, h⟩

/-- Every standard four-group has a nonidentity actor in the linear–field
subgroup, since there are at most two graph cosets. -/
theorem exists_nonidentity_linearField {A : Type*} [Group A] [IsKleinFour A]
    (ψ : A →* MulAut PSL) (hstandard : ∀ b : A, ψ b ∈ standard F) :
    ∃ a : A, a ≠ 1 ∧ ψ a ∈ linearField := by
  classical
  let : Finite A := Nat.finite_of_card_ne_zero (by simp)
  let : Fintype A := Fintype.ofFinite A
  have hc : 1 < ((Finset.univ : Finset A).erase 1).card := by simp
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
  have ha1 : a ≠ 1 := (Finset.mem_erase.mp ha).1
  have hb1 : b ≠ 1 := (Finset.mem_erase.mp hb).1
  rcases standard_two_cosets (ψ a) (hstandard a) with haK | ⟨x, hx, hax⟩
  · exact ⟨a, ha1, haK⟩
  rcases standard_two_cosets (ψ b) (hstandard b) with hbK | ⟨y, hy, hby⟩
  · exact ⟨b, hb1, hbK⟩
  refine ⟨a * b⁻¹, ?_, ?_⟩
  · exact fun h => hab (mul_inv_eq_one.mp h)
  · have he : ψ (a * b⁻¹) = x * y⁻¹ := by
      rw [map_mul, map_inv, hax, hby]
      group
    rw [he]
    exact linearField.mul_mem hx (linearField.inv_mem hy)

/-- An outer involution in the linear–field subgroup is conjugate to the
literal projective Frobenius. -/
theorem linearField_outer_involution_conjugate (a : MulAut PSL)
    (ha : a ∈ linearField) (ha2 : a ^ 2 = 1)
    (houter : a ∉ MulAut.innerSubgroup PSL) :
    ∃ d : MulAut PSL, MulAut.congr d a = pslFrobenius := by
  obtain ⟨m, σ, rfl⟩ := linearField_factorization a ha
  rcases coefficient_eq_one_or_frobenius σ with rfl | rfl
  · simp only [map_one, mul_one] at ha2 houter
    exact (houter (linear_involution_inner m ha2)).elim
  · rw [← frobenius_eq_fieldAction] at ha2 ⊢
    exact linear_frobenius_involution_conjugate m ha2

/-- Every standard outer four-group on the actual PSL₃(4) has a Frobenius
actor, up to an automorphism of that same projective quotient. -/
theorem exists_frobenius_actor {A : Type*} [Group A] [IsKleinFour A]
    (ψ : A →* MulAut PSL) (hstandard : ∀ b : A, ψ b ∈ standard F)
    (houter : ∀ b : A, b ≠ 1 → ψ b ∉ MulAut.innerSubgroup PSL) :
    ∃ a : A, a ≠ 1 ∧ ∃ d : MulAut PSL, MulAut.congr d (ψ a) = pslFrobenius := by
  obtain ⟨a, ha, haK⟩ := exists_nonidentity_linearField ψ hstandard
  refine ⟨a, ha, linearField_outer_involution_conjugate (ψ a) haK ?_ (houter a ha)⟩
  rw [← map_pow, pow_two, IsKleinFour.mul_self, map_one]

end Matrix.PSL3Four.OuterPlane.FieldOccurrence
