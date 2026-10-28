module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
public import Theory.SpecificGroups.PSL3Four.OuterPlane.FieldOccurrence
public import Theory.SpecificGroups.PSL3.SplitPrimeActors.Reduction

/-!
# Marked index-two linear–field extensions of PSL₃(4)

The native field extension acts faithfully on PSL₃(4). For an automorphism
subgroup of order 40320 containing all inner automorphisms, a noninner element
fixing both parabolics has a nontrivial coefficient part: its square is inner,
whereas the diagonal outer part has order dividing three. Conjugating by its
linear factor removes that diagonal part without moving either parabolic.
The resulting automorphism subgroup is exactly the native field-extension image.

Source: Aschbacher–Smith 5.2.16(2), printed p.655 (`refs/quasithin.pdf`),
using the concrete automorphism calculations of GLS3, §2.5 and §2.7.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.GroupTheory.QuasithinM23.LinearExtension
open Matrix Matrix.PSL3Four
open Matrix.PSL3.OuterSolvable

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
    rw [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card] at h
    have hd : Module.finrank (ZMod 2) F = 2 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
      rw [Nat.card_zmod,card_F] at hh
      have hh' : (2:ℕ)^2 = 2 ^ Module.finrank (ZMod 2) F := hh
      exact (Nat.pow_right_injective (by decide : 1 < 2) hh').symm
    rwa [hd] at h
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


private theorem frobenius_not_inner : pslFrobenius ∉ MulAut.innerSubgroup PSL := by
  intro h
  rw [frobenius_eq_fieldAction] at h
  have hh := PSL3.SplitPrimeActors.field_eq_one_of_inner fieldFrobenius h
  obtain ⟨x,hx⟩ := exists_fieldFrobenius_ne
  exact hx (congrArg (fun a : F ≃+* F => a x) hh)

/-- The field extension acts faithfully by its literal inner and coefficient actors. -/
def fieldAut : FieldExtension →* MulAut PSL :=
  SemidirectProduct.lift MulAut.conj Matrix.PSL3Four.fieldAction (by
    intro t
    ext x y
    simp [MulAut.conj_apply])

private theorem conj_injective : Function.Injective (MulAut.conj : PSL →* MulAut PSL) := by
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  exact MulAut.conj_injective_of_center_eq_bot
    (Group.IsPerfect.center_quotient_center_eq_bot SL)

theorem fieldAut_injective : Function.Injective fieldAut := by
  apply fieldAut.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro z hz
  have hz' : MulAut.conj z.left * Matrix.PSL3Four.fieldAction z.right = 1 := hz
  have hr : z.right = 1 := by
    by_contra hn
    have ht : z.right = Multiplicative.ofAdd (1 : ZMod 2) := by
      have hh : ∀ u : C2, u ≠ 1 → u = Multiplicative.ofAdd (1 : ZMod 2) := by
        intro u hn
        change u.toAdd ≠ (0 : ZMod 2) at hn
        change u.toAdd = (1 : ZMod 2)
        have hh : ∀ v : ZMod 2, v ≠ 0 → v = 1 := by decide
        exact hh u.toAdd hn
      exact hh z.right hn
    rw [ht,Matrix.PSL3Four.fieldAction_generator] at hz'
    apply frobenius_not_inner
    rw [eq_inv_of_mul_eq_one_right hz']
    exact (MulAut.innerSubgroup PSL).inv_mem ⟨z.left,rfl⟩
  have hl : z.left = 1 := conj_injective (by simpa [hr] using hz')
  exact SemidirectProduct.ext hl hr

theorem fieldAut_linear (x : PSL) : fieldAut (linearInclusion x) = MulAut.conj x := by
  change MulAut.conj x * Matrix.PSL3Four.fieldAction 1 = _
  rw [map_one,mul_one]

theorem fieldAut_field (t : C2) : fieldAut (fieldInclusion t) = Matrix.PSL3Four.fieldAction t := by
  change MulAut.conj 1 * Matrix.PSL3Four.fieldAction t = _
  rw [map_one,one_mul]

private theorem inner_le_fieldAut : MulAut.innerSubgroup PSL ≤ fieldAut.range := by
  rintro _ ⟨x,rfl⟩
  exact ⟨linearInclusion x,fieldAut_linear x⟩

private theorem fieldAut_card : Nat.card fieldAut.range = 40320 :=
  (Nat.card_congr (MonoidHom.ofInjective fieldAut_injective).toEquiv).symm.trans card_FieldExtension

private theorem congr_inner (d : MulAut PSL) :
    (MulAut.innerSubgroup PSL).map (MulAut.congr d).toMonoidHom = MulAut.innerSubgroup PSL := by
  ext a
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    refine ⟨d x,?_⟩
    ext y
    simp [MulAut.congr_apply,MulAut.conj_apply]
  · rintro ⟨x,rfl⟩
    refine ⟨MulAut.conj (d.symm x),⟨d.symm x,rfl⟩,?_⟩
    ext y
    simp [MulAut.congr_apply,MulAut.conj_apply]

/-- An index-two extension with a marked type-preserving actor is the actual
field extension, after an automorphism fixing both marked parabolics. -/
theorem marked_range
    (A : Subgroup (MulAut PSL)) (hI : MulAut.innerSubgroup PSL ≤ A)
    (hc : Nat.card A = 40320) (a : MulAut PSL) (ha : a ∈ A)
    (hout : a ∉ MulAut.innerSubgroup PSL)
    (hP : ∀ b : Bool, (PSL3.RootPlaneGeometry.parabolic F b).map a.toMonoidHom =
      PSL3.RootPlaneGeometry.parabolic F b) :
    ∃ d : MulAut PSL,
      (∀ b : Bool, (PSL3.RootPlaneGeometry.parabolic F b).map d.toMonoidHom =
        PSL3.RootPlaneGeometry.parabolic F b) ∧
      A.map (MulAut.congr d).toMonoidHom = fieldAut.range := by
  have hcardI : Nat.card (MulAut.innerSubgroup PSL) = 20160 :=
    (Nat.card_congr (MonoidHom.ofInjective conj_injective).toEquiv).symm.trans card_PSL
  have hindex : ((MulAut.innerSubgroup PSL).subgroupOf A).index = 2 := by
    have hh := ((MulAut.innerSubgroup PSL).subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hI).toEquiv,hcardI,hc] at hh
    omega
  have hasq : a^2 ∈ MulAut.innerSubgroup PSL :=
    ((MulAut.innerSubgroup PSL).subgroupOf A).sq_mem_of_index_two hindex ⟨a,ha⟩
  have hlinear : a ∈ PSL3.ExtensionBorel.linearField F :=
    (PSL3.LinearThree.OuterExtensions.mapsParabolicType_self_iff_mem_linearField
      F (n:=2) (by decide) card_F a true).mp ⟨1,by
        rw [map_one]
        change _ = (PSL3.RootPlaneGeometry.parabolic F true).map (MonoidHom.id _)
        rw [Subgroup.map_id]
        exact hP true⟩
  obtain ⟨m,σ,heq⟩ := PSL3.ExtensionBorel.linearField_factorization F a hlinear
  have hσ : σ = fieldFrobenius := by
    rcases coefficient_eq_one_or_frobenius σ with hs | hs
    · have ham : a = linearConj F m := by simpa [hs] using heq
      have hcube : a^3 ∈ MulAut.innerSubgroup PSL :=
        ham ▸ PSL3.CartanActions.ResidualInner.linearConj_cube_inner m
      have hh := (MulAut.innerSubgroup PSL).mul_mem hcube
        ((MulAut.innerSubgroup PSL).inv_mem hasq)
      apply False.elim
      apply hout
      convert hh using 1
      group
    · exact hs
  rw [hσ,←frobenius_eq_fieldAction] at heq
  let d := linearConj F m
  have hd (b : Bool) : (PSL3.RootPlaneGeometry.parabolic F b).map d.toMonoidHom =
      PSL3.RootPlaneGeometry.parabolic F b := by
    have h := hP b
    rw [heq] at h
    change (PSL3.RootPlaneGeometry.parabolic F b).map
      (d.toMonoidHom.comp pslFrobenius.toMonoidHom) = _ at h
    rw [←Subgroup.map_map] at h
    rw [frobenius_eq_fieldAction,
      PSL3.LinearThree.OuterExtensions.field_map_parabolic] at h
    exact h
  obtain ⟨x,hx⟩ := OuterPlane.FieldOccurrence.linear_frobenius_conjugate_inner m
  have hx' : MulAut.congr d a = MulAut.conj x * pslFrobenius := by rw [heq]; exact hx
  let A' := A.map (MulAut.congr d).toMonoidHom
  have hI' : MulAut.innerSubgroup PSL ≤ A' := by
    rw [←congr_inner d]
    exact map_mono hI
  have hf : pslFrobenius ∈ A' := by
    have hh := A'.mul_mem (A'.inv_mem (hI' ⟨x,rfl⟩))
      (mem_map_of_mem (MulAut.congr d).toMonoidHom ha)
    change (MulAut.conj x)⁻¹ * MulAut.congr d a ∈ A' at hh
    rw [hx',inv_mul_cancel_left] at hh
    exact hh
  have hle : fieldAut.range ≤ A' := by
    rintro _ ⟨z,rfl⟩
    apply A'.mul_mem (hI' ⟨z.left,rfl⟩)
    change Matrix.PSL3Four.fieldAction z.right ∈ A'
    change pslFrobenius ^ z.right.toAdd.val ∈ A'
    exact A'.pow_mem hf _
  refine ⟨d,hd,(eq_of_le_of_card_ge hle ?_).symm⟩
  rw [fieldAut_card]
  change Nat.card (A.map (MulAut.congr d).toMonoidHom) ≤ 40320
  rw [card_map_of_injective (MulAut.congr d).injective,hc]

end Theory.GroupTheory.QuasithinM23.LinearExtension
