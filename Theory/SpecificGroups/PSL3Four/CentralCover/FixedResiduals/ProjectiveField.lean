module

public import Theory.GroupAction.CentralKernelFixedResidual
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The projective field fixed subgroup of PSL₃(4)

The fixed subgroup of entrywise squaring on the actual projective quotient
is PSL₃(2). Binary coefficient inclusion identifies SL₃(2) with the fixed
matrices. A projective fixed point represented by x has displacement
k = x⁻¹F(x) in the scalar center, so k³ = 1 and xk² is fixed. The only
fixed scalar of determinant one is 1, proving that projectivization is an
isomorphism on these fixed subgroups.

Elementary-matrix perfectness of PSL₃(2) then identifies its two-residual
with the whole fixed subgroup. This is the projective calculation for
Aschbacher--Smith 15.3.38, printed p.1137 (1 March 2004 manuscript).
Lifting it to the perfect four-cover still requires the separate proof
that the residual projection has trivial kernel. Perfectness is reused
from the attributed ATLAS port `ExceptionalIsomorphisms.Elementary`.
-/

public section

namespace Matrix.PSL3Four
noncomputable section

private abbrev binaryCast : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F

private theorem binaryCast_fixed (x : ZMod 2) : fieldFrobenius (binaryCast x) = binaryCast x := by
  have h : x = 0 ∨ x = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x
  rcases h with rfl | rfl <;> simp

private theorem exists_binaryCast_of_fixed (x : F) (hx : fieldFrobenius x = x) :
    ∃ y : ZMod 2, binaryCast y = x := by
  have hxx : x * (x - 1) = 0 := by
    calc
      x * (x - 1) = x ^ 2 - x := by ring
      _ = 0 := sub_eq_zero.mpr hx
  rcases mul_eq_zero.mp hxx with h | h
  · exact ⟨0, by simpa using h.symm⟩
  · exact ⟨1, by simpa using (sub_eq_zero.mp h).symm⟩

private def binaryFixedHom : PSL3Two.SL →* slFrobenius.fixedSubgroup :=
  (SpecialLinearGroup.map binaryCast).codRestrict _ (by
    intro g
    rw [MulAut.mem_fixedSubgroup]
    ext i j
    exact binaryCast_fixed (g i j))

private theorem binaryFixedHom_injective : Function.Injective binaryFixedHom := by
  intro x y h
  apply SpecialLinearGroup.ext
  intro i j
  apply binaryCast.injective
  exact congrArg (fun z : slFrobenius.fixedSubgroup => z.val i j) h

private theorem binaryFixedHom_surjective : Function.Surjective binaryFixedHom := by
  intro x
  have hx (i j : Fin 3) : ∃ y : ZMod 2, binaryCast y = x.val i j := by
    apply exists_binaryCast_of_fixed
    exact congrArg (fun z : SL => z i j) ((MulAut.mem_fixedSubgroup _ _).mp x.property)
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun i j => Classical.choose (hx i j)
  have hM (i j : Fin 3) : binaryCast (M i j) = x.val i j := Classical.choose_spec (hx i j)
  have hd : Matrix.det M = 1 := by
    apply binaryCast.injective
    rw [binaryCast.map_det, map_one]
    have he : Matrix.map M binaryCast = x.val.val := by ext i j; exact hM i j
    change (Matrix.map M binaryCast).det = 1
    rw [he]
    exact x.val.property
  refine ⟨⟨M, hd⟩, ?_⟩
  apply Subtype.ext
  apply SpecialLinearGroup.ext
  exact hM

private def fieldFixedProjection : slFrobenius.fixedSubgroup →* pslFrobenius.fixedSubgroup :=
  MulAut.fixedSubgroupMap slFrobenius pslFrobenius
    (QuotientGroup.mk' (Subgroup.center SL)) (fun x => (pslFrobenius_mk x).symm)

private theorem central_cube (g : SL) (hg : g ∈ Subgroup.center SL) : g ^ 3 = 1 := by
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  have hr' : r ^ 3 = 1 := hr
  apply Subtype.ext
  change g.val ^ 3 = (1 : Matrix (Fin 3) (Fin 3) F)
  rw [← he]
  change (Matrix.diagonal (fun _ : Fin 3 => r)) ^ 3 = _
  simp only [Matrix.diagonal_pow]
  congr 1
  funext i
  exact hr'

private theorem fieldFixedProjection_surjective : Function.Surjective fieldFixedProjection := by
  intro b
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) b.val
  let k := x⁻¹ * slFrobenius x
  have hk : (QuotientGroup.mk' (Subgroup.center SL)) k = 1 := by
    dsimp only [k]
    rw [map_mul, map_inv]
    change (QuotientGroup.mk' _ x)⁻¹ * pslFrobenius (QuotientGroup.mk' _ x) = 1
    rw [hx, (MulAut.mem_fixedSubgroup _ _).mp b.property, inv_mul_cancel]
  have hk3 : k ^ 3 = 1 := central_cube k ((QuotientGroup.eq_one_iff k).mp hk)
  have hki : k⁻¹ = k ^ 2 := by
    calc
      k⁻¹ = k⁻¹ * (k * k ^ 2) := by rw [← pow_succ', hk3, mul_one]
      _ = k ^ 2 := by group
  have hck : slFrobenius k = k⁻¹ := by
    simp [k, map_mul, map_inv]
  have hcx : slFrobenius x = x * k := by simp [k]
  have hz : slFrobenius (x * k ^ 2) = x * k ^ 2 := by
    rw [map_mul, map_pow, hck, hcx]
    calc
      x * k * (k⁻¹) ^ 2 = x * k⁻¹ := by group
      _ = x * k ^ 2 := by rw [hki]
  refine ⟨⟨x * k ^ 2, (MulAut.mem_fixedSubgroup _ _).mpr hz⟩, ?_⟩
  apply Subtype.ext
  change (QuotientGroup.mk' _) (x * k ^ 2) = b.val
  simp [map_mul, map_pow, hk, hx]

private theorem fieldFixedProjection_injective : Function.Injective fieldFixedProjection := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hx' : x.val ∈ Subgroup.center SL := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun z : pslFrobenius.fixedSubgroup => z.val) hx
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hx'
  have hrfix : fieldFrobenius r = r := by
    have h := congrArg (fun z : SL => z 0 0)
      ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    change fieldFrobenius (x.val.val 0 0) = x.val.val 0 0 at h
    simpa [← he] using h
  obtain ⟨y, hy⟩ := exists_binaryCast_of_fixed r hrfix
  have hy3 : y ^ 3 = 1 := by
    apply binaryCast.injective
    rw [map_pow, map_one, hy]
    exact hr
  have hy1 : y = 1 := (by decide : ∀ y : ZMod 2, y ^ 3 = 1 → y = 1) y hy3
  have hr1 : r = 1 := by rw [← hy, hy1, map_one]
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Subtype.ext
  rw [← he, hr1]
  simp

/-- Frobenius-fixed projective matrices are the actual binary projective group. -/
noncomputable def projectiveFieldFixedEquiv :
    pslFrobenius.fixedSubgroup ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (MulEquiv.ofBijective fieldFixedProjection
    ⟨fieldFixedProjection_injective, fieldFixedProjection_surjective⟩).symm.trans
    ((MulEquiv.ofBijective binaryFixedHom
      ⟨binaryFixedHom_injective, binaryFixedHom_surjective⟩).symm.trans PSL3Two.equiv)

private theorem fieldFixed_twoPerfect : IsPPerfect 2 pslFrobenius.fixedSubgroup := by
  let e := projectiveFieldFixedEquiv
  let := Atlas.psl_perfect (F := ZMod 2) 3 (by decide)
  have hp : IsPPerfect 2 (ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
    intro N hN h
    let := hN
    have hs : Subsingleton (ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ h.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  exact hp.of_surjective e.symm.toMonoidHom e.symm.surjective

/-- The projective field fixed-subgroup two-residual is PSL₃(2). -/
noncomputable def projectiveFieldResidualEquiv :
    pResidual 2 pslFrobenius.fixedSubgroup ≃*
      ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (MulEquiv.subgroupCongr ((pResidual_eq_top_iff 2 _).mpr fieldFixed_twoPerfect)).trans
    ((Subgroup.topEquiv).trans projectiveFieldFixedEquiv)

end
end Matrix.PSL3Four
