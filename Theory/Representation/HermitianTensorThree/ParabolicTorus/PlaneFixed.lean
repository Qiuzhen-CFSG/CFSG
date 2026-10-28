module
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.ActorFixed
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.OddSimilitudes

/-!
# Odd congruences on the Hermitian plane fixed space

The plane radical fixes the literal two-by-two Hermitian corner. A GL₃
congruence preserving this corner acts as a similitude of its determinant
form, with multiplier the norm of the upper-left block determinant.
Restriction preserves odd order. The four-dimensional minus form therefore
excludes a fixed space of dimension three. Cardinalities transfer this to
binary rank 3n and inner conjugacy transfers it to the selected actor.

Source: Aschbacher–Smith H.4.4(1,4), printed pp.380–381, used in
8.2.3, printed p.716 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
namespace Representation.HermitianTensorThree.ParabolicTorus
variable (n : ℕ) [NeZero n]
private theorem plane_le_image : UnipotentRadicals.plane n ≤ binaryImage n := by
  rintro _ ⟨a,ha,rfl⟩
  exact ⟨_,rfl⟩

private abbrev PlaneFixed := innerFixed n (UnipotentRadicals.plane n) (plane_le_image n)

private def planeCoordinates : PlaneFixed n ≃ₗ[F n] ((F n × F n) × E n) where
  toEquiv := UnipotentRadicals.planeFixedCoordinates n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def planeCorner : PlaneFixed n ≃ₗ[F n] OrthogonalFourMinus.FiniteModel.Space n :=
  (planeCoordinates n).trans (OrthogonalFourMinus.FiniteModel.coordinates n).symm

private theorem planeCorner_entry (v : PlaneFixed n) (i j : Fin 2) :
    (planeCorner n v).val i j = v.val.val i.castSucc j.castSucc := by
  fin_cases i <;> fin_cases j <;> try rfl
  exact entry_conjugate n v.val 1 0

private theorem plane_similarity
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n))
    (t : PlaneFixed n ≃ₗ[F n] PlaneFixed n)
    (ht : ∀ v, (t v).val = congruence n g v.val) :
    ∃ c : F n, ∀ v, OrthogonalFourMinus.FiniteModel.form n (planeCorner n (t v)) =
      c * OrthogonalFourMinus.FiniteModel.form n (planeCorner n v) := by
  let b : Matrix (Fin 2) (Fin 2) (E n) := g.val.submatrix Fin.castSucc Fin.castSucc
  refine ⟨OrthogonalFourMinus.FiniteModel.norm n b.det,?_⟩
  intro v
  have hm : (planeCorner n (t v)).val = b * (planeCorner n v).val * (b.transpose.map (sigma n)) := by
    obtain ⟨h22,h12,h02⟩ := (UnipotentRadicals.mem_plane_fixed_iff n v.val).mp v.property
    have hc (i : Fin 3) : v.val.val i 2 = 0 := by
      fin_cases i <;> assumption
    have hr (i : Fin 3) : v.val.val 2 i = 0 := by
      rw [← entry_conjugate n v.val 2 i,hc,map_zero]
    ext i j
    rw [planeCorner_entry,ht]
    change (g.val * v.val.val * adjoint n g.val) i.castSucc j.castSucc = _
    simp only [Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two,
      planeCorner_entry,Matrix.map_apply,Matrix.transpose_apply,
      b,Matrix.submatrix_apply,adjoint,hc,hr,zero_mul,mul_zero,add_zero]
    rfl
  apply Subtype.ext
  change (planeCorner n (t v)).val.det = (b.det * sigma n b.det) * (planeCorner n v).val.det
  have hb : (b.transpose.map (sigma n)).det = sigma n b.det := by
    exact ((sigma n).map_det b.transpose).symm.trans (congrArg (sigma n) b.det_transpose)
  rw [hm,Matrix.det_mul,Matrix.det_mul,hb]
  ring

/-- An odd congruence normalizing the actual plane radical cannot have
all its fixed vectors in the plane fixed space with binary rank 3n. -/
theorem plane_no_fixed_rank_three_mul
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (ho : Odd (orderOf g))
    (hn : binaryCongruence n g ∈ normalizer (UnipotentRadicals.plane n : Set (BinaryAut n)))
    (hle : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g)) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n))
    (hd : finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n)
      (zpowers (binaryCongruence n g))) = 3*n) : False := by
  let U := PlaneFixed n
  let e := planeCorner n
  have hs := fixedSpace_stable_of_normalizes (UnipotentRadicals.ambientAction n)
    (L := UnipotentRadicals.plane n) le_rfl
  let t : U ≃ₗ[F n] U :=
    { toFun := fun v => ⟨congruence n g v.val, (hs hn v.val).2 v.property⟩
      invFun := fun v => ⟨(congruence n g).symm v.val, (hs (inv_mem hn) v.val).2 v.property⟩
      left_inv := fun v => Subtype.ext ((congruence n g).symm_apply_apply v.val)
      right_inv := fun v => Subtype.ext ((congruence n g).apply_symm_apply v.val)
      map_add' := fun v w => Subtype.ext ((congruence n g).map_add v.val w.val)
      map_smul' := fun a v => Subtype.ext ((congruence n g).map_smul a v.val) }
  have ht (v : U) : (t v).val = congruence n g v.val := rfl
  have hp (m : ℕ) (v : U) : ((t^m) v).val = ((congruence n g)^m) v.val := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ',pow_succ']
      change (congruence n g) (((t^m) v).val) = (congruence n g) (((congruence n g)^m) v.val)
      rw [ih]
  have htord : t ^ orderOf g = 1 := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [hp]
    have hh : (congruence n g)^orderOf g = 1 := by
      change (congruenceHom n g)^orderOf g = 1
      rw [← map_pow,pow_orderOf_eq_one,map_one]
    rw [hh]
    rfl
  have hto : Odd (orderOf t) := ho.of_dvd_nat (orderOf_dvd_of_pow_eq_one htord)
  let f : (U ≃ₗ[F n] U) →* (OrthogonalFourMinus.FiniteModel.Space n ≃ₗ[F n]
      OrthogonalFourMinus.FiniteModel.Space n) :=
    { toFun := fun a => e.symm.trans (a.trans e)
      map_one' := by
        apply LinearEquiv.ext
        intro v
        exact e.apply_symm_apply v
      map_mul' := fun a b => by
        apply LinearEquiv.ext
        intro v
        change e (a (b (e.symm v))) = e (a (e.symm (e (b (e.symm v)))))
        rw [e.symm_apply_apply] }
  let t' := f t
  have hto' : Odd (orderOf t') := hto.of_dvd_nat (orderOf_map_dvd f t)
  obtain ⟨c,hc⟩ := plane_similarity n g t ht
  have hc' (v : OrthogonalFourMinus.FiniteModel.Space n) :
      OrthogonalFourMinus.FiniteModel.form n (t' v) =
        c * OrthogonalFourMinus.FiniteModel.form n v := by
    have hh := hc (e.symm v)
    change OrthogonalFourMinus.FiniteModel.form n (e (t (e.symm v))) =
      c * OrthogonalFourMinus.FiniteModel.form n (e (e.symm v)) at hh
    rw [e.apply_symm_apply] at hh
    exact hh
  let K := LinearMap.ker (t'.toLinearMap - LinearMap.id)
  let X := fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g))
  let j : K → X := fun v => ⟨(e.symm v.val).val, by
    apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
    have hv : e (t (e.symm v.val)) = v.val := sub_eq_zero.mp v.property
    have hu : t (e.symm v.val) = e.symm v.val := e.injective (hv.trans (e.apply_symm_apply _).symm)
    exact congrArg Subtype.val hu⟩
  have hj : Function.Bijective j := by
    constructor
    · intro v w hvw
      apply Subtype.ext
      apply e.symm.injective
      apply Subtype.ext
      exact congrArg (fun z : X => z.val) hvw
    · intro v
      let u : U := ⟨v.val,hle v.property⟩
      have hu : t u = u := Subtype.ext ((mem_fixedSpace_zpowers_iff _ _ _).mp v.property)
      refine ⟨⟨e u,?_⟩,?_⟩
      · change e (t (e.symm (e u))) - e u = 0
        rw [e.symm_apply_apply,hu,sub_self]
      · apply Subtype.ext
        change (e.symm (e u)).val = v.val
        rw [e.symm_apply_apply]
  have hcard := Module.natCard_eq_pow_finrank (K := F n) (V := K)
  rw [card_F,← pow_mul,Nat.card_congr (Equiv.ofBijective j hj),
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd] at hcard
  have hr : finrank (F n) K = 3 := by
    have hh := Nat.pow_right_injective (by decide : 2 ≤ 2) hcard
    apply Nat.eq_of_mul_eq_mul_left (NeZero.pos n)
    omega
  exact OrthogonalFourMinus.FiniteModel.no_three_dimensional_fixed_similitude n t' c hc' hto' hr
/-- Transport the actual plane calculation through an inner conjugacy. -/
theorem conjugate_plane_no_fixed_rank_three_mul
    (A : Subgroup (BinaryAut n)) (c : Cover n)
    (hc : A.map (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n)
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (ho : Odd (orderOf g))
    (hn : binaryCongruence n g ∈ normalizer (A : Set (BinaryAut n)))
    (hle : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g)) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) A)
    (hd : finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n)
      (zpowers (binaryCongruence n g))) = 3*n) : False := by
  let u := binaryActionHom n c
  let f := (MulAut.conj u).toMonoidHom
  let g' := (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)) g
  have hg : binaryCongruence n g' = f (binaryCongruence n g) := by
    change binaryCongruence n (Matrix.SpecialLinearGroup.toGL c * g *
      (Matrix.SpecialLinearGroup.toGL c)⁻¹) = _
    rw [map_mul,map_mul,map_inv,binaryCongruence_toGL]
    rfl
  have hn' : binaryCongruence n g' ∈ normalizer (UnipotentRadicals.plane n : Set (BinaryAut n)) := by
    rw [hg,←hc]
    exact A.le_normalizer_map f (mem_map_of_mem f hn)
  have he (a : BinaryAut n) (v : Space n) :
      u (UnipotentRadicals.ambientAction n a v) =
        UnipotentRadicals.ambientAction n (f a) (u v) := by
    change u (a v) = (u * a * u⁻¹) (u v)
    change u (a v) = u (a (u.symm (u v)))
    rw [u.symm_apply_apply]
  have hm (B : Subgroup (BinaryAut n)) := fixedSpace_map_equivariant
    (UnipotentRadicals.ambientAction n) (UnipotentRadicals.ambientAction n) f u he B
  have hz : (zpowers (binaryCongruence n g)).map f = zpowers (binaryCongruence n g') := by
    rw [MonoidHom.map_zpowers,hg]
  have hle' : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g')) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n) := by
    rw [←hz,←hc,←hm,←hm]
    exact Submodule.map_mono hle
  have hd' : finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n)
      (zpowers (binaryCongruence n g'))) = 3*n := by
    rw [←hz,←hm,LinearEquiv.finrank_map_eq,hd]
  have ho' : Odd (orderOf g') := by
    have hh := orderOf_injective (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)).toMonoidHom
      (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)).injective g
    exact hh.symm ▸ ho
  exact plane_no_fixed_rank_three_mul n g' ho' hn' hle' hd'
end Representation.HermitianTensorThree.ParabolicTorus

end
