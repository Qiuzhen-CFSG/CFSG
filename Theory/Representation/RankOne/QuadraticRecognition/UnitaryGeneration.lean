module
public import Theory.Representation.RankOne.QuadraticRecognition.SL2PairGeneration
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots

/-!
# Generation by small central-root actors in binary unitary groups

Any subgroup A of the central root with |A|≥4 has three conjugates generating
SU₃(q), for every q=2ⁿ>2. The binary SL₂ pair theorem makes two conjugates
contain the entire fixed-field block. A third conjugate contributes one
transvection which, together with an element of that block, connects its two
orbits on isotropic lines. Transitivity and the actual quasisimple root
normal-closure theorem then give the whole special unitary group.

The projective theorem lifts the given actor through the injected fixed-field
block. Its order is preserved, and mapping the three conjugates down gives
PSU₃ itself. The full root/block generation used by the torus argument is
proved separately with the same coordinates.

This proves the binary |A|≥4 branch of DGS85, Groups and Graphs, (5.4)(f),
printed p.107, required on p.112 in the proof of (5.10)(b). UnitaryActorDegree
uses the three-conjugate result to bound the actual actor fixed codimension.
The Hermitian field, form, and full special-to-projective quotient are retained.
-/

public noncomputable section
open Matrix Subgroup Representation.BinaryOffender
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus.EvenCenterAction
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 3 F)
  (hJ : J.form=!![0,0,1;0,1,0;1,0,0])

private theorem block_injective : Function.Injective (block J hJ) :=
  (J.specialGraphAut hJ).fixedSubgroup.subtype_injective.comp
    (J.specialGraphFixedEquivSL2 hJ).symm.injective

private theorem block_upper_image :
    (SpecialLinearGroup.upperUnipotent (fixedField J)).map (block J hJ) =
      central J hJ := by
  have he (c : fixedField J) :
      block J hJ (SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one c) =
        hermitianUnipotentSU J hJ
          (centralCoord J (Multiplicative.ofAdd c)) := by
    apply Subtype.ext
    apply Units.ext
    rw [block_val]
    change _ = (!![1, 0, (c : F); 0, 1, -J.conj 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe]
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent _ _).mp ha
    rw [he]
    exact ⟨Multiplicative.ofAdd c, rfl⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨SpecialLinearGroup.transvection zero_ne_one c.toAdd, ?_, ?_⟩
    · exact (SpecialLinearGroup.mem_upperUnipotent _ _).mpr ⟨c.toAdd, rfl⟩
    · exact he c.toAdd

private theorem projective_block_injective :
    Function.Injective (J.specialToProjective.comp (block J hJ)) := by
  intro x y h
  have hp : ProjGenLinGroup.mk (block J hJ x).val =
      ProjGenLinGroup.mk (block J hJ y).val := by
    simpa only [MonoidHom.comp_apply, J.specialToProjective_apply_val] using
      congrArg Subtype.val h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have huval : (u : F) = 1 := by
    have hh := congrArg (fun g : GL (Fin 3) F => g.val 1 1) hu
    rw [GeneralLinearGroup.coe_mul, block_val, block_val] at hh
    simpa [GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.scalar] using hh
  have huone : u = 1 := Units.ext huval
  rw [huone, map_one, mul_one] at hu
  exact block_injective J hJ (Subtype.ext hu)

private theorem projective_block_upper_image :
    (SpecialLinearGroup.upperUnipotent (fixedField J)).map
        (J.specialToProjective.comp (block J hJ)) = centralImage J hJ := by
  rw [← Subgroup.map_map, block_upper_image]
  change (((hermitianUnipotentSU J hJ).comp (centralCoord J)).range).map
      J.specialToProjective = _
  rw [MonoidHom.map_range]
  have he : J.specialToProjective.comp
        ((hermitianUnipotentSU J hJ).comp (centralCoord J)) = centralMap J hJ := by
    apply MonoidHom.ext
    intro c
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, J.specialToProjective_apply_val]
    change ProjGenLinGroup.mk _ =
      (hermitianUnipotentPSU J hJ (centralCoord J c)).val
    exact (hermitianUnipotentPSU_val J hJ (centralCoord J c)).symm
  rw [he]
  rfl


private theorem central_le_block : central J hJ ≤ (block J hJ).range := by
  rw [←block_upper_image]
  exact map_le_range _ _

private theorem central_one_block :
    block J hJ (SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one
      (1 : fixedField J)) =
      hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd 1)) := by
  apply Subtype.ext
  apply Units.ext
  rw [block_val]
  change _ = (!![1,0,1;0,1,-J.conj 0;0,0,1] : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]

variable [Finite F]

private theorem central_involution_conjugate_one
    (a : J.specialSubgroup) (ha : a ∈ central J hJ) (ha1 : a≠1) :
    ∃ c : J.specialSubgroup, c*a*c⁻¹=
      hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd 1)) := by
  obtain ⟨a₀,ha₀,rfl⟩ := (block_upper_image J hJ).symm ▸ ha
  let t : SL(2,fixedField J) := SpecialLinearGroup.transvection zero_ne_one 1
  have ht : t≠1 := by
    intro he
    have hh := congrArg (fun x : SL(2,fixedField J) => x 0 1) he
    simp [t,SpecialLinearGroup.transvection_coe] at hh
  have ha₀1 : a₀≠1 := fun he => ha1 (by rw [he,map_one])
  have htwo (b : SL(2,fixedField J)) (hb : b ∈ SpecialLinearGroup.upperUnipotent (fixedField J)) :
      b^2=1 := by
    have hh := SpecialLinearGroup.twoSubgroup_pow_two
      (SpecialLinearGroup.upperUnipotent (fixedField J))
      (SpecialLinearGroup.upperUnipotentSylow (fixedField J) 2).isPGroup' ⟨b,hb⟩
    exact congrArg Subtype.val hh
  have htmem : t ∈ SpecialLinearGroup.upperUnipotent (fixedField J) :=
    (SpecialLinearGroup.mem_upperUnipotent _ _).mpr ⟨1,rfl⟩
  let e := Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (fixedField J)
  have hc := Theory.PSL2.involutions_isConj (e a₀) (e t)
    ((e.orderOf_eq a₀).trans (orderOf_eq_prime (htwo a₀ ha₀) ha₀1))
    ((e.orderOf_eq t).trans (orderOf_eq_prime (htwo t htmem) ht))
  have hh : IsConj a₀ t := by
    simpa only [MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using
      e.symm.toMonoidHom.map_isConj hc
  obtain ⟨c,hc⟩ := isConj_iff.mp hh
  refine ⟨block J hJ c,?_⟩
  rw [←map_inv,←map_mul,←map_mul,hc]
  exact central_one_block J hJ

omit [Finite F] in
private theorem connector_in_subgroup
    (b : F) (hb : b+J.conj b=1) (H : Subgroup J.specialSubgroup)
    (hz : hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd 1)) ∈ H)
    (htz : thirdConjugator J hJ b hb *
      hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd 1)) *
      (thirdConjugator J hJ b hb)⁻¹ ∈ H) :
    ∃ g ∈ H, ∀ i, g.val.val i 0=(![b,1,1] : Fin 3 → F) i := by
  let z := hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd 1))
  let t := thirdConjugator J hJ b hb
  refine ⟨z*(t*z*t⁻¹),H.mul_mem hz htz,?_⟩
  have hzval : z.val.val = !![1,0,1;0,1,0;0,0,1] := by
    change (!![1,0,1;0,1,-J.conj 0;0,0,1] : Matrix (Fin 3) (Fin 3) F) = _
    simp
  have hw : (hermitianWeylSU J hJ)⁻¹=hermitianWeylSU J hJ := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianWeylSU,hermitianWeylGL,hermitianWeylMatrix,Matrix.mul_apply,Fin.sum_univ_three]
  have hs : (seed J hJ b hb)⁻¹.val.val = !![1,1,J.conj b;0,1,1;0,0,1] := by
    change ((hermitianUnipotentSU J hJ) _)⁻¹.val.val = _
    rw [←map_inv]
    change hermitianUnipotentMatrix J _ = _
    change (!![1,-1,J.conj b;0,1,-J.conj (-1);0,0,1] : Matrix (Fin 3) (Fin 3) F) = _
    simp [CharTwo.neg_eq]
  have ht : t⁻¹=hermitianWeylSU J hJ*(seed J hJ b hb)⁻¹ := by
    dsimp [t,thirdConjugator]
    rw [_root_.mul_inv_rev,hw]
  intro i
  rw [ht]
  change (z.val.val*(((seed J hJ b hb).val.val*(hermitianWeylSU J hJ).val.val)*
    z.val.val*((hermitianWeylSU J hJ).val.val*(seed J hJ b hb)⁻¹.val.val))) i 0 = _
  rw [hzval,seed_val,hs]
  fin_cases i <;> simp [hermitianWeylSU,hermitianWeylGL,hermitianWeylMatrix,
    Matrix.mul_apply,Fin.sum_univ_three,CharTwo.neg_eq,add_assoc,CharTwo.add_self_eq_zero]


/-- Three conjugates of every central-root actor of order at least four
 generate the actual special unitary group. -/
theorem su3_root_three_conjugates
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (A : Subgroup J.specialSubgroup) (hA : A≤central J hJ) (hAc : 4≤Nat.card A) :
    ∃ g h : J.specialSubgroup,
      A ⊔ A.map (MulAut.conj g).toMonoidHom ⊔ A.map (MulAut.conj h).toMonoidHom=⊤ := by
  let j := block J hJ
  let B := A.comap j
  have hAr : A≤j.range := hA.trans (central_le_block J hJ)
  have hBA : B.map j=A := map_comap_eq_self hAr
  have hBS : B≤SpecialLinearGroup.upperUnipotent (fixedField J) := by
    apply (comap_mono (hA.trans (block_upper_image J hJ).symm.le)).trans
    exact (comap_map_eq_self_of_injective (block_injective J hJ) _).le
  have hBc : 4≤Nat.card B := by rw [←hBA,card_map_of_injective (block_injective J hJ)] at hAc; exact hAc
  have hBne : B≠⊥ := by intro he; simp [he] at hBc
  obtain ⟨a₀,ha₀,ha₀1⟩ := B.bot_or_exists_ne_one.resolve_left hBne
  have hF : Nat.card (fixedField J)=2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨g,hg⟩ := sl2_exists_quadratic_pair (by omega) hF
    (SpecialLinearGroup.upperUnipotentSylow (fixedField J) 2) B hBS hBc a₀ ha₀ ha₀1
  have hblock : j.range≤A ⊔ A.map (MulAut.conj (j g)).toMonoidHom := by
    have hh := congrArg (Subgroup.map j) hg
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map] at hh
    rw [←hh]
    apply sup_le
    · exact map_mono (zpowers_le.mpr ha₀) |>.trans hBA.le |>.trans le_sup_left
    · rintro _ ⟨_,⟨a,ha,rfl⟩,rfl⟩
      apply (show A.map (MulAut.conj (j g)).toMonoidHom≤_ from le_sup_right)
      refine ⟨j a,ha,?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,map_mul,map_inv]
  have ha1 : j a₀≠1 := fun he => ha₀1 ((block_injective J hJ) (he.trans j.map_one.symm))
  obtain ⟨c,hc⟩ := central_involution_conjugate_one J hJ (j a₀) (hA ha₀) ha1
  have hf : Nat.card {x : F // J.conj x=x}=2^n := hF
  obtain ⟨b,hb⟩ := huppert_II_10_4_trace_surjective J (2^n) hcard hf 1 (by simp)
  let h := thirdConjugator J hJ b hb*c
  let H := A ⊔ A.map (MulAut.conj (j g)).toMonoidHom ⊔ A.map (MulAut.conj h).toMonoidHom
  have hL : j.range≤H := hblock.trans le_sup_left
  have hU : central J hJ≤H := (central_le_block J hJ).trans hL
  have hz : hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd 1)) ∈ H :=
    hU ⟨Multiplicative.ofAdd 1,rfl⟩
  have htz : thirdConjugator J hJ b hb *
      hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd 1)) *
      (thirdConjugator J hJ b hb)⁻¹ ∈ H := by
    have hh : h*(j a₀)*h⁻¹ ∈ H :=
      (show A.map (MulAut.conj h).toMonoidHom≤H from le_sup_right) ⟨j a₀,ha₀,rfl⟩
    have he : h*(j a₀)*h⁻¹=thirdConjugator J hJ b hb *
        (c*(j a₀)*c⁻¹)*(thirdConjugator J hJ b hb)⁻¹ := by dsimp [h]; group
    rwa [he,hc] at hh
  obtain ⟨d,hd,hdv⟩ := connector_in_subgroup J hJ b hb H hz htz
  refine ⟨j g,h,eq_top_of_isotropicLineTransitive J hJ hn hcard hf H hU ?_⟩
  intro v hv hi
  rcases blockOrbitDecomposition J hJ b hb v hv hi with ⟨x,e,he,hx⟩ | ⟨x,e,he,hx⟩
  · exact ⟨j x,hL ⟨x,rfl⟩,e,he,hx⟩
  · refine ⟨j x*d,H.mul_mem (hL ⟨x,rfl⟩) hd,e,he,?_⟩
    intro i
    change ((block J hJ x).val.val*d.val.val) i 0 = _
    simpa only [Matrix.mul_apply,hdv,Matrix.mulVec,dotProduct] using hx i


/-- The same three-conjugate theorem on the projective carrier, with its
 actual central root and canonical scalar quotient. -/
theorem psu3_root_three_conjugates
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A≤centralImage J hJ) (hAc : 4≤Nat.card A) :
    ∃ g h : ProjectiveSpecialUnitaryMatrixGroup J,
      A ⊔ A.map (MulAut.conj g).toMonoidHom ⊔ A.map (MulAut.conj h).toMonoidHom=⊤ := by
  let j := J.specialToProjective.comp (block J hJ)
  let B := A.comap j
  have hBS : B≤SpecialLinearGroup.upperUnipotent (fixedField J) := by
    exact (comap_mono (hA.trans (projective_block_upper_image J hJ).symm.le)).trans
      (comap_map_eq_self_of_injective (projective_block_injective J hJ) _).le
  have hBA : B.map j=A := map_comap_eq_self
    (hA.trans ((projective_block_upper_image J hJ).symm.le.trans (map_le_range _ _)))
  let C := B.map (block J hJ)
  have hC : C≤central J hJ := (map_mono hBS).trans (block_upper_image J hJ).le
  have hCc : 4≤Nat.card C := by
    rw [←hBA,card_map_of_injective (projective_block_injective J hJ)] at hAc
    simpa only [C,card_map_of_injective (block_injective J hJ)] using hAc
  have hCA : C.map J.specialToProjective=A := by change (B.map (block J hJ)).map J.specialToProjective=A; rw [Subgroup.map_map]; exact hBA
  obtain ⟨g,h,hgen⟩ := su3_root_three_conjugates J hJ hn hcard hconj C hC hCc
  refine ⟨J.specialToProjective g,J.specialToProjective h,?_⟩
  have hmap (g : J.specialSubgroup) :
      (C.map (MulAut.conj g).toMonoidHom).map J.specialToProjective =
      A.map (MulAut.conj (J.specialToProjective g)).toMonoidHom := by
    have he : J.specialToProjective.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (J.specialToProjective g)).toMonoidHom.comp J.specialToProjective := by
      ext c
      simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
        MulAut.conj_apply,map_mul,map_inv]
    rw [Subgroup.map_map C J.specialToProjective (MulAut.conj g).toMonoidHom,he,
      ←Subgroup.map_map C (MulAut.conj (J.specialToProjective g)).toMonoidHom
        J.specialToProjective,hCA]
  have he := congrArg (Subgroup.map J.specialToProjective) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,hCA,hmap,hmap,
    map_top_of_surjective _ J.specialToProjective_surjective] at he
  exact he


/-- The full unitary root and the literal fixed-field block generate SU₃. -/
theorem su3_root_block_generate
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n)) :
    HermitianForm.BorelTorus.specialRoot J hJ ⊔ (block J hJ).range=⊤ := by
  let H := HermitianForm.BorelTorus.specialRoot J hJ ⊔ (block J hJ).range
  have hL : (block J hJ).range≤H := le_sup_right
  have hU : central J hJ≤H := (central_le_block J hJ).trans hL
  let w : SL(2,fixedField J) := ⟨!![0,1;1,0],by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩
  have hw : block J hJ w=hermitianWeylSU J hJ := by
    apply Subtype.ext
    apply Units.ext
    rw [block_val]
    change (!![0,0,1;0,1,0;1,0,0] : Matrix (Fin 3) (Fin 3) F)=!![0,0,1;0,-1,0;1,0,0]
    simp [CharTwo.neg_eq]
  have hwH : hermitianWeylSU J hJ ∈ H := hL ⟨w,hw⟩
  have hf : Nat.card {x : F // J.conj x=x}=2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨b,hb⟩ := huppert_II_10_4_trace_surjective J (2^n) hcard hf 1 (by simp)
  have hsH : seed J hJ b hb∈H := (show HermitianForm.BorelTorus.specialRoot J hJ≤H from
    le_sup_left) ⟨_,rfl⟩
  have htH : thirdConjugator J hJ b hb ∈ H := H.mul_mem hsH hwH
  have hzH : hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd 1)) ∈ H :=
    hU ⟨_,rfl⟩
  obtain ⟨d,hd,hdv⟩ := connector_in_subgroup J hJ b hb H hzH
    (H.mul_mem (H.mul_mem htH hzH) (H.inv_mem htH))
  apply eq_top_of_isotropicLineTransitive J hJ hn hcard hf H hU
  intro v hv hi
  rcases blockOrbitDecomposition J hJ b hb v hv hi with ⟨x,e,he,hx⟩ | ⟨x,e,he,hx⟩
  · exact ⟨block J hJ x,hL ⟨x,rfl⟩,e,he,hx⟩
  · refine ⟨block J hJ x*d,H.mul_mem (hL ⟨x,rfl⟩) hd,e,he,?_⟩
    intro i
    change ((block J hJ x).val.val*d.val.val) i 0 = _
    simpa only [Matrix.mul_apply,hdv,Matrix.mulVec,dotProduct] using hx i

/-- Projectivization preserves the same root/block generation. -/
theorem psu3_root_block_generate
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n)) :
    HermitianForm.BorelTorus.projectiveRoot J hJ ⊔
      (J.specialToProjective.comp (block J hJ)).range=⊤ := by
  have he := congrArg (Subgroup.map J.specialToProjective)
    (su3_root_block_generate J hJ hn hcard hconj)
  rw [Subgroup.map_sup,MonoidHom.map_range,
    map_top_of_surjective _ J.specialToProjective_surjective] at he
  have hr : (HermitianForm.BorelTorus.specialRoot J hJ).map J.specialToProjective=
      HermitianForm.BorelTorus.projectiveRoot J hJ := by
    change ((hermitianUnipotentSU J hJ).range).map J.specialToProjective = _
    rw [MonoidHom.map_range]
    have hh : J.specialToProjective.comp (hermitianUnipotentSU J hJ)=hermitianUnipotentPSU J hJ := by
      apply MonoidHom.ext
      intro z
      apply Subtype.ext
      simp only [MonoidHom.comp_apply,J.specialToProjective_apply_val]
      exact (hermitianUnipotentPSU_val J hJ z).symm
    rw [hh]
    rfl
  rwa [hr] at he

omit [Finite F] in
/-- The literal special central root lies in the fixed-field block. -/
theorem su3_central_le_block : central J hJ≤(block J hJ).range := central_le_block J hJ

omit [Finite F] in
/-- The projective central root lies in the same injected fixed-field block. -/
theorem psu3_central_le_block : centralImage J hJ≤
    (J.specialToProjective.comp (block J hJ)).range := by
  rw [←projective_block_upper_image]
  exact map_le_range _ _

end Representation.RankOne.QuadraticRecognition
