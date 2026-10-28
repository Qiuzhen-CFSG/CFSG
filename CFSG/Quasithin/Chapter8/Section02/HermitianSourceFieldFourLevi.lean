module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.CommutatorImage
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The faithful SL₂(4) action on the canonical Hermitian fixed subgroup

The fixed space of the plane radical is the literal two-by-two Hermitian
corner. The determinant-one block in SL₃(4) acts there by SL₂(4) congruences.
Transport through the original component marking realizes this faithful
linear action in the ambient automizer of the fixed subgroup. Perfectness
puts this image inside the action image of N_L(U)^∞. Conversely, each
element of the component normalizer preserves the corner determinant form.
The residual is perfect, so its action lies in the orthogonal commutator,
which is exactly the Hermitian SL₂(4) image. Thus the entire residual image
is identified, with the residual embedded in the original group and its
full action kernel retained.

The Chapter 12 companion supplies the actual canonical subgroup in both
remaining weak-closure branches. This identifies the action of N_L(U)^∞;
the equality of its centralizer kernel with its two-core, its component
placement and the source exclusion remain separate obligations.

Source: Aschbacher--Smith H.4.6(2) and 8.2.6(2), printed pp.382,717,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
public noncomputable section
set_option backward.isDefEq.respectTransparency false
private abbrev Corner := OrthogonalFourMinus.FiniteModel.Space 1
private abbrev PlaneFixed := fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)
private def cornerCoordinates : PlaneFixed ≃ₗ[ZMod 2] ((F 1 × F 1) × E 1) where
  toEquiv := UnipotentRadicals.planeFixedCoordinates 1
  map_add' _ _ := rfl
  map_smul' a x := by
    have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases ha with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      rfl
    · simp only [one_smul, RingHom.id_apply]
private def cornerEquiv : PlaneFixed ≃ₗ[ZMod 2] Corner :=
  cornerCoordinates.trans ((OrthogonalFourMinus.FiniteModel.coordinates 1).restrictScalars (ZMod 2)).symm
private def cornerLevi : SL(2,E 1) →* Cover 1 where
  toFun a := ⟨!![a 0 0,a 0 1,0; a 1 0,a 1 1,0; 0,0,1],by
    have ha : a.val.det = 1 := a.property
    rw [Matrix.det_fin_two] at ha
    simpa [Matrix.det_fin_three] using ha⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change !![(a*b) 0 0,(a*b) 0 1,0; (a*b) 1 0,(a*b) 1 1,0; 0,0,1] =
      !![a 0 0,a 0 1,0; a 1 0,a 1 1,0; 0,0,1] *
      !![b 0 0,b 0 1,0; b 1 0,b 1 1,0; 0,0,1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two]

private theorem cornerLevi_val (a : SL(2,E 1)) :
    (cornerLevi a).val = !![a 0 0,a 0 1,0; a 1 0,a 1 1,0; 0,0,1] := rfl

private theorem cornerEquiv_entry (v : PlaneFixed) (i j : Fin 2) :
    (cornerEquiv v).val i j = v.val.val i.castSucc j.castSucc := by
  change ((OrthogonalFourMinus.FiniteModel.coordinates 1).symm
    ((UnipotentRadicals.planeFixedCoordinates 1) v)).val i j = _
  fin_cases i <;> fin_cases j <;> try rfl
  exact entry_conjugate 1 v.val 1 0

private theorem cornerLevi_fixed (a : SL(2,E 1)) (v : PlaneFixed) :
    binaryActionHom 1 (cornerLevi a) v.val ∈ PlaneFixed := by
  apply (UnipotentRadicals.mem_plane_fixed_iff 1 _).mpr
  obtain ⟨h22,h12,h02⟩ := (UnipotentRadicals.mem_plane_fixed_iff 1 v.val).mp v.property
  change ((cornerLevi a).val * v.val.val * adjoint 1 (cornerLevi a).val) 2 2 = 0 ∧
    ((cornerLevi a).val * v.val.val * adjoint 1 (cornerLevi a).val) 1 2 = 0 ∧
    ((cornerLevi a).val * v.val.val * adjoint 1 (cornerLevi a).val) 0 2 = 0
  simp [cornerLevi_val,
    adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,h22,h12,h02]

private theorem cornerLevi_action (a : SL(2,E 1)) (v : PlaneFixed) :
    cornerEquiv ⟨binaryActionHom 1 (cornerLevi a) v.val,cornerLevi_fixed a v⟩ =
      OrthogonalFourMinus.FiniteModel.action 1 a (cornerEquiv v) := by
  apply Subtype.ext
  ext i j
  rw [cornerEquiv_entry,OrthogonalFourMinus.FiniteModel.action_apply]
  change ((cornerLevi a).val * v.val.val * adjoint 1 (cornerLevi a).val)
    i.castSucc j.castSucc = _
  fin_cases i <;> fin_cases j <;>
    simp [cornerLevi_val,
      adjoint,OrthogonalFourMinus.adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,
      Fin.sum_univ_two,cornerEquiv_entry]

private theorem fixed_field_two (a : F 1) : a = 0 ∨ a = 1 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    let : Fintype (F 1) := Fintype.ofFinite _
    have hh := FiniteField.pow_card_sub_one_eq_one a ha
    have hc : Fintype.card (F 1) = 2 := by
      rw [← Nat.card_eq_fintype_card,card_F]
      rfl
    simpa only [hc,show 2-1 = 1 by decide,pow_one] using hh

private theorem corner_form_preserved (a : Cover 1) (t : Corner ≃ₗ[ZMod 2] Corner)
    (ht : ∀ v : PlaneFixed, (cornerEquiv.symm (t (cornerEquiv v))).val =
      binaryActionHom 1 a v.val) :
    ∀ v, OrthogonalFourMinus.FiniteModel.form 1 (t v) =
      OrthogonalFourMinus.FiniteModel.form 1 v := by
  let b := a.val.submatrix Fin.castSucc Fin.castSucc
  let c := OrthogonalFourMinus.FiniteModel.norm 1 b.det
  have hm (v : PlaneFixed) : (t (cornerEquiv v)).val =
      b * (cornerEquiv v).val * (b.transpose.map (sigma 1)) := by
    obtain ⟨h22,h12,h02⟩ := (UnipotentRadicals.mem_plane_fixed_iff 1 v.val).mp v.property
    have hc (i : Fin 3) : v.val.val i 2 = 0 := by
      fin_cases i <;> assumption
    have hr (i : Fin 3) : v.val.val 2 i = 0 := by
      rw [←entry_conjugate 1 v.val 2 i,hc,map_zero]
    ext i j
    have hh := cornerEquiv_entry (cornerEquiv.symm (t (cornerEquiv v))) i j
    rw [cornerEquiv.apply_symm_apply,ht] at hh
    rw [hh]
    change (a.val * v.val.val * adjoint 1 a.val) i.castSucc j.castSucc = _
    simp only [Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two,
      cornerEquiv_entry,Matrix.map_apply,Matrix.transpose_apply,
      b,Matrix.submatrix_apply,adjoint,hc,hr,zero_mul,mul_zero,add_zero]
    rfl
  have hs (v : Corner) : OrthogonalFourMinus.FiniteModel.form 1 (t v) =
      c * OrthogonalFourMinus.FiniteModel.form 1 v := by
    obtain ⟨u,rfl⟩ := cornerEquiv.surjective v
    apply Subtype.ext
    change (t (cornerEquiv u)).val.det =
      (b.det * sigma 1 b.det) * (cornerEquiv u).val.det
    have hb : (b.transpose.map (sigma 1)).det = sigma 1 b.det := by
      exact ((sigma 1).map_det b.transpose).symm.trans (congrArg (sigma 1) b.det_transpose)
    rw [hm,Matrix.det_mul,Matrix.det_mul,hb]
    ring
  have hc : c = 1 := by
    rcases fixed_field_two c with hc | hc
    · have hh := hs (t.symm ((OrthogonalFourMinus.FiniteModel.coordinates 1).symm ((1,1),0)))
      rw [t.apply_symm_apply,hc,zero_mul,OrthogonalFourMinus.FiniteModel.form_coordinates] at hh
      have hh' := congrArg Subtype.val hh
      norm_num [OrthogonalFourMinus.FiniteModel.norm] at hh'
    · exact hc
  intro v
  simpa only [hc,one_mul] using hs v

private def cornerLinear (t : Corner ≃ₗ[ZMod 2] Corner) :
    Corner ≃ₗ[F 1] Corner where
  toEquiv := t.toEquiv
  map_add' := t.map_add
  map_smul' a v := by
    rcases fixed_field_two a with rfl | rfl <;> simp


private theorem perfect_corner_action
    {X : Type*} [Group X] [Group.IsPerfect X]
    (f : X →* (Corner ≃ₗ[F 1] Corner))
    (hf : ∀ x v, OrthogonalFourMinus.FiniteModel.form 1 (f x v) =
      OrthogonalFourMinus.FiniteModel.form 1 v) (x : X) :
    ∃ a : SL(2,E 1), ∀ v, f x v = OrthogonalFourMinus.FiniteModel.action 1 a v := by
  let o : X →* ClassicalOrthogonal.Minus.Orthogonal (F 1) Corner
      (OrthogonalFourMinus.FiniteModel.form 1) :=
    f.codRestrict _ (fun x => (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr (hf x))
  let : Group.IsPerfect o.range := Group.IsPerfect.range o
  have hh : o.range ≤ commutator _ := by
    rw [←o.range.commutator_eq_self,commutator_def]
    exact commutator_mono le_top le_top
  obtain ⟨a,ha⟩ := OrthogonalFourMinus.HermitianEquiv.commutator_le_range_orthogonalAction 1
    (hh (show o x ∈ o.range from ⟨x,rfl⟩))
  refine ⟨a,fun v => ?_⟩
  exact congrArg (fun t => t.val v) ha.symm

private theorem perfect_range_le_induced_residual
    {G X : Type*} [Group G] [Finite G] [Group X] [Group.IsPerfect X]
    (U H : Subgroup G) (hH : H ≤ normalizer (U : Set G))
    (f : X →* Automizer U) (hf : f.range ≤ inducedAutomizer U H) :
    f.range ≤ inducedAutomizer U ((solvableResidual H).map H.subtype) := by
  let q := U.normalizerMonoidHom.rangeRestrict.comp (inclusion hH)
  have hq : q.range = inducedAutomizer U H := by
    rw [MonoidHom.range_comp,Subgroup.inclusion_range]
    rfl
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  have hh := le_map_solvableResidual_of_isPerfect f.range q.range (hq ▸ hf)
  have hmap : (solvableResidual q.range).map q.range.subtype =
      (solvableResidual H).map q := by
    rw [←map_solvableResidual_eq q.rangeRestrict q.rangeRestrict_surjective,map_map]
    rfl
  rw [hmap] at hh
  intro t ht
  obtain ⟨x,hx,hxt⟩ := hh ht
  rw [←hxt]
  apply mem_map_of_mem U.normalizerMonoidHom.rangeRestrict
  exact mem_map_of_mem H.subtype hx

private theorem residual_le_corner_action
    {G : Type*} [Group G] [Finite G]
    (V L U : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (k : Additive U ≃ₗ[ZMod 2] PlaneFixed)
    (hk : ∀ u, (k u).val = e ((inclusion hUV).toAdditive.toZModLinearMap 2 u))
    (f : SL(2,E 1) →* Automizer U)
    (hf : ∀ a u, cornerEquiv (k (automizerRepresentation U (f a) u)) =
      OrthogonalFourMinus.FiniteModel.action 1 a (cornerEquiv (k u))) :
    inducedAutomizer U ((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
      (L ⊓ normalizer (U : Set G)).subtype) ≤ f.range := by
  let ι := (inclusion hUV).toAdditive.toZModLinearMap 2
  let b := k.trans cornerEquiv
  let H : Subgroup G := L ⊓ normalizer (U : Set G)
  let R := solvableResidual H
  let qU : H →* Automizer U := U.normalizerMonoidHom.rangeRestrict.comp (inclusion inf_le_right)
  let θ (x : Automizer U) : Corner ≃ₗ[ZMod 2] Corner :=
    b.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv ((automizerRepresentation U).asGroupHom x)).trans b)
  let φ : Automizer U →* (Corner ≃ₗ[F 1] Corner) :=
    { toFun := fun x => cornerLinear (θ x)
      map_one' := by
        apply LinearEquiv.ext
        intro v
        change b (automizerRepresentation U 1 (b.symm v)) = v
        rw [map_one]
        exact b.apply_symm_apply v
      map_mul' := by
        intro x y
        apply LinearEquiv.ext
        intro v
        change b (automizerRepresentation U (x*y) (b.symm v)) =
          b (automizerRepresentation U x (b.symm (b (automizerRepresentation U y (b.symm v)))))
        rw [b.symm_apply_apply,map_mul]
        rfl }
  let ψ : R →* (Corner ≃ₗ[F 1] Corner) := φ.comp (qU.comp R.subtype)
  have hp (r : R) (v : Corner) :
      OrthogonalFourMinus.FiniteModel.form 1 (ψ r v) =
        OrthogonalFourMinus.FiniteModel.form 1 v := by
    let l : L := ⟨r.val.val,r.val.property.1⟩
    obtain ⟨a,ha⟩ := (q l).property
    apply corner_form_preserved a (θ (qU r.val)) ?_ v
    intro u
    have hh := he l (ι (k.symm u))
    rw [←ha] at hh
    change e (ι (automizerRepresentation U (qU r.val) (k.symm u))) =
      binaryActionHom 1 a (e (ι (k.symm u))) at hh
    change (cornerEquiv.symm (b (automizerRepresentation U (qU r.val)
      (b.symm (cornerEquiv u))))).val = binaryActionHom 1 a u.val
    change (cornerEquiv.symm (cornerEquiv (k (automizerRepresentation U (qU r.val)
      (k.symm (cornerEquiv.symm (cornerEquiv u))))))).val = _
    rw [cornerEquiv.symm_apply_apply,cornerEquiv.symm_apply_apply]
    rw [hk]
    calc
      _ = binaryActionHom 1 a (e (ι (k.symm u))) := hh
      _ = binaryActionHom 1 a (k (k.symm u)).val := congrArg (binaryActionHom 1 a) (hk (k.symm u)).symm
      _ = _ := congrArg (fun z : PlaneFixed => binaryActionHom 1 a z.val) (k.apply_symm_apply u)
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨r,hr,hry⟩ := hy
  let r' : R := ⟨r,hr⟩
  obtain ⟨a,ha⟩ := perfect_corner_action ψ hp r'
  refine ⟨a,?_⟩
  apply automizerRepresentation_injective U
  apply LinearMap.ext
  intro u
  apply b.injective
  change cornerEquiv (k (automizerRepresentation U (f a) u)) = _
  rw [hf]
  have hh := ha (b u)
  change b (automizerRepresentation U (qU r) (b.symm (b u))) = _ at hh
  rw [b.symm_apply_apply] at hh
  have heqU : qU r = U.normalizerMonoidHom.rangeRestrict y := by
    exact congrArg U.normalizerMonoidHom.rangeRestrict (Subtype.ext hry)
  rw [heqU] at hh
  exact hh.symm

variable {G : Type*} [Group G] [Finite G]

/-- The whole image of the original component normalizer residual is the
faithful Hermitian SL₂(4) action on its plane fixed subgroup. -/
theorem field_four_fixed_subgroup_sl2_action
    (V L U : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : L →* binaryImage 1) (hq : Function.Surjective q)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔
      e v ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)) :
    ∃ (b : Additive U ≃ₗ[ZMod 2] OrthogonalFourMinus.FiniteModel.Space 1)
      (f : SL(2,E 1) →* Automizer U), Function.Injective f ∧
        f.range = inducedAutomizer U ((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
          (L ⊓ normalizer (U : Set G)).subtype) ∧
        ∀ a u, b (automizerRepresentation U (f a) u) =
          OrthogonalFourMinus.FiniteModel.action 1 a (b u) := by
  let ι := (inclusion hUV).toAdditive.toZModLinearMap 2
  let c : Additive U →ₗ[ZMod 2] PlaneFixed :=
    (e.toLinearMap.comp ι).codRestrict _ (fun u => (hU (ι u)).mp u.toMul.property)
  have hci : Function.Injective c := by
    intro u v huv
    have hh : ι u = ι v := e.injective (congrArg Subtype.val huv)
    exact Subtype.ext (congrArg (fun z : Additive V => (z.toMul : G)) hh)
  have hcs : Function.Surjective c := by
    intro v
    let x := e.symm v.val
    have hx : (x.toMul : G) ∈ U := (hU x).mpr (by rw [e.apply_symm_apply]; exact v.property)
    refine ⟨Additive.ofMul ⟨x.toMul,hx⟩,?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply v.val
  let k : Additive U ≃ₗ[ZMod 2] PlaneFixed := LinearEquiv.ofBijective c ⟨hci,hcs⟩
  let b := k.trans cornerEquiv
  have lifts (a : SL(2,E 1)) : ∃ t : Automizer U,
      t ∈ inducedAutomizer U (L ⊓ normalizer (U : Set G)) ∧
      ∀ u, b (automizerRepresentation U t u) =
        OrthogonalFourMinus.FiniteModel.action 1 a (b u) := by
    obtain ⟨l,hl⟩ := hq ⟨binaryActionHom 1 (cornerLevi a),⟨cornerLevi a,rfl⟩⟩
    have hnorm : (l : G) ∈ normalizer (U : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      apply eq_of_le_of_card_ge
      · rintro _ ⟨x,hx,rfl⟩
        let v : Additive V := Additive.ofMul ⟨x,hUV hx⟩
        have hv : e v ∈ PlaneFixed := (hU v).mp hx
        have hh := cornerLevi_fixed a ⟨e v,hv⟩
        rw [← show (q l).val = binaryActionHom 1 (cornerLevi a) from congrArg Subtype.val hl,
          ← he l v] at hh
        exact (hU _).mpr hh
      · exact (Nat.card_congr (U.equivMapOfInjective
          (MulAut.conj (l : G)).toMonoidHom (MulAut.conj (l : G)).injective).toEquiv).le
    let t : Automizer U := U.normalizerMonoidHom.rangeRestrict ⟨l,hnorm⟩
    refine ⟨t,mem_map_of_mem U.normalizerMonoidHom.rangeRestrict ⟨l.property,hnorm⟩,?_⟩
    intro u
    have hk : k (automizerRepresentation U t u) =
        ⟨binaryActionHom 1 (cornerLevi a) (k u).val,cornerLevi_fixed a (k u)⟩ := by
      apply Subtype.ext
      have hh := he l (ι u)
      rw [hl] at hh
      exact hh
    change cornerEquiv (k (automizerRepresentation U t u)) = _
    rw [hk,cornerLevi_action]
    rfl
  choose f hf heq using lifts
  have hact (x y : Automizer U)
      (hh : ∀ u, b (automizerRepresentation U x u) = b (automizerRepresentation U y u)) :
      x = y := by
    apply automizerRepresentation_injective U
    apply LinearMap.ext
    intro u
    exact b.injective (hh u)
  let f' : SL(2,E 1) →* Automizer U :=
    { toFun := f
      map_one' := by
        apply hact
        intro u
        rw [heq,map_one,map_one]
        rfl
      map_mul' := by
        intro a d
        apply hact
        intro u
        rw [heq,map_mul,map_mul]
        change _ = b (automizerRepresentation U (f a) (automizerRepresentation U (f d) u))
        rw [heq,heq]
        rfl }
  refine ⟨b,f',?_,?_,heq⟩
  · intro a d had
    apply OrthogonalFourMinus.FiniteModel.action_injective 1
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := b.surjective v
    exact (heq a u).symm.trans ((congrArg (fun t => b (automizerRepresentation U t u)) had).trans (heq d u))
  · apply le_antisymm
    · let : Group.IsPerfect SL(2,E 1) :=
        ⟨OrthogonalFourMinus.HermitianEquiv.sl2_commutator_eq_top 1⟩
      apply perfect_range_le_induced_residual U (L ⊓ normalizer (U : Set G)) inf_le_right f'
      rintro _ ⟨a,rfl⟩
      exact hf a
    · exact residual_le_corner_action V L U hUV hLN e q he k (fun _ => rfl) f' heq

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
