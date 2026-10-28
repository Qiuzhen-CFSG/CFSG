module
public import Theory.GroupTheory.QuaternionSwapModel.Parabolic
/-!
# The symmetric-four quotient of the quaternion-swap parabolic

The sum of the two quaternion quotient coordinates has kernel A. It extends
to H0 with image the affine group E4 ⋊ S3. The diagonal S3 action on E4 is
faithful: its kernel embeds in the inner automorphisms of Q8 and is a normal
two-subgroup of S3, hence trivial. The faithful affine action on the four
points is then the whole symmetric group, giving the actual quotient H0/A.
The quotient map and affine evaluation formulas retain the chosen coordinates.

Source: Aschbacher–Smith, proof of Lemma 14.2.21, printed p.988
(PDF p.1005), refs/quasithin.pdf.
-/

@[expose] public section
namespace QuaternionSwapModel

theorem q8Aut_neg (e : MulAut (QuaternionGroup 2)) :
    e (QuaternionGroup.a 2 : QuaternionGroup 2) = QuaternionGroup.a 2 := by
  exact congrArg (fun w : Raw => w.left 1) (rawAut_killed e)

theorem quaternionQuotient_ker (q : QuaternionGroup 2) :
    quaternionQuotient q = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2 := by
  have h : ∀ q : QuaternionGroup 2, quaternionQuotient q = 1 ↔
      q = 1 ∨ q = QuaternionGroup.a 2 := by decide +kernel
  exact h q

theorem quaternionQuotient_surjective : Function.Surjective quaternionQuotient := by
  decide +kernel

noncomputable def q8QuotientEquiv : QuaternionGroup 2 ⧸ quaternionQuotient.ker ≃* E4 :=
  QuotientGroup.quotientKerEquivOfSurjective quaternionQuotient quaternionQuotient_surjective

noncomputable def e4Aut (e : MulAut (QuaternionGroup 2)) : MulAut E4 :=
  q8QuotientEquiv.symm.trans ((QuotientGroup.congr quaternionQuotient.ker
    quaternionQuotient.ker e (by
      apply le_antisymm
      · rintro _ ⟨q,hq,rfl⟩
        change quaternionQuotient (e q) = 1
        rcases (quaternionQuotient_ker q).mp hq with rfl | rfl
        · simp
        · rw [q8Aut_neg]; decide
      · intro q hq
        refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
        change quaternionQuotient (e.symm q) = 1
        rcases (quaternionQuotient_ker q).mp hq with rfl | rfl
        · simp
        · rw [q8Aut_neg]; decide)).trans q8QuotientEquiv)

theorem e4Aut_quaternionQuotient (e : MulAut (QuaternionGroup 2)) (q : QuaternionGroup 2) :
    e4Aut e (quaternionQuotient q) = quaternionQuotient (e q) := by
  have hq : q8QuotientEquiv.symm (quaternionQuotient q) =
      QuotientGroup.mk' quaternionQuotient.ker q := by
    apply q8QuotientEquiv.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  simp only [e4Aut, MulEquiv.trans_apply, hq, QuotientGroup.congr_mk']
  rfl

noncomputable def e4AutHom : MulAut (QuaternionGroup 2) →* MulAut E4 where
  toFun := e4Aut
  map_one' := by
    apply MulEquiv.ext
    intro v
    obtain ⟨q,rfl⟩ := quaternionQuotient_surjective v
    exact e4Aut_quaternionQuotient 1 q
  map_mul' e f := by
    apply MulEquiv.ext
    intro v
    obtain ⟨q,rfl⟩ := quaternionQuotient_surjective v
    simp only [MulAut.mul_apply, e4Aut_quaternionQuotient]

noncomputable def s3E4Action : S3 →* MulAut E4 := e4AutHom.comp q8PermAction

theorem s3E4Action_quotient (a : S3) (q : QuaternionGroup 2) :
    s3E4Action a (quaternionQuotient q) = quaternionQuotient (q8PermAction a q) :=
  e4Aut_quaternionQuotient _ _

theorem permThreeLift_injective : Function.Injective permThreeLift := by
  intro a b h
  have h' := (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4).permCongrHom.injective h
  apply Equiv.ext
  intro x
  have hh := DFunLike.congr_fun h' (Sum.inr x)
  exact Sum.inr.inj hh

theorem q8PermAction_injective : Function.Injective q8PermAction :=
  QuaternionGroup.Residual.autEquivPerm.symm.injective.comp permThreeLift_injective

abbrev q8Inner : Subgroup (MulAut (QuaternionGroup 2)) := MulAut.conj.range

theorem q8Inner_two : IsPGroup 2 q8Inner := by
  have h : IsPGroup 2 (QuaternionGroup 2) := by
    apply IsPGroup.of_card (n := 3)
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  exact h.of_surjective (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

theorem q8_action_ker_inner (e : MulAut (QuaternionGroup 2)) (he : e4Aut e = 1) : e ∈ q8Inner := by
  obtain ⟨q,hq⟩ := QuaternionGroup.exists_conj_of_central_difference e (by
    intro x
    have hh : quaternionQuotient (x⁻¹ * e x) = 1 := by
      rw [map_mul, map_inv, ← e4Aut_quaternionQuotient, he, MulAut.one_apply, inv_mul_cancel]
    rcases (quaternionQuotient_ker _).mp hh with hh | hh
    · rw [hh]; exact Subgroup.one_mem _
    · rw [hh]
      exact (by decide : QuaternionGroup.a 2 ∈ Subgroup.center (QuaternionGroup 2)))
  exact ⟨q,hq.symm⟩

theorem s3E4Action_injective : Function.Injective s3E4Action := by
  let f : s3E4Action.ker →* q8Inner := {
    toFun a := ⟨q8PermAction a, q8_action_ker_inner _ a.property⟩
    map_one' := by apply Subtype.ext; exact map_one q8PermAction
    map_mul' a b := by apply Subtype.ext; exact map_mul q8PermAction (a : S3) (b : S3) }
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact q8PermAction_injective (congrArg Subtype.val h)
  have hp : IsPGroup 2 s3E4Action.ker := q8Inner_two.of_injective f hf
  have hle : s3E4Action.ker ≤ pCore 2 S3 := le_sSup ⟨inferInstance, hp⟩
  have hbot : pCore 2 S3 = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id S3)
      Function.surjective_id (by
        rw [MonoidHom.ker_id]
        exact IsPGroup.of_card (n := 0) (by simp))
    simpa only [MonoidHom.ker_id] using hh.symm
  exact (MonoidHom.ker_eq_bot_iff _).mp (le_antisymm (hbot ▸ hle) bot_le)

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rawSum : Raw →* E4 where
  toFun r := quaternionQuotient (r.left 1) * quaternionQuotient (r.left turn)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def sumCoord : QH →* E4 := QuotientGroup.lift diagonalCenter rawSum (by
  rintro x (rfl | rfl) <;> decide +kernel)

theorem sumCoord_left (q : QuaternionGroup 2) :
    sumCoord (leftEmbedding q) = quaternionQuotient q := by
  have hh : ∀ q : QuaternionGroup 2, rawSum (leftRaw q) = quaternionQuotient q := by
    decide +kernel
  exact hh q

theorem sumCoord_surjective : Function.Surjective sumCoord := by
  intro v
  obtain ⟨q,rfl⟩ := quaternionQuotient_surjective v
  exact ⟨leftEmbedding q, sumCoord_left q⟩

theorem sumCoord_ker : sumCoord.ker = A := by
  ext x
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  change rawSum r = 1 ↔ quaternionQuotient (r.left 1) = quaternionQuotient (r.left turn)
  have hh : ∀ r : Raw, rawSum r = 1 ↔
      quaternionQuotient (r.left 1) = quaternionQuotient (r.left turn) := by decide +kernel
  exact hh r

theorem sumCoord_qhAut (e : MulAut (QuaternionGroup 2)) (x : QH) :
    sumCoord (qhAut e x) = e4Aut e (sumCoord x) := by
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  change quaternionQuotient (e (r.left 1)) * quaternionQuotient (e (r.left turn)) =
    e4Aut e (quaternionQuotient (r.left 1) * quaternionQuotient (r.left turn))
  rw [map_mul, e4Aut_quaternionQuotient, e4Aut_quaternionQuotient]

abbrev AffineFour := E4 ⋊[s3E4Action] S3
instance : Finite AffineFour := Finite.of_equiv (E4 × S3) SemidirectProduct.equivProd.symm

noncomputable def affineMap : H0 →* AffineFour :=
  SemidirectProduct.map sumCoord (MonoidHom.id S3) (by
    intro a
    apply MonoidHom.ext
    intro x
    exact sumCoord_qhAut _ _)

theorem affineMap_surjective : Function.Surjective affineMap := by
  intro v
  obtain ⟨q,hq⟩ := sumCoord_surjective v.left
  exact ⟨⟨q,v.right⟩, SemidirectProduct.ext hq rfl⟩

theorem affineMap_ker : affineMap.ker = A.map i := by
  ext h
  constructor
  · intro hh
    have hl : sumCoord h.left = 1 := congrArg SemidirectProduct.left hh
    have hr : h.right = 1 := congrArg SemidirectProduct.right hh
    refine ⟨h.left, ?_, ?_⟩
    · rw [← sumCoord_ker]; exact hl
    · apply SemidirectProduct.ext
      · rfl
      · exact hr.symm
  · rintro ⟨a,ha,rfl⟩
    apply SemidirectProduct.ext
    · exact show a ∈ sumCoord.ker from sumCoord_ker.symm ▸ ha
    · rfl

noncomputable def affinePerm (h : AffineFour) : Equiv.Perm E4 where
  toFun x := h.left * s3E4Action h.right x
  invFun x := (s3E4Action h.right).symm (h.left⁻¹ * x)
  left_inv x := by simp only [inv_mul_cancel_left, MulEquiv.symm_apply_apply]
  right_inv x := by simp only [MulEquiv.apply_symm_apply, mul_inv_cancel_left]

noncomputable def affinePermHom : AffineFour →* Equiv.Perm E4 where
  toFun := affinePerm
  map_one' := by
    apply Equiv.ext
    intro x
    change 1 * s3E4Action 1 x = x
    rw [map_one, MulAut.one_apply, one_mul]
  map_mul' h k := by
    apply Equiv.ext
    intro x
    change (h.left * s3E4Action h.right k.left) * s3E4Action (h.right*k.right) x =
      h.left * s3E4Action h.right (k.left * s3E4Action k.right x)
    rw [map_mul, map_mul, MulAut.mul_apply, mul_assoc]

theorem affinePermHom_injective : Function.Injective affinePermHom := by
  intro h k he
  have hl : h.left = k.left := by
    have hh := DFunLike.congr_fun he 1
    change h.left * s3E4Action h.right 1 = k.left * s3E4Action k.right 1 at hh
    simpa only [map_one, mul_one] using hh
  apply SemidirectProduct.ext hl
  apply s3E4Action_injective
  apply MulEquiv.ext
  intro x
  have hh := DFunLike.congr_fun he x
  change h.left * s3E4Action h.right x = k.left * s3E4Action k.right x at hh
  rw [hl] at hh
  exact mul_left_cancel hh

noncomputable def affineEquivPerm : AffineFour ≃* Equiv.Perm E4 :=
  MulEquiv.ofBijective affinePermHom ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨affinePermHom_injective, by
      rw [SemidirectProduct.card]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]⟩)

noncomputable def fourPoints : E4 ≃ Fin 4 := Fintype.equivOfCardEq (by decide)

noncomputable def affineEquivS4 : AffineFour ≃* S4 :=
  affineEquivPerm.trans fourPoints.permCongrHom

noncomputable def s4Map : H0 →* S4 := affineEquivS4.toMonoidHom.comp affineMap

/-- Evaluation of the quotient map on the chosen four affine points. -/
theorem s4Map_apply (h : H0) (v : E4) :
    s4Map h (fourPoints v) =
      fourPoints (sumCoord h.left * s3E4Action h.right v) := by
  change fourPoints (sumCoord h.left *
    s3E4Action h.right (fourPoints.symm (fourPoints v))) = _
  rw [Equiv.symm_apply_apply]

theorem s4Map_surjective : Function.Surjective s4Map :=
  affineEquivS4.surjective.comp affineMap_surjective

theorem s4Map_ker : s4Map.ker = A.map i := by
  rw [← affineMap_ker]
  ext h
  change affineEquivS4 (affineMap h) = 1 ↔ affineMap h = 1
  exact map_eq_one_iff affineEquivS4 affineEquivS4.injective

instance : (A.map i).Normal := A_map_i_normal

noncomputable def elementaryQuotientEquiv : H0 ⧸ (A.map i) ≃* S4 :=
  (QuotientGroup.quotientMulEquivOfEq s4Map_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective s4Map s4Map_surjective)

theorem elementaryQuotientEquiv_mk (h : H0) :
    elementaryQuotientEquiv (QuotientGroup.mk' (A.map i) h) = s4Map h := rfl

end QuaternionSwapModel
