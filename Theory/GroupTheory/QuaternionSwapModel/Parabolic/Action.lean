module
public import Theory.GroupTheory.QuaternionSwapModel.Parabolic.Quotient
/-!
# Coordinate conjugation in the quaternion-swap parabolic

The action on QH is conjugation by the quaternion component followed by the
diagonal S3 action. It restricts to the normal elementary subgroup A, and
`elementaryAction` transports this literal action through `elementaryEquiv`.
An explicit decoder reads a representative's two quaternion quotient bits,
its relative central sign and its swap bit. This gives an evaluation formula
for every actor and every vector, and fixes the third basis vector, the marked z.

On QH/Z, the action is conjugation in the wreath group followed by the diagonal
E4 action. Its left and right coordinate formulas prove invariance of the
specified subgroup `other` under all of H0. The quotient action is compatible
with the original `quotientEquiv`, including its quotient map.

Together with `Parabolic` and `Parabolic.Quotient`, this completes the intrinsic
order-384 construction, two-core, residual commutator, normal E16 and S4 quotient.
Identification with the concrete Aut(M12) compatible pair is a separate theorem.
Source: Aschbacher–Smith, proof of Lemma 14.2.21, printed p.988
(PDF p.1005), refs/quasithin.pdf.
-/

@[expose] public section
namespace QuaternionSwapModel

noncomputable def coreAction : H0 →* MulAut QH where
  toFun h := MulAut.conj h.left * s3Action h.right
  map_one' := by
    change MulAut.conj 1 * s3Action 1 = 1
    simp
  map_mul' h k := by
    apply MulEquiv.ext
    intro x
    change (h.left * s3Action h.right k.left) * s3Action (h.right * k.right) x *
      (h.left * s3Action h.right k.left)⁻¹ =
      h.left * s3Action h.right (k.left * s3Action k.right x * k.left⁻¹) * h.left⁻¹
    simp only [map_mul, map_inv, MulAut.mul_apply, mul_inv_rev]
    group

theorem coreAction_apply (h : H0) (x : QH) :
    coreAction h x = h.left * s3Action h.right x * h.left⁻¹ := rfl

theorem i_coreAction (h : H0) (x : QH) :
    i (coreAction h x) = h * i x * h⁻¹ := by
  rw [← SemidirectProduct.inl_left_mul_inr_right h]
  rw [coreAction_apply, map_mul, map_mul, ← inr_conj_i]
  simp only [map_inv, i, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.left_inr, SemidirectProduct.right_inl,
    SemidirectProduct.right_inr, map_one, mul_one, one_mul]
  group

theorem coreAction_mem_A (h : H0) (a : QH) (ha : a ∈ A) : coreAction h a ∈ A :=
  (inferInstance : A.Normal).conj_mem _ (s3Action_mem_A _ _ ha) _

noncomputable def aConjugation : H0 →* MulAut A where
  toFun h := {
    toFun a := ⟨coreAction h a, coreAction_mem_A h a a.property⟩
    invFun a := ⟨coreAction h⁻¹ a, coreAction_mem_A h⁻¹ a a.property⟩
    left_inv a := by apply Subtype.ext; simp
    right_inv a := by apply Subtype.ext; simp
    map_mul' a b := by apply Subtype.ext; exact map_mul (coreAction h) (a : QH) (b : QH) }
  map_one' := by ext a; exact DFunLike.congr_fun (map_one coreAction) (a : QH)
  map_mul' h k := by ext a; exact DFunLike.congr_fun (map_mul coreAction h k) (a : QH)

noncomputable def elementaryAction : H0 →* MulAut E16 :=
  (MulAut.congr elementaryEquiv).toMonoidHom.comp aConjugation

def sixteenDecode (r : Raw) : E16 := Multiplicative.ofAdd ![
  (quaternionQuotient (r.left turn)).toAdd 0,
  (quaternionQuotient (r.left turn)).toAdd 1,
  if r.left 1 = r.left turn then 0 else 1,
  r.right.toAdd]

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem sixteenDecode_sixteenRaw : ∀ v : E16, sixteenDecode (sixteenRaw v) = v := by
  decide +kernel

theorem sixteenDecode_lift (r : Raw) (hr : projection r ∈ A) :
    projection (sixteenRaw (sixteenDecode r)) = projection r := by
  rw [projection_eq_iff]
  change quaternionQuotient (r.left 1) = quaternionQuotient (r.left turn) at hr
  have ht : ∀ r : Raw,
      quaternionQuotient (r.left 1) = quaternionQuotient (r.left turn) →
      (sixteenRaw (sixteenDecode r))⁻¹ * r = 1 ∨
      (sixteenRaw (sixteenDecode r))⁻¹ * r = killed := by decide +kernel
  exact ht r hr

theorem elementaryEquiv_sixteenEmbedding (v : E16) :
    elementaryEquiv ⟨sixteenEmbedding v, sixteenEmbedding_range ▸ ⟨v,rfl⟩⟩ = v := by
  change (MonoidHom.ofInjective sixteenEmbedding_injective).symm
    ((MonoidHom.ofInjective sixteenEmbedding_injective) v) = v
  exact MulEquiv.symm_apply_apply _ _

theorem elementaryEquiv_decode (r : Raw) (hr : projection r ∈ A) :
    elementaryEquiv ⟨projection r, hr⟩ = sixteenDecode r := by
  have he : (⟨projection r, hr⟩ : A) =
      ⟨sixteenEmbedding (sixteenDecode r), sixteenEmbedding_range ▸ ⟨_, rfl⟩⟩ :=
    Subtype.ext (sixteenDecode_lift r hr).symm
  rw [he, elementaryEquiv_sixteenEmbedding]

theorem s3Action_projection (a : S3) (r : Raw) :
    s3Action a (projection r) = projection (rawAut (q8PermAction a) r) := rfl

theorem coreAction_projection (r s : Raw) (a : S3) :
    coreAction (⟨projection r, a⟩ : H0) (projection s) =
      projection (r * rawAut (q8PermAction a) s * r⁻¹) := by
  rw [coreAction_apply, map_mul, map_mul, map_inv]
  rfl

theorem elementaryAction_embedding (h : H0) (v : E16) :
    sixteenEmbedding (elementaryAction h v) = coreAction h (sixteenEmbedding v) := by
  change (elementaryEquiv.symm (elementaryEquiv
    (aConjugation h (elementaryEquiv.symm v))) : QH) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The action in the published binary basis is literal conjugation in H0. -/
theorem elementaryAction_conjugation (h : H0) (v : E16) :
    i (sixteenEmbedding (elementaryAction h v)) =
      h * i (sixteenEmbedding v) * h⁻¹ := by
  rw [elementaryAction_embedding, i_coreAction]

/-- Evaluate any actor and binary vector using their quaternion coordinates. -/
theorem elementaryAction_coordinates (r : Raw) (a : S3) (v : E16) :
    elementaryAction (⟨projection r, a⟩ : H0) v =
      sixteenDecode (r * rawAut (q8PermAction a) (sixteenRaw v) * r⁻¹) := by
  apply sixteenEmbedding_injective
  rw [elementaryAction_embedding]
  change coreAction (⟨projection r, a⟩ : H0) (projection (sixteenRaw v)) = _
  rw [coreAction_projection]
  exact (sixteenDecode_lift _ (by
    rw [← coreAction_projection]
    exact coreAction_mem_A _ _ (sixteenEmbedding_range ▸ ⟨v,rfl⟩))).symm

theorem conjugate_z (x : QH) : x * z * x⁻¹ = z := by
  have hz : z ∈ Z := (mem_Z z).mpr (Or.inr rfl)
  have hc := (inferInstance : Z.Normal).conj_mem z hz x
  rcases (mem_Z _).mp hc with hc | hc
  · have he : MulAut.conj x z = MulAut.conj x 1 := by simpa using hc
    exact (z_ne_one ((MulAut.conj x).injective he)).elim
  · exact hc

theorem s3Action_z (a : S3) : s3Action a z = z := by
  change s3Action a (leftEmbedding (QuaternionGroup.a 2)) = _
  rw [s3Action_left, q8Aut_neg]
  rfl

theorem coreAction_z (h : H0) : coreAction h z = z := by
  rw [coreAction_apply, s3Action_z, conjugate_z]

theorem i_z_central (h : H0) : h * i z * h⁻¹ = i z := by
  rw [← i_coreAction, coreAction_z]

/-- The marked central involution is the fixed third basis vector. -/
theorem elementaryAction_basis_two (h : H0) :
    elementaryAction h (basisBit 2) = basisBit 2 := by
  apply sixteenEmbedding_injective
  rw [elementaryAction_embedding, sixteenEmbedding_basis_two, coreAction_z]

noncomputable def wreathAut (e : MulAut E4) : MulAut W where
  toFun w := ⟨fun t => e (w.left t), w.right⟩
  invFun w := ⟨fun t => e.symm (w.left t), w.right⟩
  left_inv w := by
    apply RegularWreathProduct.ext
    · funext t; simp
    · rfl
  right_inv w := by
    apply RegularWreathProduct.ext
    · funext t; simp
    · rfl
  map_mul' x y := by
    apply RegularWreathProduct.ext
    · funext t; simp [RegularWreathProduct.mul_left]
    · rfl

theorem wreathMap_s3Action (a : S3) (x : QH) :
    wreathMap (s3Action a x) = wreathAut (s3E4Action a) (wreathMap x) := by
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  apply RegularWreathProduct.ext
  · funext t
    exact (s3E4Action_quotient a (r.left t)).symm
  · rfl

theorem wreathMap_coreAction (h : H0) (x : QH) :
    wreathMap (coreAction h x) = wreathMap h.left *
      wreathAut (s3E4Action h.right) (wreathMap x) * (wreathMap h.left)⁻¹ := by
  rw [coreAction_apply, map_mul, map_mul, map_inv, wreathMap_s3Action]

/-- The full parabolic action on the actual wreath quotient. -/
noncomputable def wreathAction : H0 →* MulAut W where
  toFun h := MulAut.conj (wreathMap h.left) * wreathAut (s3E4Action h.right)
  map_one' := by
    apply MulEquiv.ext
    intro w
    obtain ⟨x,rfl⟩ := wreathMap_surjective w
    change wreathMap (1 : H0).left *
      wreathAut (s3E4Action (1 : H0).right) (wreathMap x) *
      (wreathMap (1 : H0).left)⁻¹ = wreathMap x
    rw [← wreathMap_coreAction, map_one, MulAut.one_apply]
  map_mul' h k := by
    apply MulEquiv.ext
    intro w
    obtain ⟨x,rfl⟩ := wreathMap_surjective w
    change wreathMap (h*k).left *
      wreathAut (s3E4Action (h*k).right) (wreathMap x) *
      (wreathMap (h*k).left)⁻¹ = wreathMap h.left *
      wreathAut (s3E4Action h.right) (wreathMap k.left *
        wreathAut (s3E4Action k.right) (wreathMap x) * (wreathMap k.left)⁻¹) *
      (wreathMap h.left)⁻¹
    rw [← wreathMap_coreAction, ← wreathMap_coreAction,
      ← wreathMap_coreAction, map_mul, MulAut.mul_apply]

theorem wreathAction_apply (h : H0) (w : W) :
    wreathAction h w = wreathMap h.left * wreathAut (s3E4Action h.right) w *
      (wreathMap h.left)⁻¹ := rfl

theorem wreathAction_wreathMap (h : H0) (x : QH) :
    wreathAction h (wreathMap x) = wreathMap (coreAction h x) :=
  (wreathMap_coreAction h x).symm

/-- Compatibility with the published quotient equivalence, on every representative. -/
theorem wreathAction_quotientEquiv (h : H0) (x : QH) :
    wreathAction h (quotientEquiv (QuotientGroup.mk' Z x)) =
      quotientEquiv (QuotientGroup.mk' Z (coreAction h x)) :=
  wreathAction_wreathMap h x

/-- The distinguished diagonal eight is invariant under every element of H0. -/
theorem wreathAction_mem_other (h : H0) (w : W) (hw : w ∈ other) :
    wreathAction h w ∈ other := by
  obtain ⟨x,rfl⟩ := wreathMap_surjective w
  rw [wreathAction_wreathMap]
  exact coreAction_mem_A h x hw

theorem wreathAction_other (h : H0) : other.map (wreathAction h).toMonoidHom = other := by
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact wreathAction_mem_other h w hw
  · intro w hw
    refine ⟨wreathAction h⁻¹ w, wreathAction_mem_other h⁻¹ w hw, ?_⟩
    simp

noncomputable def centerQuotientAction : H0 →* MulAut (QH ⧸ Z) :=
  (MulAut.congr quotientEquiv.symm).toMonoidHom.comp wreathAction

theorem centerQuotientAction_mk (h : H0) (x : QH) :
    centerQuotientAction h (QuotientGroup.mk' Z x) =
      QuotientGroup.mk' Z (coreAction h x) := by
  apply quotientEquiv.injective
  change quotientEquiv (quotientEquiv.symm
    (wreathAction h (quotientEquiv (QuotientGroup.mk' Z x)))) = _
  rw [MulEquiv.apply_symm_apply, wreathAction_quotientEquiv]

theorem centerQuotientAction_equiv (h : H0) (x : QH ⧸ Z) :
    quotientEquiv (centerQuotientAction h x) = wreathAction h (quotientEquiv x) := by
  change quotientEquiv (quotientEquiv.symm _) = _
  exact quotientEquiv.apply_symm_apply _

theorem wreathAction_inr (a : S3) (w : W) :
    wreathAction (SemidirectProduct.inr a) w = wreathAut (s3E4Action a) w := by
  rw [wreathAction_apply]
  change wreathMap 1 * _ * (wreathMap 1)⁻¹ = _
  simp only [map_one, one_mul, inv_one, mul_one]
  rfl

theorem wreathAction_inr_left (a : S3) (w : W) (t : C2) :
    (wreathAction (SemidirectProduct.inr a) w).left t = s3E4Action a (w.left t) := by
  rw [wreathAction_inr]
  rfl

theorem wreathAction_right (h : H0) (w : W) :
    (wreathAction h w).right = w.right := by
  rw [wreathAction_apply]
  change (wreathMap h.left).right * w.right * (wreathMap h.left).right⁻¹ = w.right
  simp [mul_comm]

theorem wreathAction_left (h : H0) (w : W) (t : C2) :
    (wreathAction h w).left t = (wreathMap h.left).left t *
      s3E4Action h.right (w.left ((wreathMap h.left).right⁻¹ * t)) *
      ((wreathMap h.left).left (w.right⁻¹ * t))⁻¹ := by
  rw [wreathAction_apply]
  change (wreathMap h.left).left t *
      s3E4Action h.right (w.left ((wreathMap h.left).right⁻¹ * t)) *
      ((wreathMap h.left).left ((wreathMap h.left).right *
        (((wreathMap h.left).right * w.right)⁻¹ * t)))⁻¹ = _
  congr 3
  simp only [mul_inv_rev, mul_assoc, mul_left_comm, mul_inv_cancel_left]

/-- The elementary subgroup in H0 has the same published coordinates. -/
noncomputable def elementaryImageEquiv : (A.map i) ≃* E16 :=
  (A.equivMapOfInjective i i_inj).symm.trans elementaryEquiv

theorem elementaryImageEquiv_symm_coe (v : E16) :
    (elementaryImageEquiv.symm v : H0) = i (sixteenEmbedding v) := rfl

theorem commutator_pcore_residual : ⁅pCore 2 H0, pResidual 2 H0⁆ = QK.map i := by
  rw [pcore_eq_i_range, commutator_residual_eq_qk]

theorem s3Action_injective : Function.Injective s3Action := by
  intro a b hab
  apply q8PermAction_injective
  apply MulEquiv.ext
  intro q
  apply leftEmbedding_injective
  have h := DFunLike.congr_fun hab (leftEmbedding q)
  simpa only [s3Action_left] using h

end QuaternionSwapModel
