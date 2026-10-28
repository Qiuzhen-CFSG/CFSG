module
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Mathlib.Tactic.NormNum

/-!
# The quaternion central product extended by a factor swap

This model is `(Q₈ wr C₂)/⟨(-1,-1)⟩`, with the quotient and both quaternion
embeddings retained. The embedded central product `QK` is extraspecial of
order 32 and has center the marked subgroup `Z` of order two. The whole
model `QH` has order 64. Its quotient by `Z` is actually isomorphic to
`E₄ wr C₂`, and that isomorphism takes `QK/Z` to the base.

In the wreath quotient, `other` is the diagonal four together with the pure
swap, an elementary eight. Its literal inverse image `A` is elementary of
order sixteen. Four explicit binary generators give `elementaryEquiv`;
in particular the swapping lift has order two and centralizes the paired
quaternion diagonal. The centralizer calculation gives `C_A(QK) = Z`.
The action of `QH` on the quotient base has kernel `QK` and image of order two.

Finite calculations are checked in the kernel on the 128-element covering
wreath product. Quotient descent, the embedded factor presentation, and the
first isomorphism theorem then give the group identifications. This avoids
replacing a central quotient by an unrelated outer-action image.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005),
`refs/quasithin.pdf`. These are intrinsic coordinates. Identifying them with
the actual Aut(M₁₂) parabolic, its two-core, its residual commutator, and the
compatible whole overlap requires a separate model comparison. No such
comparison or full-parabolic invariance is asserted here.
-/

@[expose] public section
namespace QuaternionSwapModel
abbrev C2 := Multiplicative (ZMod 2)
abbrev E4 := Multiplicative (Fin 2 → ZMod 2)
abbrev Raw := RegularWreathProduct (QuaternionGroup 2) C2
abbrev W := RegularWreathProduct E4 C2
instance : Fintype Raw := Fintype.ofEquiv _ (RegularWreathProduct.equivProd _ _).symm
instance : DecidableEq Raw := fun x y => decidable_of_iff
  (x.left = y.left ∧ x.right = y.right) RegularWreathProduct.ext_iff.symm
instance : Fintype W := Fintype.ofEquiv _ (RegularWreathProduct.equivProd _ _).symm
instance : DecidableEq W := fun x y => decidable_of_iff
  (x.left = y.left ∧ x.right = y.right) RegularWreathProduct.ext_iff.symm

def turn : C2 := Multiplicative.ofAdd 1

def killed : Raw := ⟨fun _ => QuaternionGroup.a 2, 1⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def diagonalCenter : Subgroup Raw where
  carrier := {x | x = 1 ∨ x = killed}
  one_mem' := Or.inl rfl
  mul_mem' := by rintro a b (rfl | rfl) (rfl | rfl) <;> decide +kernel
  inv_mem' := by rintro a (rfl | rfl) <;> decide +kernel

instance : diagonalCenter.Normal := by
  have h : ∀ x : Raw, x * killed * x⁻¹ = killed := by decide +kernel
  constructor
  rintro x (rfl | rfl) g
  · exact Or.inl (by simp)
  · exact Or.inr (h g)

abbrev QH := Raw ⧸ diagonalCenter

def projection : Raw →* QH := QuotientGroup.mk' diagonalCenter

theorem projection_eq_iff (x y : Raw) : projection x = projection y ↔
    x⁻¹ * y = 1 ∨ x⁻¹ * y = killed := QuotientGroup.eq

def quaternionQuotient : QuaternionGroup 2 →* E4 where
  toFun q := Multiplicative.ofAdd (match q with
    | .a n => ![(n.val : ZMod 2), 0]
    | .xa n => ![(n.val : ZMod 2), 1])
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def rawWreathMap : Raw →* W where
  toFun w := ⟨fun t => quaternionQuotient (w.left t), w.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp

theorem rawWreathMap_surjective : Function.Surjective rawWreathMap := by
  have hs : Function.Surjective quaternionQuotient := by decide +kernel
  intro w
  choose f hf using fun t => hs (w.left t)
  exact ⟨⟨f, w.right⟩, RegularWreathProduct.ext (funext hf) rfl⟩

def wreathMap : QH →* W := QuotientGroup.lift diagonalCenter rawWreathMap (by
  rintro x (rfl | rfl) <;> decide +kernel)

@[simp] theorem wreathMap_projection (x : Raw) : wreathMap (projection x) = rawWreathMap x := rfl

theorem wreathMap_surjective : Function.Surjective wreathMap := by
  intro w
  obtain ⟨x,rfl⟩ := rawWreathMap_surjective w
  exact ⟨projection x, rfl⟩


def leftRaw : QuaternionGroup 2 →* Raw where
  toFun q := ⟨fun t => if t = 1 then q else 1, 1⟩
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def rightRaw : QuaternionGroup 2 →* Raw where
  toFun q := ⟨fun t => if t = turn then q else 1, 1⟩
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def leftEmbedding : QuaternionGroup 2 →* QH := projection.comp leftRaw
def rightEmbedding : QuaternionGroup 2 →* QH := projection.comp rightRaw

theorem leftEmbedding_injective : Function.Injective leftEmbedding := by
  intro q r h
  change projection (leftRaw q) = projection (leftRaw r) at h
  rw [projection_eq_iff] at h
  have hc : ∀ q r : QuaternionGroup 2,
      (leftRaw q)⁻¹ * leftRaw r = 1 ∨ (leftRaw q)⁻¹ * leftRaw r = killed → q = r := by
    decide +kernel
  exact hc q r h

theorem rightEmbedding_injective : Function.Injective rightEmbedding := by
  intro q r h
  change projection (rightRaw q) = projection (rightRaw r) at h
  rw [projection_eq_iff] at h
  have hc : ∀ q r : QuaternionGroup 2,
      (rightRaw q)⁻¹ * rightRaw r = 1 ∨ (rightRaw q)⁻¹ * rightRaw r = killed → q = r := by
    decide +kernel
  exact hc q r h

def z : QH := leftEmbedding (QuaternionGroup.a 2)
def Z : Subgroup QH := wreathMap.ker
instance : Z.Normal := inferInstanceAs wreathMap.ker.Normal

theorem mem_Z (x : QH) : x ∈ Z ↔ x = 1 ∨ x = z := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  change rawWreathMap x = 1 ↔ projection x = projection 1 ∨
    projection x = projection (leftRaw (QuaternionGroup.a 2))
  simp only [projection_eq_iff]
  have h : ∀ x : Raw, rawWreathMap x = 1 ↔
      (x⁻¹ * 1 = 1 ∨ x⁻¹ * 1 = killed) ∨
      (x⁻¹ * leftRaw (QuaternionGroup.a 2) = 1 ∨
       x⁻¹ * leftRaw (QuaternionGroup.a 2) = killed) := by decide +kernel
  exact h x

theorem z_ne_one : z ≠ 1 := by
  intro h
  have h' : leftEmbedding (QuaternionGroup.a 2) = leftEmbedding 1 := by simpa only [z, map_one] using h
  have := leftEmbedding_injective h'
  contradiction

theorem card_Z : Nat.card Z = 2 := by
  have he : (Z : Set QH) = {1,z} := by
    ext g
    exact (mem_Z g).trans (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff])
  rw [← SetLike.coe_sort_coe, he, Nat.card_coe_set_eq]
  exact Set.ncard_pair z_ne_one.symm

noncomputable def quotientEquiv : QH ⧸ Z ≃* W :=
  QuotientGroup.quotientKerEquivOfSurjective wreathMap wreathMap_surjective

theorem quotientEquiv_mk (x : QH) :
    quotientEquiv (QuotientGroup.mk' Z x) = wreathMap x := rfl

theorem card_W : Nat.card W = 32 := by
  rw [RegularWreathProduct.card]
  norm_num [Nat.card_eq_fintype_card]

theorem card_QH : Nat.card QH = 64 := by
  have h := Z.card_mul_index
  rw [card_Z, Subgroup.index_eq_card, Nat.card_congr quotientEquiv.toEquiv, card_W] at h
  omega

def leftFactor : Subgroup QH := leftEmbedding.range
def rightFactor : Subgroup QH := rightEmbedding.range
def QK : Subgroup QH := leftFactor ⊔ rightFactor

theorem factors_commute : ∀ b ∈ leftFactor, ∀ c ∈ rightFactor, b * c = c * b := by
  rintro _ ⟨q,rfl⟩ _ ⟨r,rfl⟩
  change projection (leftRaw q) * projection (rightRaw r) =
    projection (rightRaw r) * projection (leftRaw q)
  rw [← map_mul, ← map_mul]
  congr 1
  have h : ∀ q r : QuaternionGroup 2, leftRaw q * rightRaw r = rightRaw r * leftRaw q := by
    decide +kernel
  exact h q r

theorem shared_involution : rightEmbedding (QuaternionGroup.a 2) = z := by
  change projection (rightRaw (QuaternionGroup.a 2)) = projection (leftRaw (QuaternionGroup.a 2))
  rw [projection_eq_iff]
  decide +kernel

theorem factors_intersection : leftFactor ⊓ rightFactor = Z := by
  ext x
  rw [mem_Z]
  constructor
  · rintro ⟨⟨q,rfl⟩,⟨r,hr⟩⟩
    change projection (rightRaw r) = projection (leftRaw q) at hr
    rw [projection_eq_iff] at hr
    have h : ∀ q r : QuaternionGroup 2,
        (rightRaw r)⁻¹ * leftRaw q = 1 ∨ (rightRaw r)⁻¹ * leftRaw q = killed →
        q = 1 ∨ q = QuaternionGroup.a 2 := by decide +kernel
    rcases h q r hr with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨leftFactor.one_mem, rightFactor.one_mem⟩
    · exact ⟨⟨_,rfl⟩,⟨_,shared_involution⟩⟩

noncomputable def coreQuaternionData : Subgroup.QuaternionCentralProductData QK where
  left := leftFactor.subgroupOf QK
  right := rightFactor.subgroupOf QK
  left_model := ⟨(Subgroup.subgroupOfEquivOfLe (show leftFactor ≤ QK from le_sup_left)).trans
    (MonoidHom.ofInjective leftEmbedding_injective).symm⟩
  right_model := ⟨(Subgroup.subgroupOfEquivOfLe (show rightFactor ≤ QK from le_sup_right)).trans
    (MonoidHom.ofInjective rightEmbedding_injective).symm⟩
  intersection_card := by
    change Nat.card ((leftFactor ⊓ rightFactor).subgroupOf QK) = 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show leftFactor ⊓ rightFactor ≤ QK from inf_le_left.trans le_sup_left)).toEquiv,
      factors_intersection, card_Z]
  commute := by
    intro b hb c hc
    exact Subtype.ext (factors_commute b.val hb c.val hc)
  span := by
    rw [← Subgroup.subgroupOf_sup (show leftFactor ≤ QK from le_sup_left)
      (show rightFactor ≤ QK from le_sup_right)]
    exact Subgroup.subgroupOf_self _

theorem card_QK : Nat.card QK = 32 := coreQuaternionData.card

theorem extraspecial_QK : IsExtraspecial 2 QK := coreQuaternionData.extraspecial

theorem core_center_image : (Subgroup.center QK).map QK.subtype = Z := by
  rw [coreQuaternionData.center_eq]
  change ((leftFactor ⊓ rightFactor).subgroupOf QK).map QK.subtype = Z
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr
    (show leftFactor ⊓ rightFactor ≤ QK from inf_le_left.trans le_sup_left), factors_intersection]


def base : Subgroup W := (RegularWreathProduct.rightHom : W →* C2).ker
instance : base.Normal := inferInstanceAs (RegularWreathProduct.rightHom : W →* C2).ker.Normal

theorem QK_eq_comap_base : QK = base.comap wreathMap := by
  have hle : QK ≤ base.comap wreathMap := by
    apply sup_le
    · rintro _ ⟨q,rfl⟩
      change (leftRaw q).right = 1
      rfl
    · rintro _ ⟨q,rfl⟩
      change (rightRaw q).right = 1
      rfl
  apply le_antisymm hle
  intro x hx
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  change x.right = 1 at hx
  have h : ∀ x : Raw, x.right = 1 →
      x = leftRaw (x.left 1) * rightRaw (x.left turn) := by decide +kernel
  change projection x ∈ QK
  rw [h x hx, map_mul]
  exact Subgroup.mul_mem_sup (show leftEmbedding (x.left 1) ∈ leftFactor from ⟨_,rfl⟩)
    (show rightEmbedding (x.left turn) ∈ rightFactor from ⟨_,rfl⟩)

instance : QK.Normal := by rw [QK_eq_comap_base]; infer_instance

theorem QK_map_wreathMap : QK.map wreathMap = base := by
  rw [QK_eq_comap_base, Subgroup.map_comap_eq_self_of_surjective wreathMap_surjective]

theorem quotientEquiv_base :
    (QK.map (QuotientGroup.mk' Z)).map quotientEquiv.toMonoidHom = base := by
  rw [Subgroup.map_map]
  exact QK_map_wreathMap

theorem Z_le_QK : Z ≤ QK := factors_intersection ▸ inf_le_left.trans le_sup_left

theorem centralizer_QK : Subgroup.centralizer (QK : Set QH) = Z := by
  apply le_antisymm
  · intro x hx
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
    have hl (q : QuaternionGroup 2) :
        projection (leftRaw q * x) = projection (x * leftRaw q) := by
      simpa only [leftEmbedding, MonoidHom.comp_apply, projection, map_mul] using hx (leftEmbedding q)
        ((show leftFactor ≤ QK from le_sup_left) ⟨q,rfl⟩)
    have hr (q : QuaternionGroup 2) :
        projection (rightRaw q * x) = projection (x * rightRaw q) := by
      simpa only [rightEmbedding, MonoidHom.comp_apply, projection, map_mul] using hx (rightEmbedding q)
        ((show rightFactor ≤ QK from le_sup_right) ⟨q,rfl⟩)
    simp only [projection_eq_iff] at hl hr
    have h : ∀ x : Raw,
        (∀ q, (leftRaw q * x)⁻¹ * (x * leftRaw q) = 1 ∨
          (leftRaw q * x)⁻¹ * (x * leftRaw q) = killed) →
        (∀ q, (rightRaw q * x)⁻¹ * (x * rightRaw q) = 1 ∨
          (rightRaw q * x)⁻¹ * (x * rightRaw q) = killed) → rawWreathMap x = 1 := by
      decide +kernel
    exact h x hl hr
  · intro x hx y hy
    rw [mem_Z] at hx
    rcases hx with rfl | rfl
    · simp
    · obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter y
      change projection y * projection (leftRaw (QuaternionGroup.a 2)) =
        projection (leftRaw (QuaternionGroup.a 2)) * projection y
      rw [← map_mul, ← map_mul, projection_eq_iff]
      have h : ∀ y : Raw,
          (y * leftRaw (QuaternionGroup.a 2))⁻¹ * (leftRaw (QuaternionGroup.a 2) * y) = 1 ∨
          (y * leftRaw (QuaternionGroup.a 2))⁻¹ * (leftRaw (QuaternionGroup.a 2) * y) = killed := by
        decide +kernel
      exact h y


/-- The diagonal base together with the actual swapping involution. -/
def other : Subgroup W where
  carrier := {w | w.left 1 = w.left turn}
  one_mem' := rfl
  mul_mem' := by
    have h : ∀ x y : W, x.left 1 = x.left turn → y.left 1 = y.left turn →
        (x*y).left 1 = (x*y).left turn := by decide +kernel
    exact fun x y hx hy => h x y hx hy
  inv_mem' := by
    have h : ∀ x : W, x.left 1 = x.left turn → x⁻¹.left 1 = x⁻¹.left turn := by
      decide +kernel
    exact fun x hx => h x hx

instance : other.Normal := by
  have h : ∀ x g : W, x.left 1 = x.left turn →
      (g*x*g⁻¹).left 1 = (g*x*g⁻¹).left turn := by decide +kernel
  exact ⟨fun x hx g => h x g hx⟩

def A : Subgroup QH := other.comap wreathMap
instance : A.Normal := inferInstanceAs (other.comap wreathMap).Normal

abbrev E16 := Multiplicative (Fin 4 → ZMod 2)

def diagonalRaw : QuaternionGroup 2 →* Raw where
  toFun q := ⟨fun _ => q, 1⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

def swapRaw : Raw := ⟨1, turn⟩
def swap : QH := projection swapRaw

def sixteenRaw (v : E16) : Raw :=
  diagonalRaw (QuaternionGroup.a 1) ^ (v.toAdd 0).val *
  diagonalRaw (QuaternionGroup.xa 0) ^ (v.toAdd 1).val *
  leftRaw (QuaternionGroup.a 2) ^ (v.toAdd 2).val * swapRaw ^ (v.toAdd 3).val

def sixteenEmbedding : E16 →* QH where
  toFun v := projection (sixteenRaw v)
  map_one' := by
    change projection (sixteenRaw 1) = projection 1
    rw [projection_eq_iff]
    decide +kernel
  map_mul' v w := by
    change projection (sixteenRaw (v*w)) = projection (sixteenRaw v) * projection (sixteenRaw w)
    rw [← map_mul, projection_eq_iff]
    have h : ∀ v w : E16,
        (sixteenRaw (v*w))⁻¹ * (sixteenRaw v * sixteenRaw w) = 1 ∨
        (sixteenRaw (v*w))⁻¹ * (sixteenRaw v * sixteenRaw w) = killed := by decide +kernel
    exact h v w

theorem sixteenEmbedding_injective : Function.Injective sixteenEmbedding := by
  intro v w h
  change projection (sixteenRaw v) = projection (sixteenRaw w) at h
  rw [projection_eq_iff] at h
  have he : ∀ v w : E16,
      (sixteenRaw v)⁻¹ * sixteenRaw w = 1 ∨ (sixteenRaw v)⁻¹ * sixteenRaw w = killed → v = w := by
    decide +kernel
  exact he v w h

theorem sixteenEmbedding_range : sixteenEmbedding.range = A := by
  ext x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  change (∃ v : E16, projection (sixteenRaw v) = projection x) ↔
    (rawWreathMap x).left 1 = (rawWreathMap x).left turn
  simp only [projection_eq_iff]
  have h : ∀ x : Raw,
      (∃ v : E16, (sixteenRaw v)⁻¹ * x = 1 ∨ (sixteenRaw v)⁻¹ * x = killed) ↔
      (rawWreathMap x).left 1 = (rawWreathMap x).left turn := by decide +kernel
  exact h x

noncomputable def elementaryEquiv : A ≃* E16 :=
  (MulEquiv.subgroupCongr sixteenEmbedding_range.symm).trans
    (MonoidHom.ofInjective sixteenEmbedding_injective).symm

theorem card_A : Nat.card A = 16 := by
  rw [Nat.card_congr elementaryEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

instance : IsElementaryAbelian 2 A where
  toIsMulCommutative := ⟨⟨fun x y => elementaryEquiv.injective (by
    simp only [map_mul]; exact mul_comm _ _)⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply elementaryEquiv.injective
    rw [map_pow, map_one]
    have h : ∀ x : E16, x^2 = 1 := by decide +kernel
    exact h _)

theorem swap_square : swap ^ 2 = 1 := by
  change (projection swapRaw)^2 = projection 1
  rw [← map_pow]
  congr 1

theorem swap_mem_A : swap ∈ A := by
  change (rawWreathMap swapRaw).left 1 = (rawWreathMap swapRaw).left turn
  decide +kernel

theorem swap_not_mem_QK : swap ∉ QK := by
  rw [QK_eq_comap_base]
  change ¬ (rawWreathMap swapRaw).right = 1
  decide +kernel

theorem swap_centralizes_diagonal (q : QuaternionGroup 2) :
    swap * projection (diagonalRaw q) = projection (diagonalRaw q) * swap := by
  change projection swapRaw * projection (diagonalRaw q) = projection (diagonalRaw q) * projection swapRaw
  rw [← map_mul, ← map_mul]
  congr 1
  have h : ∀ q : QuaternionGroup 2, swapRaw * diagonalRaw q = diagonalRaw q * swapRaw := by
    decide +kernel
  exact h q

theorem Z_le_A : Z ≤ A := by
  intro x hx
  change wreathMap x ∈ other
  rw [show wreathMap x = 1 from hx]
  exact other.one_mem

theorem A_centralizer_QK : A ⊓ Subgroup.centralizer (QK : Set QH) = Z := by
  rw [centralizer_QK, inf_eq_right.mpr Z_le_A]


theorem A_map_wreathMap : A.map wreathMap = other :=
  Subgroup.map_comap_eq_self_of_surjective wreathMap_surjective other

theorem quotientEquiv_other :
    (A.map (QuotientGroup.mk' Z)).map quotientEquiv.toMonoidHom = other := by
  rw [Subgroup.map_map]
  exact A_map_wreathMap

private theorem other_value (w : other) (t : C2) : w.val.left t = w.val.left 1 := by
  have h : ∀ w : W, w.left 1 = w.left turn → ∀ t : C2, w.left t = w.left 1 := by
    decide +kernel
  exact h w.val w.property t

def otherEquiv : other ≃* E4 × C2 where
  toFun w := (w.val.left 1, w.val.right)
  invFun v := ⟨⟨fun _ => v.1, v.2⟩, rfl⟩
  left_inv w := by
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · exact funext (fun t => (other_value w t).symm)
    · rfl
  right_inv _ := rfl
  map_mul' x y := by
    apply Prod.ext
    · change x.val.left 1 * y.val.left (x.val.right⁻¹ * 1) = x.val.left 1 * y.val.left 1
      rw [other_value y (x.val.right⁻¹ * 1)]
    · rfl

theorem card_other : Nat.card other = 8 := by
  rw [Nat.card_congr otherEquiv.toEquiv]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card]

instance : IsElementaryAbelian 2 other where
  toIsMulCommutative := ⟨⟨fun x y => otherEquiv.injective (by
    simp only [map_mul]; exact mul_comm _ _)⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply otherEquiv.injective
    rw [map_pow, map_one]
    have h : ∀ x : E4 × C2, x^2 = 1 := by decide +kernel
    exact h _)

/-- The center of the wreath quotient is the diagonal four in its base. -/
theorem center_W : Subgroup.center W = other ⊓ base := by
  ext w
  rw [Subgroup.mem_center_iff]
  change (∀ v : W, v*w = w*v) ↔ w.left 1 = w.left turn ∧ w.right = 1
  have h : ∀ w : W, (∀ v : W, v*w = w*v) ↔ w.left 1 = w.left turn ∧ w.right = 1 := by
    decide +kernel
  exact h w

/-- The quotient coordinates preserve actual inner conjugation. -/
theorem wreathMap_conj (g x : QH) :
    wreathMap (g*x*g⁻¹) = wreathMap g * wreathMap x * (wreathMap g)⁻¹ := by
  simp only [map_mul, map_inv]


/-- The chosen lift really interchanges the two embedded quaternion factors. -/
theorem swap_left (q : QuaternionGroup 2) :
    swap * leftEmbedding q * swap⁻¹ = rightEmbedding q := by
  change projection swapRaw * projection (leftRaw q) * (projection swapRaw)⁻¹ =
    projection (rightRaw q)
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  have h : ∀ q : QuaternionGroup 2, swapRaw * leftRaw q * swapRaw⁻¹ = rightRaw q := by
    decide +kernel
  exact h q

/-- The actual inner action of the two-group on the base of its central quotient. -/
noncomputable def baseAction : QH →* MulAut base := MulAut.conjNormal.comp wreathMap

theorem baseAction_apply (g : QH) (b : base) :
    (baseAction g b : W) = wreathMap g * (b : W) * (wreathMap g)⁻¹ := rfl

theorem baseAction_ker : baseAction.ker = QK := by
  rw [QK_eq_comap_base]
  ext g
  rw [MonoidHom.mem_ker]
  have hiff : baseAction g = 1 ↔
      ∀ b : W, b.right = 1 → wreathMap g * b * (wreathMap g)⁻¹ = b := by
    constructor
    · intro h b hb
      have he := congrArg (fun a : MulAut base => (a ⟨b,hb⟩ : W)) h
      exact he
    · intro h
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      exact h b.val b.property
  rw [hiff]
  change (∀ b : W, b.right = 1 → wreathMap g * b * (wreathMap g)⁻¹ = b) ↔
    (wreathMap g).right = 1
  have h : ∀ w : W, (∀ b : W, b.right = 1 → w*b*w⁻¹ = b) ↔ w.right = 1 := by
    decide +kernel
  exact h (wreathMap g)

/-- In particular this action has order two, not the full order-72 outer image. -/
theorem card_baseAction_range : Nat.card baseAction.range = 2 := by
  have h := baseAction.ker.card_mul_index
  rw [Subgroup.index_ker, baseAction_ker, card_QK, card_QH] at h
  omega

noncomputable def quotientBaseAction : QH ⧸ QK →* MulAut base :=
  QuotientGroup.lift QK baseAction (by
    intro g hg
    exact (show g ∈ baseAction.ker from baseAction_ker.symm ▸ hg))

theorem quotientBaseAction_mk (g : QH) :
    quotientBaseAction (QuotientGroup.mk' QK g) = baseAction g := rfl


/-- A coordinate vector with one nonzero binary entry. -/
def basisBit (i : Fin 4) : E16 := Multiplicative.ofAdd (fun j => if j = i then 1 else 0)

theorem sixteenEmbedding_basis_two : sixteenEmbedding (basisBit 2) = z := by
  change projection (sixteenRaw (basisBit 2)) = projection (leftRaw (QuaternionGroup.a 2))
  apply congrArg projection
  decide +kernel

theorem sixteenEmbedding_basis_three : sixteenEmbedding (basisBit 3) = swap := by
  change projection (sixteenRaw (basisBit 3)) = projection swapRaw
  apply congrArg projection
  decide +kernel

/-- The elementary coordinates retain the explicit four-generator map. -/
theorem elementaryEquiv_symm_coe (v : E16) :
    (elementaryEquiv.symm v : QH) = sixteenEmbedding v := rfl

theorem A_not_le_QK : ¬ A ≤ QK := fun h => swap_not_mem_QK (h swap_mem_A)

end QuaternionSwapModel
