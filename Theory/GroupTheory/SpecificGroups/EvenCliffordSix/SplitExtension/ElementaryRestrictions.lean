module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension

/-!
# Central layers of elementary restrictions of the signed extension

Let H contain the embedded cyclic-four center, have order 64, and have all
squares in the embedded sign subgroup. Its Frattini subgroup is exactly that
sign subgroup: squares give one inclusion and the volume square gives the
other. Consequently the sign and cyclic-four quotients are elementary of
orders 32 and 16. The projection of H to A₆ is elementary, and it fixes the
vector coordinates of H's intersection with the Clifford radical.

These reductions retain the actual subgroup H and both literal central
layers. They do not assert that the embedded C₄ is H's full center or that H
has the Clifford isomorphism type; those are the remaining recognition steps.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.2(6a),
printed pp.410 and 412. The actual pair-core application is in the separate
CFSG `FixedPairQuartic.ModelRestriction.Recognition` module.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace EvenCliffordSix.SplitExtension.ElementaryRestrictions

/-- The original cyclic-four layer, restricted to H. -/
abbrev centralIn (H : Subgroup SplitExtension) : Subgroup H := central.subgroupOf H
/-- The original sign layer, restricted to H. -/
abbrev signIn (H : Subgroup SplitExtension) : Subgroup H := sign.subgroupOf H

theorem centralIn_le_center (H : Subgroup SplitExtension) : centralIn H ≤ center H := by
  intro z hz
  exact mem_center_iff.mpr fun x =>
    Subtype.ext (mem_center_iff.mp (central_le_center hz) x)

theorem signIn_le_centralIn (H : Subgroup SplitExtension) : signIn H ≤ centralIn H :=
  fun _ hx => sign_le_central hx

theorem signIn_le_center (H : Subgroup SplitExtension) : signIn H ≤ center H :=
  (signIn_le_centralIn H).trans (centralIn_le_center H)

instance centralIn_normal (H : Subgroup SplitExtension) : (centralIn H).Normal where
  conj_mem z hz x := by
    have hc := mem_center_iff.mp (centralIn_le_center H hz) x
    simpa only [hc, mul_inv_cancel_right] using hz

instance signIn_normal (H : Subgroup SplitExtension) : (signIn H).Normal where
  conj_mem z hz x := by
    have hc := mem_center_iff.mp (signIn_le_center H hz) x
    simpa only [hc, mul_inv_cancel_right] using hz

/-- The central layer is an actual cyclic group of order four. -/
noncomputable def centralInFourEquiv (H : Subgroup SplitExtension) (hZ : central ≤ H) :
    centralIn H ≃* Multiplicative (ZMod 4) :=
  (subgroupOfEquivOfLe hZ).trans
    (((center Model).equivMapOfInjective radicalEmbedding radicalEmbedding_injective).symm.trans
      Structure.centerFourEquiv)

theorem centralIn_cyclic (H : Subgroup SplitExtension) (hZ : central ≤ H) :
    IsCyclic (centralIn H) :=
  isCyclic_of_surjective (centralInFourEquiv H hZ).symm
    (centralInFourEquiv H hZ).symm.surjective

theorem centralIn_card (H : Subgroup SplitExtension) (hZ : central ≤ H) :
    Nat.card (centralIn H) = 4 :=
  (Nat.card_congr (subgroupOfEquivOfLe hZ).toEquiv).trans central_card

theorem signIn_card (H : Subgroup SplitExtension) (hZ : central ≤ H) :
    Nat.card (signIn H) = 2 :=
  (Nat.card_congr (subgroupOfEquivOfLe (sign_le_central.trans hZ)).toEquiv).trans sign_card

/-- Volume is retained as an element of the original subgroup. -/
def volumeIn (H : Subgroup SplitExtension) (hZ : central ≤ H) : H :=
  ⟨radicalEmbedding volume, hZ (mem_map_of_mem _ Structure.volume_mem_center)⟩

theorem signIn_eq_zpowers_volume_sq (H : Subgroup SplitExtension) (hZ : central ≤ H) :
    signIn H = zpowers (volumeIn H hZ ^ 2) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, he⟩ := hx
    rcases (mem_signKernel_iff s).mp hs with rfl | rfl
    · have hx1 : x = 1 := Subtype.ext (he.symm.trans radicalEmbedding.map_one)
      simpa only [hx1] using (zpowers (volumeIn H hZ ^ 2)).one_mem
    · have hxs : x = volumeIn H hZ ^ 2 := by
        apply Subtype.ext
        exact he.symm.trans (by
          change _ = radicalEmbedding volume ^ 2
          rw [← map_pow, volume_sq])
      rw [hxs]
      exact mem_zpowers _
  · apply zpowers_le.mpr
    change radicalEmbedding volume ^ 2 ∈ sign
    rw [← map_pow, volume_sq]
    exact mem_map_of_mem _ ((mem_signKernel_iff involution).mpr (Or.inr rfl))

variable (H : Subgroup SplitExtension)
variable (hZ : central ≤ H) (hcard : Nat.card H = 64)
variable (hsq : ∀ x ∈ H, x ^ 2 ∈ sign)

include hsq in
theorem commutator_le_signIn : _root_.commutator H ≤ signIn H := by
  apply commutator_le_closure_squares.trans
  apply (closure_le _).mpr
  rintro _ ⟨x, rfl⟩
  exact hsq x x.property

include hZ hcard hsq in
/-- The sign is forced by the volume square, not assumed to be Frattini. -/
theorem frattini_eq_signIn : frattini H = signIn H := by
  rw [(IsPGroup.of_card (p := 2) (n := 6) hcard).frattini_eq_closure_squares]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact hsq x x.property
  · rw [signIn_eq_zpowers_volume_sq H hZ]
    exact zpowers_le.mpr (subset_closure ⟨volumeIn H hZ, rfl⟩)

include hsq in
theorem signQuotient_elementary : IsElementaryAbelian 2 (H ⧸ signIn H) where
  toIsMulCommutative := Normal.quotient_commutative_iff_commutator_le.mpr
    (commutator_le_signIn H hsq)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (signIn H) x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq x x.property))

include hsq in
theorem centralQuotient_elementary : IsElementaryAbelian 2 (H ⧸ centralIn H) where
  toIsMulCommutative := Normal.quotient_commutative_iff_commutator_le.mpr
    ((commutator_le_signIn H hsq).trans (signIn_le_centralIn H))
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (centralIn H) x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (sign_le_central (hsq x x.property)))

include hZ hcard in
theorem signQuotient_card : Nat.card (H ⧸ signIn H) = 32 := by
  have h := (signIn H).card_mul_index
  rw [signIn_card H hZ, hcard, index_eq_card] at h
  omega

include hZ hcard in
theorem centralQuotient_card : Nat.card (H ⧸ centralIn H) = 16 := by
  have h := (centralIn H).card_mul_index
  rw [centralIn_card H hZ, hcard, index_eq_card] at h
  omega

include hsq in
theorem pow_four (x : H) : x ^ 4 = 1 := by
  have ht : Nat.card sign = 2 := sign_card
  have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨(x : SplitExtension) ^ 2,
    hsq x x.property⟩ : sign)))
  apply Subtype.ext
  simpa only [ht, coe_pow, coe_one, ← pow_mul] using h

/-- The projection uses the literal A₆ factor of the signed extension. -/
abbrev actorImage : Subgroup A := H.map SemidirectProduct.rightHom

include hsq in
theorem actorImage_elementary : IsElementaryAbelian 2 (actorImage H) := by
  have hpow (a : actorImage H) : a ^ 2 = 1 := by
    obtain ⟨x, hx, he⟩ := a.property
    apply Subtype.ext
    change (a : A) ^ 2 = 1
    rw [← he, ← map_pow]
    exact (mem_sign_iff (x ^ 2)).mp (hsq x hx) |>.2
  exact {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }

theorem centralIn_eq_zpowers_volume (hZ : central ≤ H) :
    centralIn H = zpowers (volumeIn H hZ) := by
  apply (map_injective H.subtype_injective)
  rw [subgroupOf_map_subtype, inf_eq_left.mpr hZ, MonoidHom.map_zpowers]
  change (center Model).map radicalEmbedding = zpowers (radicalEmbedding volume)
  rw [Structure.center_eq_zpowers_volume, MonoidHom.map_zpowers]

theorem volumeIn_order (hZ : central ≤ H) : orderOf (volumeIn H hZ) = 4 :=
  (Subgroup.orderOf_coe (volumeIn H hZ)).symm.trans
    ((orderOf_injective radicalEmbedding radicalEmbedding_injective volume).trans volume_order)

include hsq in
theorem square_mem_volume_sq (hZ : central ≤ H) (x : H) :
    x ^ 2 ∈ zpowers (volumeIn H hZ ^ 2) := by
  rw [← signIn_eq_zpowers_volume_sq H hZ]
  exact hsq x x.property

include hsq in
theorem mul_vectors_commute (x y : SplitExtension) (hx : x ∈ H) (hy : y ∈ H) :
    (x * y).left.vector = (y * x).left.vector := by
  have hc : ⁅x, y⁆ ∈ sign := commutator_le_signIn H hsq
    (commutator_mem_commutator (mem_top (⟨x,hx⟩ : H)) (mem_top (⟨y,hy⟩ : H)))
  obtain ⟨s, hs, he⟩ := hc
  have hv := (mem_signKernel s).mp hs
  have hh : radicalEmbedding s * (y * x) = x * y := by
    rw [he]
    simp [commutatorElement_def, mul_assoc]
  have hvec := congrArg (fun a : SplitExtension => a.left.vector) hh
  simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, map_one, MulAut.one_apply, mul_vector, hv, zero_add]
    using hvec.symm

include hsq in
/-- The actor fixes every vector represented in the radical intersection. -/
theorem radicalVector_fixed (x : SplitExtension) (hx : x ∈ H)
    (m : Model) (hm : radicalEmbedding m ∈ H) :
    permuteVector x.right.val m.vector = m.vector := by
  have h := mul_vectors_commute H hsq x (radicalEmbedding m) hx hm
  change x.left.vector + permuteVector x.right.val m.vector =
    m.vector + (action 1 x.left).vector at h
  rw [map_one, MulAut.one_apply, add_comm m.vector] at h
  exact add_left_cancel h

/-- The literal intersection with the embedded Clifford radical, in its own coordinates. -/
abbrev radicalPart : Subgroup Model := H.comap radicalEmbedding
/-- Vector coordinates of the radical intersection, retaining the augmentation projection. -/
abbrev radicalVectors : Subgroup (Multiplicative V) := (radicalPart H).map projection

include hsq in
theorem actorImage_fixes_radicalVectors (a : A) (ha : a ∈ actorImage H)
    (v : Multiplicative V) (hv : v ∈ radicalVectors H) :
    permuteVector a.val v.toAdd = v.toAdd := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨m, hm, rfl⟩ := hv
  exact radicalVector_fixed H hsq x hx m hm

/-- The radical intersection identifies with the kernel of the actual actor projection. -/
def radicalPartEquivKernel : radicalPart H ≃*
    (SemidirectProduct.rightHom.comp H.subtype).ker where
  toFun m := ⟨⟨radicalEmbedding m, m.property⟩, by rfl⟩
  invFun x := ⟨x.val.val.left, by
    have hr : x.val.val.right = 1 := x.property
    have he : radicalEmbedding x.val.val.left = x.val.val :=
      SemidirectProduct.ext rfl hr.symm
    change radicalEmbedding x.val.val.left ∈ H
    rw [he]
    exact x.val.property⟩
  left_inv m := rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact SemidirectProduct.ext rfl x.property.symm
  map_mul' m n := by
    apply Subtype.ext
    apply Subtype.ext
    exact radicalEmbedding.map_mul m n

theorem radicalPart_card_mul_actorImage_card :
    Nat.card (radicalPart H) * Nat.card (actorImage H) = Nat.card H := by
  have h := (SemidirectProduct.rightHom.comp H.subtype).ker.card_mul_index
  rw [index_ker, ← Nat.card_congr (radicalPartEquivKernel H).toEquiv] at h
  rw [MonoidHom.range_comp, range_subtype] at h
  exact h

theorem radicalVectors_card (hZ : central ≤ H) :
    2 * Nat.card (radicalVectors H) = Nat.card (radicalPart H) := by
  have hker : (projection.comp (radicalPart H).subtype).ker =
      signKernel.subgroupOf (radicalPart H) := rfl
  have hs : signKernel ≤ radicalPart H := fun _ hm =>
    hZ (sign_le_central (mem_map_of_mem _ hm))
  have hcard : Nat.card (projection.comp (radicalPart H).subtype).ker = 2 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hs).toEquiv, signKernel_card]
  have h := (projection.comp (radicalPart H).subtype).ker.card_mul_index
  rw [index_ker, hcard] at h
  rw [MonoidHom.range_comp, range_subtype] at h
  exact h

end EvenCliffordSix.SplitExtension.ElementaryRestrictions
