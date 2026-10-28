module
public import Theory.SpecificGroups.SymmetricFourWreath.Planes
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PResidual.Quotient
/-!
# The central quotient action of a dihedral square with an elementary factor

For S isomorphic to E × D₈ × D₈ with E elementary abelian, every induced
automorphism on S/Z(S) has fourth power one. The four products of the two
Klein four-subgroups in each dihedral factor exhaust the largest elementary
subgroups. Opposite pairs are characterized by intersection equal to Z(S),
so their permutation action has exponent dividing four. An automorphism fixing
all four subgroups fixes the four axis lines modulo the center; the involutions
on these lines generate the two dihedral factors. This gives trivial action
on the quotient without assuming preservation of the chosen direct factors.

Transport uses the supplied group isomorphism and the literal characteristic
center quotient. The resulting two-group image kills the two-residual of any
actor. For the actual normalizer action, this residual consequently normalizes
every intermediate subgroup containing the embedded center of S.

Source: Aschbacher–Smith 5.1.7(1), printed pp.633–634. This supplies the
odd-residual consequence of the Krull–Schmidt paragraph directly from the
intrinsic four-subgroup geometry.
-/
public section
namespace DihedralSquareAutomorphisms
open Subgroup SymmetricFourWreath
open scoped IsMulCommutative
private abbrev Model (D : Type*) := (D8 × D8) × D

private def axisCenter : Subgroup D8 := plane true ⊓ plane false

private instance axisCenter_decidable : DecidablePred (· ∈ axisCenter) := fun x =>
  inferInstanceAs (Decidable (x ∈ plane true ∧ x ∈ plane false))

private def family (D : Type*) [Group D] (i j : Bool) : Subgroup (Model D) :=
  ((plane i).prod (plane j)).prod ⊤

private def intersection (D : Type*) [Group D] : Subgroup (Model D) :=
  (axisCenter.prod axisCenter).prod ⊤

private theorem elementary_plane (A : Subgroup D8) (hA : IsElementaryAbelian 2 A) :
    ∃ i, A ≤ plane i := by
  by_cases ht : A ≤ plane true
  · exact ⟨true,ht⟩
  obtain ⟨x,hx,hxt⟩ := SetLike.not_le_iff_exists.mp ht
  refine ⟨false,?_⟩
  intro y hy
  have hlocal : ∀ x y : D8, x^2=1 → y^2=1 → x*y=y*x → x∉plane true → y∈plane false := by
    decide +kernel
  let : IsElementaryAbelian 2 A := hA
  exact hlocal x y (elemPow_eq_one_of_isElementaryAbelian x hx)
    (elemPow_eq_one_of_isElementaryAbelian y hy)
    (congrArg Subtype.val (hA.is_comm.comm (⟨x,hx⟩ : A) ⟨y,hy⟩)) hxt

variable (D : Type*) [Group D]

private theorem elementary_cover (A : Subgroup (Model D)) (hA : IsElementaryAbelian 2 A) :
    ∃ i j, A ≤ family D i j := by
  let f : Model D →* D8 := (MonoidHom.fst D8 D8).comp (MonoidHom.fst (D8×D8) D)
  let g : Model D →* D8 := (MonoidHom.snd D8 D8).comp (MonoidHom.fst (D8×D8) D)
  let : IsElementaryAbelian 2 A := hA
  obtain ⟨i,hi⟩ := elementary_plane (A.map f) (IsElementaryAbelian.map f)
  obtain ⟨j,hj⟩ := elementary_plane (A.map g) (IsElementaryAbelian.map g)
  refine ⟨i,j,?_⟩
  intro a ha
  exact ⟨⟨hi (mem_map_of_mem f ha),hj (mem_map_of_mem g ha)⟩,mem_top _⟩

private theorem prod_card {A B : Type*} [Group A] [Group B] (P : Subgroup A) (Q : Subgroup B) :
    Nat.card (P.prod Q) = Nat.card P * Nat.card Q := by
  rw [Nat.card_congr (prodEquiv P Q).toEquiv,Nat.card_prod]

private theorem family_card (i j : Bool) : Nat.card (family D i j) = 16 * Nat.card D := by
  rw [family,prod_card,prod_card,card_plane,card_plane,
    Nat.card_congr (topEquiv : (⊤ : Subgroup D) ≃* D).toEquiv]


variable [Finite D] [IsElementaryAbelian 2 D]

private instance family_elementary (i j : Bool) : IsElementaryAbelian 2 (family D i j) where
  is_comm.comm := by
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
          (⟨x.1.1.1,x.2.1.1⟩ : plane i) ⟨y.1.1.1,y.2.1.1⟩)
      · exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
          (⟨x.1.1.2,x.2.1.2⟩ : plane j) ⟨y.1.1.2,y.2.1.2⟩)
    · exact IsMulCommutative.is_comm.comm _ _
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (elemPow_eq_one_of_isElementaryAbelian x.1.1.1 x.2.1.1)
        (elemPow_eq_one_of_isElementaryAbelian x.1.1.2 x.2.1.2)
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 D) x.1.2)

omit [Finite D] in
private theorem family_injective : Function.Injective (fun i : Bool × Bool => family D i.1 i.2) := by
  intro i j he
  have hi : ∀ x : D8,x ∈ plane i.1 ↔ x ∈ plane j.1 := by
    intro x
    have hh := SetLike.ext_iff.mp he ((x,1),1)
    simpa only [family,mem_prod,mem_top,one_mem,and_true] using hh
  have hj : ∀ x : D8,x ∈ plane i.2 ↔ x ∈ plane j.2 := by
    intro x
    have hh := SetLike.ext_iff.mp he ((1,x),1)
    simpa only [family,mem_prod,mem_top,one_mem,true_and,and_true] using hh
  have hcheck : ∀ a b : Bool,(∀ x : D8,x ∈ plane a ↔ x ∈ plane b) → a=b := by decide +kernel
  exact Prod.ext (hcheck _ _ hi) (hcheck _ _ hj)

omit [Finite D] in
private theorem center_eq : center (Model D) = intersection D := by
  have hD : center D = ⊤ := by ext x; simp only [mem_center_iff,mem_top,iff_true]; exact fun y => IsMulCommutative.is_comm.comm _ _
  have he : center D8 = axisCenter := by ext x; exact (by decide +kernel : ∀ x : D8, x ∈ center D8 ↔ x ∈ axisCenter) x
  change center ((D8 × D8) × D) = _
  rw [Subgroup.center_prod,Subgroup.center_prod,he,hD]
  rfl

omit [Finite D] in
private theorem opposite_iff (i j : Bool × Bool) :
    family D i.1 i.2 ⊓ family D j.1 j.2 = center (Model D) ↔ j=(!i.1,!i.2) := by
  rw [center_eq]
  have hc : ∀ i j : Bool × Bool,
      (∀ u v : D8, ((u∈plane i.1 ∧ v∈plane i.2) ∧ (u∈plane j.1 ∧ v∈plane j.2)) ↔
        (u∈axisCenter ∧ v∈axisCenter)) ↔ j=(!i.1,!i.2) := by decide +kernel
  constructor
  · intro he
    apply (hc i j).mp
    intro u v
    have hh := SetLike.ext_iff.mp he ((u,v),1)
    simpa only [family,intersection,mem_inf,mem_prod,mem_top,and_true] using hh
  · intro he
    ext x
    simpa only [family,intersection,mem_inf,mem_prod,mem_top,and_true] using
      (hc i j).mpr he x.1.1 x.1.2

private theorem exists_family_image (a : MulAut (Model D)) (i : Bool × Bool) :
    ∃ j : Bool × Bool,(family D i.1 i.2).map a.toMonoidHom = family D j.1 j.2 := by
  obtain ⟨j,k,hjk⟩ := elementary_cover D ((family D i.1 i.2).map a.toMonoidHom)
    (IsElementaryAbelian.map a.toMonoidHom)
  refine ⟨(j,k),eq_of_le_of_card_ge hjk ?_⟩
  rw [card_map_of_injective a.injective,family_card,family_card]

private noncomputable def familyMap (a : MulAut (Model D)) (i : Bool × Bool) : Bool × Bool :=
  Classical.choose (exists_family_image D a i)

private theorem familyMap_spec (a : MulAut (Model D)) (i : Bool × Bool) :
    (family D i.1 i.2).map a.toMonoidHom = family D (familyMap D a i).1 (familyMap D a i).2 :=
  Classical.choose_spec (exists_family_image D a i)

private theorem familyMap_injective (a : MulAut (Model D)) : Function.Injective (familyMap D a) := by
  intro i j he
  apply family_injective D
  apply map_injective (f := a.toMonoidHom) a.injective
  rw [familyMap_spec,familyMap_spec,he]

private noncomputable def familyAction : MulAut (Model D) →* Equiv.Perm (Bool × Bool) where
  toFun a := Equiv.ofBijective (familyMap D a)
    ⟨familyMap_injective D a,Finite.surjective_of_injective (familyMap_injective D a)⟩
  map_one' := by
    apply Equiv.ext
    intro i
    apply family_injective D
    exact (familyMap_spec D 1 i).symm.trans (by ext x; simp)
  map_mul' a b := by
    apply Equiv.ext
    intro i
    apply family_injective D
    change family D (familyMap D (a*b) i).1 (familyMap D (a*b) i).2 =
      family D (familyMap D a (familyMap D b i)).1 (familyMap D a (familyMap D b i)).2
    rw [←familyMap_spec,←familyMap_spec,←familyMap_spec,map_map]
    rfl

private theorem familyAction_spec (a : MulAut (Model D)) (i : Bool × Bool) :
    (family D i.1 i.2).map a.toMonoidHom = family D (familyAction D a i).1 (familyAction D a i).2 :=
  familyMap_spec D a i

private theorem familyAction_opposite (a : MulAut (Model D)) (i : Bool × Bool) :
    familyAction D a (!i.1,!i.2) = (!(familyAction D a i).1,!(familyAction D a i).2) := by
  apply (opposite_iff D _ _).mp
  rw [←familyAction_spec,←familyAction_spec,←Subgroup.map_inf _ _ _ a.injective,
    (opposite_iff D i (!i.1,!i.2)).mpr rfl]
  exact characteristic_iff_map_eq.mp inferInstance a

private theorem familyAction_pow_four (a : MulAut (Model D)) : familyAction D a ^ 4 = 1 := by
  have hc : ∀ p : Equiv.Perm (Bool × Bool),
      (∀ i,p (!i.1,!i.2)=(!(p i).1,!(p i).2)) → p^4=1 := by decide +kernel
  exact hc _ (familyAction_opposite D a)

private def axisPair (b : Bool) : D8 →* D8 × D8 :=
  if b then MonoidHom.inl D8 D8 else MonoidHom.inr D8 D8

private def axisMap (b : Bool) : D8 →* Model D :=
  (MonoidHom.inl (D8 × D8) D).comp (axisPair b)

omit [Finite D] [IsElementaryAbelian 2 D] in
private theorem center_iff (a : MulAut (Model D)) (x : Model D) :
    a x ∈ center (Model D) ↔ x ∈ center (Model D) := by
  have hm : (center (Model D)).map a.toMonoidHom = center (Model D) :=
    characteristic_iff_map_eq.mp inferInstance a
  constructor
  · intro hx
    rw [←hm] at hx
    obtain ⟨y,hy,he⟩ := hx
    exact a.injective he ▸ hy
  · intro hx
    rw [←hm]
    exact mem_map_of_mem a.toMonoidHom hx

omit [Finite D] in
private theorem fixed_axis (a : MulAut (Model D))
    (hf : ∀ i j,(family D i j).map a.toMonoidHom = family D i j)
    (b : Bool) (u : D8) (hu : u^2=1) :
    QuotientGroup.mk' (center (Model D)) (a (axisMap D b u)) =
      QuotientGroup.mk' (center (Model D)) (axisMap D b u) := by
  have hc : ∀ (b : Bool) (u : D8) (v : D8 × D8), u^2=1 →
      (∀ i j, ((axisPair b u).1∈plane i ∧ (axisPair b u).2∈plane j) →
        (v.1∈plane i ∧ v.2∈plane j)) →
      (((axisPair b u).1∈axisCenter ∧ (axisPair b u).2∈axisCenter) ↔
        (v.1∈axisCenter ∧ v.2∈axisCenter)) →
      (((axisPair b u)⁻¹*v).1∈axisCenter ∧ ((axisPair b u)⁻¹*v).2∈axisCenter) := by
    decide +kernel
  have hmem : ∀ i j, axisMap D b u ∈ family D i j → a (axisMap D b u) ∈ family D i j := by
    intro i j hu
    rw [←hf i j]
    exact mem_map_of_mem a.toMonoidHom hu
  have hi := hc b u (a (axisMap D b u)).1 hu (by
    intro i j hp
    exact (hmem i j ⟨hp,mem_top _⟩).1) (by
    have hh := (center_iff D a (axisMap D b u)).symm
    simpa only [center_eq,intersection,mem_prod,mem_top,and_true,axisMap,
      MonoidHom.comp_apply,MonoidHom.inl_apply] using hh)
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  rw [center_eq]
  exact ⟨hi,mem_top _⟩

omit [Finite D] in
private theorem family_fixed_quotient (a : MulAut (Model D))
    (hf : ∀ i j,(family D i j).map a.toMonoidHom = family D i j) :
    quotientAut (center (Model D)) a = 1 := by
  let π := QuotientGroup.mk' (center (Model D))
  have hfactor (b : Bool) (x : D8) : π (a (axisMap D b x)) = π (axisMap D b x) := by
    have hh : ∀ x : D8,∃ u ∈ plane true,∃ v ∈ plane false,u*v=x := by decide +kernel
    obtain ⟨u,hu,v,hv,rfl⟩ := hh x
    simp only [map_mul]
    rw [fixed_axis D a hf b u (elemPow_eq_one_of_isElementaryAbelian u hu),
      fixed_axis D a hf b v (elemPow_eq_one_of_isElementaryAbelian v hv)]
  have hcentral (x : D) : π (a ((1,1),x)) = π ((1,1),x) := by
    have hx : (((1,1),x) : Model D) ∈ center (Model D) := by
      rw [center_eq];exact ⟨⟨one_mem _,one_mem _⟩,mem_top _⟩
    have ha := (center_iff D a _).mpr hx
    rw [show π (a ((1,1),x)) = 1 from (QuotientGroup.eq_one_iff _).mpr ha,
      show π ((1,1),x) = 1 from (QuotientGroup.eq_one_iff _).mpr hx]
  apply MulEquiv.ext
  intro q
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center (Model D)) q
  rw [quotientAut_apply_mk]
  change π (a x) = π x
  have hx : x = axisMap D true x.1.1 * axisMap D false x.1.2 * ((1,1),x.2) := by
    ext <;> simp [axisMap,axisPair]
  rw [hx]
  simp only [map_mul,hfactor,hcentral]

private theorem model_quotientAut_pow_four (a : MulAut (Model D)) :
    quotientAut (center (Model D)) a ^ 4 = 1 := by
  rw [←map_pow]
  apply family_fixed_quotient D
  intro i j
  have he := familyAction_spec D (a^4) (i,j)
  rw [map_pow,familyAction_pow_four] at he
  exact he
end DihedralSquareAutomorphisms

namespace DihedralSquareAutomorphisms
open Subgroup
variable {P E : Type*} [Group P] [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- The full characteristic-center quotient action has exponent dividing four. -/
theorem quotientAut_pow_four (e : P ≃* E × (DihedralGroup 4 × DihedralGroup 4))
    (a : MulAut P) : quotientAut (center P) a ^ 4 = 1 := by
  let f : P ≃* Model E := e.trans MulEquiv.prodComm
  let b := MulAut.congr f a
  have hb := model_quotientAut_pow_four E b
  rw [←map_pow] at hb ⊢
  apply MulEquiv.ext
  intro q
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) q
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' (center P) ((a^4) x) = QuotientGroup.mk' (center P) x
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  have hx := DFunLike.congr_fun hb (QuotientGroup.mk' (center (Model E)) (f x))
  rw [quotientAut_apply_mk] at hx
  change QuotientGroup.mk' (center (Model E)) ((b^4) (f x)) =
    QuotientGroup.mk' (center (Model E)) (f x) at hx
  have he : b^4 = MulAut.congr f (a^4) := (map_pow (MulAut.congr f) a 4).symm
  rw [he,MulAut.congr_apply] at hx
  simp only [MulEquiv.trans_apply,f.symm_apply_apply] at hx
  have hc : f (x⁻¹ * (a^4) x) ∈ center (Model E) := by
    simpa only [map_mul,map_inv] using QuotientGroup.eq.mp hx.symm
  apply mem_center_iff.mpr
  intro y
  apply f.injective
  simpa only [map_mul] using mem_center_iff.mp hc (f y)

/-- An odd-order automorphism acts trivially on the literal center quotient. -/
theorem quotientAut_eq_one_of_odd
    (e : P ≃* E × (DihedralGroup 4 × DihedralGroup 4))
    (a : MulAut P) (ha : Odd (orderOf a)) : quotientAut (center P) a = 1 := by
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr ha).pow_left 2)
    (orderOf_dvd_of_pow_eq_one (quotientAut_pow_four e a))
    (orderOf_map_dvd (quotientAut (center P)) a)

/-- The automorphism image on the center quotient is a two-group. -/
theorem quotientAut_range_isPGroup
    (e : P ≃* E × (DihedralGroup 4 × DihedralGroup 4)) :
    IsPGroup 2 (quotientAut (center P)).range := by
  intro a
  refine ⟨2,?_⟩
  apply Subtype.ext
  obtain ⟨b,hb⟩ := a.property
  change (a : MulAut (P ⧸ center P)) ^ 4 = 1
  rw [←hb]
  exact quotientAut_pow_four e b

/-- Every actual actor has its two-residual in the center-quotient action kernel. -/
theorem pResidual_le_quotientAction_ker {H : Type*} [Group H]
    (e : P ≃* E × (DihedralGroup 4 × DihedralGroup 4)) (φ : H →* MulAut P) :
    pResidual 2 H ≤ ((quotientAut (center P)).comp φ).ker := by
  have he := pResidual_le_ker_of_isPGroup 2
    ((quotientAut (center P)).rangeRestrict.comp φ) (quotientAut_range_isPGroup e)
  intro h hh
  exact congrArg Subtype.val (he hh)

/-- The two-residual fixes every subgroup above the center. -/
theorem pResidual_preserves_subgroup [Finite P] {H : Type*} [Group H]
    (e : P ≃* E × (DihedralGroup 4 × DihedralGroup 4)) (φ : H →* MulAut P)
    (Q : Subgroup P) (hZ : center P ≤ Q) (h : H) (hh : h ∈ pResidual 2 H) :
    Q.map (φ h).toMonoidHom = Q := by
  have hk := pResidual_le_quotientAction_ker e φ hh
  change quotientAut (center P) (φ h) = 1 at hk
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (φ h).injective])
  rintro _ ⟨q,hq,rfl⟩
  have hx := DFunLike.congr_fun hk (QuotientGroup.mk' (center P) q)
  rw [quotientAut_apply_mk] at hx
  have hd := hZ (QuotientGroup.eq.mp hx.symm)
  have hm := Q.mul_mem hq hd
  change (φ h) q ∈ Q
  simpa only [mul_inv_cancel_left] using hm
end DihedralSquareAutomorphisms

namespace Subgroup
variable {G E : Type*} [Group G] [Finite G] [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- The literal normalizer action preserves each subgroup above the embedded center. -/
theorem pResidual_normalizer_le_normalizer_of_dihedral_square
    (S Q : Subgroup G) (e : S ≃* E × (DihedralGroup 4 × DihedralGroup 4))
    (hQS : Q ≤ S) (hZ : (center S).map S.subtype ≤ Q) :
    (pResidual 2 (normalizer (S : Set G))).map (normalizer (S : Set G)).subtype ≤
      normalizer (Q : Set G) := by
  rintro _ ⟨n,hn,rfl⟩
  have hh := DihedralSquareAutomorphisms.pResidual_preserves_subgroup e S.normalizerMonoidHom
    (Q.subgroupOf S) (fun z hz => hZ (mem_map_of_mem S.subtype hz)) n hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj (n : G)).injective])
  rintro _ ⟨q,hq,rfl⟩
  have hqn : S.normalizerMonoidHom n (⟨q,hQS hq⟩ : S) ∈ Q.subgroupOf S := by
    rw [←hh]
    exact mem_map_of_mem _ hq
  exact hqn
end Subgroup
