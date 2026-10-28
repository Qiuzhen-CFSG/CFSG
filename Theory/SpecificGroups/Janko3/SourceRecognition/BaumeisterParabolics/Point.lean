module
public import Theory.SpecificGroups.Janko3.SourceRecognition.SingerField
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Core
public import Mathlib.GroupTheory.NoncommCoprod
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# The marked point group in Baumeister's parabolic construction

The Singer normalizer in GL₂(4) is identified with C₃ × D₁₀ by its
commuting scalar-cubic and dihedral factors. Its affine extension has
self-centralizing two-core and a self-normalizing complement. The latter
identity gives L₁ ∩ N_G(L₁₂) = L₁₂ after any faithful embedding in G.
The complement's center is the selected cubic, so its ambient normalizer
lies in the normalizer of that same cubic, as needed for Lemma 2.5.

Small field certificates check the two generators of the quadratic
extension; all subgroup and ambient transport arguments are structural.
This is the point-side construction on Baumeister, *A geometry for groups
of J₃-type* (2007), pp.495–496. Identification of the full second parabolic
and the extraspecial alignment for Lemma 2.6 remain separate obligations.
-/

@[expose] public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open Subgroup
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer frobenius


abbrev F := Representation.SL2FourNatural.F

def alpha : Kˣ := Units.mk0 (⟨0,1⟩ : K) (by decide +kernel)

private theorem linear_ext_basis {a b : K ≃ₗ[F] K}
    (h1 : a 1 = b 1) (ht : a (⟨0,1⟩ : K) = b ⟨0,1⟩) : a=b := by
  apply LinearEquiv.ext
  intro x
  have hx : x = x.re • (1 : K) + x.im • (⟨0,1⟩ : K) := by
    revert x; decide +kernel
  rw [hx, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, ht]

def cubicUnits : Multiplicative (ZMod 3) →* Kˣ where
  toFun i := alpha ^ (5 * i.toAdd.val)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def dihedralWord : DihedralGroup 5 → K ≃ₗ[F] K
  | .r i => multiplication (alpha ^ (3*i.val))
  | .sr i => SingerField.frobenius * multiplication (alpha ^ (3*i.val))

private theorem dihedral_mul_one : ∀ x y : DihedralGroup 5,
    dihedralWord (x*y) 1 = dihedralWord x (dihedralWord y 1) := by decide +kernel
private theorem dihedral_mul_alpha : ∀ x y : DihedralGroup 5,
    dihedralWord (x*y) (⟨0,1⟩ : K) =
      dihedralWord x (dihedralWord y (⟨0,1⟩ : K)) := by decide +kernel

def dihedralHom : DihedralGroup 5 →* K ≃ₗ[F] K where
  toFun := dihedralWord
  map_one' := by exact linear_ext_basis (by decide +kernel) (by decide +kernel)
  map_mul' x y := by exact linear_ext_basis (dihedral_mul_one x y) (dihedral_mul_alpha x y)

private theorem factors_commute (x : Multiplicative (ZMod 3)) (y : DihedralGroup 5) :
    Commute (multiplication (cubicUnits x)) (dihedralHom y) := by
  apply linear_ext_basis
  · revert x y; decide +kernel
  · revert x y; decide +kernel

def complementHom : Seventeen.Complement →* K ≃ₗ[F] K :=
  (multiplication.comp cubicUnits).noncommCoprod dihedralHom (by exact factors_commute)

private theorem kernel_test : ∀ x : Seventeen.Complement,
    complementHom x 1 = 1 → complementHom x (⟨0,1⟩ : K) = ⟨0,1⟩ → x=1 := by
  decide +kernel

theorem complementHom_injective : Function.Injective complementHom := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  exact kernel_test x (LinearEquiv.congr_fun hx 1) (LinearEquiv.congr_fun hx ⟨0,1⟩)

theorem complementHom_mem (x : Seventeen.Complement) :
    complementHom x ∈ SingerField.normalizer := by
  have hm (u : Kˣ) : multiplication u ∈ SingerField.normalizer :=
    (show torus ≤ SingerField.normalizer from le_sup_left) ⟨u,rfl⟩
  have hf : SingerField.frobenius ∈ SingerField.normalizer :=
    (show zpowers SingerField.frobenius ≤ SingerField.normalizer from le_sup_right)
      (mem_zpowers _)
  change multiplication (cubicUnits x.1) * dihedralWord x.2 ∈ _
  apply mul_mem (hm _)
  cases x.2 with
  | r i => exact hm _
  | sr i => exact mul_mem hf (hm _)

def complementEquiv : Seventeen.Complement ≃* SingerField.normalizer := by
  let j := complementHom.codRestrict SingerField.normalizer complementHom_mem
  have hi : Function.Injective j := fun x y h => complementHom_injective
    (congrArg Subtype.val h)
  have hc : Nat.card Seventeen.Complement = Nat.card SingerField.normalizer := by
    rw [normalizer_card]
    norm_num [Seventeen.Complement, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, DihedralGroup.card]
  let : Finite SingerField.normalizer := Nat.finite_of_card_ne_zero (by rw [normalizer_card]; decide)
  exact MulEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr ⟨hi,hc⟩)




def pointComplement : Subgroup Model :=
  (SemidirectProduct.inr : SingerField.normalizer →* Model).range

theorem mem_pointComplement (x : Model) : x ∈ pointComplement ↔ x.left = 1 := by
  constructor
  · rintro ⟨y,rfl⟩; rfl
  · intro hx
    exact ⟨x.right, SemidirectProduct.ext hx.symm rfl⟩

def pointComplementEquiv : pointComplement ≃* Seventeen.Complement :=
  (MonoidHom.ofInjective SemidirectProduct.inr_injective).symm.trans complementEquiv.symm

theorem pointComplement_self_normalizing :
    Subgroup.normalizer (pointComplement : Set Model) = pointComplement := by
  apply le_antisymm ?_ pointComplement.le_normalizer
  intro x hx
  apply (mem_pointComplement x).mpr
  let r : SingerField.normalizer := ⟨multiplication alpha,
    (show torus ≤ SingerField.normalizer from le_sup_left) ⟨alpha,rfl⟩⟩
  let y : Model := SemidirectProduct.inr r
  have hy : y ∈ pointComplement := ⟨r,rfl⟩
  have hk : x⁻¹ * y * x ∈ pointComplement := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((Subgroup.normalizer (pointComplement : Set Model)).inv_mem hx) y).mp hy
  have he : y * x = x * (x⁻¹ * y * x) := by group
  have heL := congrArg SemidirectProduct.left he
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left,
    (mem_pointComplement _).mp hk, map_one, mul_one] at heL
  have hf : (alpha : K) * x.left.toAdd = x.left.toAdd := by
    have hh : action r x.left = x.left := by
      simpa only [y,SemidirectProduct.left_inr,SemidirectProduct.right_inr,one_mul] using heL
    exact congrArg Multiplicative.toAdd hh
  have ha : (alpha : K) ≠ 1 := by decide +kernel
  have hz : x.left.toAdd = 0 := by
    have hh : ((alpha : K) - 1) * x.left.toAdd = 0 := by rw [sub_mul,one_mul,hf,sub_self]
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ha)
  exact congrArg Multiplicative.ofAdd hz

theorem root_centralizer : centralizer (root.range : Set Model) = root.range := by
  have hr (x : Model) : x ∈ root.range ↔ x.right = 1 := by
    constructor
    · rintro ⟨y,rfl⟩; rfl
    · intro hx; exact ⟨x.left, SemidirectProduct.ext rfl hx.symm⟩
  apply le_antisymm
  · intro x hx
    apply (hr x).mpr
    apply Subtype.ext
    apply LinearEquiv.ext
    intro t
    have he := congrArg SemidirectProduct.left (hx (root (.ofAdd t)) ⟨.ofAdd t,rfl⟩)
    change Multiplicative.ofAdd t * x.left = x.left * action x.right (.ofAdd t) at he
    rw [mul_comm] at he
    exact (congrArg Multiplicative.toAdd (mul_left_cancel he)).symm
  · intro x hx y hy
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    rw [← map_mul,← map_mul,mul_comm]


private theorem root_card : Nat.card root.range = 16 := by
  change Nat.card ((SemidirectProduct.inl : Multiplicative K →* Model).range) = 16
  rw [← Nat.card_congr (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := action))).toEquiv]
  exact (Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)).trans
    ((Nat.card_eq_fintype_card).trans field_card)

theorem point_core : pCore 2 Model = root.range := by
  let : Finite Model := Nat.finite_of_card_ne_zero (by rw [model_card]; decide)
  let : Finite SingerField.normalizer := Nat.finite_of_card_ne_zero (by rw [normalizer_card]; decide)
  let q : Model →* SingerField.normalizer := SemidirectProduct.rightHom
  have hk : q.ker = root.range := SemidirectProduct.range_inl_eq_ker_rightHom.symm
  have hp : IsPGroup 2 q.ker := IsPGroup.of_card (n := 4) (by rw [hk,root_card]; norm_num)
  have hC : pCore 2 SingerField.normalizer = ⊥ := by
    rw [← pCore_map_iso 2 complementEquiv,Seventeen.complement_twoCore,Subgroup.map_bot]
  rw [← q.comap_pCore_of_ker_isPGroup SemidirectProduct.rightHom_surjective hp,hC]
  exact hk

theorem point_core_centralizer : centralizer (pCore 2 Model : Set Model) = pCore 2 Model := by
  rw [point_core,root_centralizer]

def binaryCoordinates : Multiplicative K ≃* Seventeen.Plane := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [Nat.card_zmod,Nat.card_eq_fintype_card,field_card] at hc
  have hd : Module.finrank (ZMod 2) K = 4 :=
    (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc.symm
  let e : K ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hd])
  exact e.toAddEquiv.toMultiplicative

def pointAction : Seventeen.Complement →* MulAut Seventeen.Plane :=
  (MulAut.congr binaryCoordinates).toMonoidHom.comp (action.comp complementEquiv.toMonoidHom)

def pointEquiv : Model ≃* Seventeen.Plane ⋊[pointAction] Seventeen.Complement :=
  SemidirectProduct.congr' binaryCoordinates complementEquiv.symm

variable {G : Type*} [Group G]

def overlap (j : Model →* G) : Subgroup G := pointComplement.map j

theorem overlap_le (j : Model →* G) : overlap j ≤ j.range := map_le_range j pointComplement

def overlapEquiv (j : Model →* G) (hj : Function.Injective j) : overlap j ≃* Seventeen.Complement :=
  (pointComplement.equivMapOfInjective j hj).symm.trans pointComplementEquiv

theorem point_intersection_normalizer (j : Model →* G) (hj : Function.Injective j) :
    j.range ⊓ Subgroup.normalizer (overlap j : Set G) = overlap j := by
  apply le_antisymm
  · rintro _ ⟨⟨x,rfl⟩,hx⟩
    have hn : x ∈ (Subgroup.normalizer (overlap j : Set G)).comap j := hx
    rw [comap_normalizer_eq_of_le_range (overlap_le j)] at hn
    have he : (overlap j).comap j = pointComplement := by
      rw [overlap,comap_map_eq,j.ker_eq_bot hj,sup_bot_eq]
    rw [he,pointComplement_self_normalizing] at hn
    exact mem_map_of_mem j hn
  · exact le_inf (overlap_le j) (overlap j).le_normalizer

private theorem center_complement :
    center Seventeen.Complement = zpowers ((Multiplicative.ofAdd (1 : ZMod 3),1) : Seventeen.Complement) := by
  have h3 : orderOf ((Multiplicative.ofAdd (1 : ZMod 3),1) : Seventeen.Complement) = 3 := by
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  ext x
  rw [mem_center_iff,mem_zpowers_iff_mem_range_orderOf,h3]
  revert x
  decide +kernel

def cubic : Model :=
  pointComplementEquiv.symm ((Multiplicative.ofAdd (1 : ZMod 3),1) : Seventeen.Complement)

theorem cubic_order : orderOf cubic = 3 := by
  rw [cubic,orderOf_coe,pointComplementEquiv.symm.orderOf_eq]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem cubic_mem : cubic ∈ pointComplement := (pointComplementEquiv.symm _).property

theorem image_involution_mem (j : Model →* G) : j fieldElement ∈ overlap j :=
  mem_map_of_mem j ((mem_pointComplement _).mpr rfl)

theorem image_involution_order (j : Model →* G) (hj : Function.Injective j) :
    orderOf (j fieldElement) = 2 := (orderOf_injective j hj _).trans fieldElement_order

theorem image_core_centralizer (j : Model →* G) (hj : Function.Injective j) :
    centralizer (pCore 2 j.range : Set j.range) = pCore 2 j.range := by
  let e := (MonoidHom.ofInjective hj).symm
  have he (x : j.range) : e x ∈ pCore 2 Model ↔ x ∈ pCore 2 j.range := by
    rw [←pCore_map_iso 2 e,mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply]
  ext x
  constructor
  · intro hx
    apply (he x).mp
    rw [←point_core_centralizer]
    intro y hy
    obtain ⟨y,rfl⟩ := e.surjective y
    rw [←map_mul,←map_mul]
    exact congrArg e (hx y ((he y).mp hy))
  · intro hx y hy
    have hx' : e x ∈ centralizer (pCore 2 Model : Set Model) :=
      point_core_centralizer.symm ▸ (he x).mpr hx
    apply e.injective
    rw [map_mul,map_mul]
    exact hx' (e y) ((he y).mpr hy)

theorem cubic_center : (center pointComplement).map pointComplement.subtype = zpowers cubic := by
  have hz : center pointComplement = (center Seventeen.Complement).map
      pointComplementEquiv.symm.toMonoidHom := by
    ext x
    rw [mem_map_equiv]
    constructor
    · intro hx
      exact (centerCongr pointComplementEquiv ⟨x,hx⟩).property
    · intro hx
      have hh := (centerCongr pointComplementEquiv.symm ⟨pointComplementEquiv x,hx⟩).property
      change pointComplementEquiv.symm (pointComplementEquiv x) ∈ center pointComplement at hh
      rwa [pointComplementEquiv.symm_apply_apply] at hh
  rw [hz,center_complement,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
  rfl

theorem overlap_normalizer_le_cubic (j : Model →* G) (hj : Function.Injective j) :
    Subgroup.normalizer (overlap j : Set G) ≤ Subgroup.normalizer (zpowers (j cubic) : Set G) := by
  have hn := normalizer_le_normalizer_characteristic_map j hj pointComplement
    (center pointComplement)
  rw [cubic_center,MonoidHom.map_zpowers] at hn
  exact hn

theorem cubic_commutes_complement (x : pointComplement) : Commute cubic (x : Model) := by
  have hz : cubic ∈ (center pointComplement).map pointComplement.subtype := by
    rw [cubic_center]
    exact mem_zpowers _
  obtain ⟨c,hc,hcv⟩ := hz
  exact hcv ▸ (congrArg Subtype.val (mem_center_iff.mp hc x)).symm

end Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
