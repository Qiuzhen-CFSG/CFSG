module
public import Theory.GroupTheory.SemidihedralSixteenQuaternion
public import Theory.SpecificGroups.DihedralEightProduct
public import Mathlib.GroupTheory.Index
/-!
# The quaternion shadow centralizer obstruction

Let a homomorphism onto a semidihedral sixteen have quaternion kernel C.
A disjoint quaternion D and dihedral eight U centralizing C have distinct
index-two images, so C_S(C) maps onto the quotient. Its kernel is Z(C), giving
order 32. In contrast C_S(D) has kernel C and image in the order-at-most-two
centralizer of its quaternion image, hence order at most 16. An automorphism
sending C to D would preserve centralizer orders, a contradiction.

Source: Aschbacher--Smith, Lemma 2.5.21, terminal quaternion case, printed p.567.
-/
public section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace Theory.GroupTheory.QuaternionShadow
private abbrev SD := Semidihedral.StandardModel 4 (by decide)
variable {S : Type*} [Group S]

private theorem injective_on_disjoint (f : S →* SD) (C D : Subgroup S)
    (hker : f.ker = C) (hd : Disjoint C D) : Function.Injective (f.comp D.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  exact disjoint_def.mp hd (hker ▸ hx) x.property

private theorem quaternion_ne_dihedral : ¬ Nonempty (QuaternionGroup 2 ≃* DihedralGroup 4) := by
  rintro ⟨e⟩
  let f : QuaternionGroup 2 →* Multiplicative (ZMod 2) × DihedralGroup 4 :=
    (1 : QuaternionGroup 2 →* Multiplicative (ZMod 2)).prod e.toMonoidHom
  exact DihedralEightProduct.not_injective_quaternionEight f (fun x y h =>
    e.injective (congrArg Prod.snd h))

private theorem quaternion_dihedral_generate (D U : Subgroup SD)
    (eD : D ≃* QuaternionGroup 2) (eU : U ≃* DihedralGroup 4) : D ⊔ U = ⊤ := by
  have hD : Nat.card D = 8 := (Nat.card_congr eD.toEquiv).trans (by rw [Nat.card_eq_fintype_card]; decide)
  have hU : Nat.card U = 8 := (Nat.card_congr eU.toEquiv).trans (by rw [Nat.card_eq_fintype_card]; decide)
  have hn : D ≠ U := by
    intro h
    exact quaternion_ne_dihedral ⟨(eD.symm.trans (MulEquiv.subgroupCongr h)).trans eU⟩
  have hi : D.index = 2 := by
    have h := D.card_mul_index
    rw [hD, Semidihedral.standardModel_card] at h
    norm_num at h
    omega
  have hl : D < D ⊔ U := lt_of_le_of_ne le_sup_left (by
    intro he
    have hUD : U ≤ D := he ▸ le_sup_right
    exact hn (eq_of_le_of_card_ge hUD (by omega)).symm)
  have hh := index_strictAnti hl
  rw [hi] at hh
  have hp : 0 < (D ⊔ U).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := D ⊔ U))
  exact index_eq_one.mp (by omega)

private def kernelCentralizerEquiv (f : S →* SD) (C : Subgroup S) (hk : f.ker = C) :
    (f.comp (centralizer (C : Set S)).subtype).ker ≃* center C where
  toFun x := ⟨⟨x.val.val, hk ▸ x.property⟩, mem_center_iff.mpr (by
    intro c
    exact Subtype.ext (x.val.property c.val c.property))⟩
  invFun c := ⟨⟨c.val.val, by
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp c.property ⟨x, hx⟩)⟩,
    show c.val.val ∈ f.ker from hk.symm ▸ c.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The two centralizer orders forced by the quaternion and dihedral images. -/
theorem centralizer_orders (f : S →* Semidihedral.StandardModel 4 (by decide)) (C D U : Subgroup S)
    (hk : f.ker = C) (eC : C ≃* QuaternionGroup 2)
    (eD : D ≃* QuaternionGroup 2) (eU : U ≃* DihedralGroup 4)
    (hCD : Disjoint C D) (hCU : Disjoint C U)
    (hDC : D ≤ centralizer (C : Set S)) (hUC : U ≤ centralizer (C : Set S)) :
    Nat.card (centralizer (C : Set S)) = 32 ∧ Nat.card (centralizer (D : Set S)) ≤ 16 := by
  let fD := f.comp D.subtype
  let fU := f.comp U.subtype
  have hfD : Function.Injective fD := injective_on_disjoint f C D hk hCD
  have hfU : Function.Injective fU := injective_on_disjoint f C U hk hCU
  have hDmap : fD.range = D.map f := by exact MonoidHom.range_comp _ _ |>.trans (by rw [range_subtype])
  have hUmap : fU.range = U.map f := by exact MonoidHom.range_comp _ _ |>.trans (by rw [range_subtype])
  let d := (MulEquiv.subgroupCongr hDmap.symm).trans ((MonoidHom.ofInjective hfD).symm.trans eD)
  let u := (MulEquiv.subgroupCongr hUmap.symm).trans ((MonoidHom.ofInjective hfU).symm.trans eU)
  have hgen : D.map f ⊔ U.map f = ⊤ := quaternion_dihedral_generate _ _ d u
  let V := centralizer (C : Set S)
  let v := f.comp V.subtype
  have hvmap : v.range = V.map f := by exact MonoidHom.range_comp _ _ |>.trans (by rw [range_subtype])
  have hvrange : v.range = ⊤ := by
    rw [hvmap]
    apply top_unique
    rw [← hgen]
    exact sup_le (map_mono hDC) (map_mono hUC)
  have hvc : Nat.card V = 32 := by
    have h := v.ker.card_mul_index
    rw [index_ker, hvrange, card_top,
      Nat.card_congr (kernelCentralizerEquiv f C hk).toEquiv,
      Semidihedral.QuaternionLocal.center_card_of_equiv eC,
      Semidihedral.standardModel_card] at h
    norm_num at h
    omega
  refine ⟨hvc, ?_⟩
  let W := centralizer (D : Set S)
  let w := f.comp W.subtype
  have hCW : C ≤ W := (le_centralizer_iff).mp hDC
  have hwker : w.ker = C.subgroupOf W := by
    change f.ker.comap W.subtype = C.comap W.subtype
    rw [hk]
  have hwkc : Nat.card w.ker = 8 := by
    rw [hwker, Nat.card_congr (subgroupOfEquivOfLe hCW).toEquiv,
      Nat.card_congr eC.toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide
  have hwle : w.range ≤ centralizer (D.map f : Set SD) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, hy, rfl⟩
    change f y * f x.val = f x.val * f y
    rw [← map_mul, ← map_mul]
    exact congrArg f (x.property y hy)
  have hwr : Nat.card w.range ≤ 2 :=
    (Nat.card_le_card_of_injective (inclusion hwle) (inclusion_injective hwle)).trans
      (Semidihedral.QuaternionLocal.centralizer_card_le_two _ d)
  have hh := w.ker.card_mul_index
  rw [index_ker, hwkc] at hh
  change 8 * Nat.card w.range = Nat.card W at hh
  change Nat.card W ≤ 16
  omega

/-- A quaternion kernel with the source dihedral complement cannot have a
disjoint commuting automorphic copy in the same Sylow group. -/
theorem no_disjoint_commuting_copy
    (f : S →* Semidihedral.StandardModel 4 (by decide)) (C U : Subgroup S)
    (hk : f.ker = C) (eC : C ≃* QuaternionGroup 2) (eU : U ≃* DihedralGroup 4)
    (hCU : Disjoint C U) (hUC : U ≤ centralizer (C : Set S))
    (a : MulAut S) (hCD : Disjoint C (C.map a.toMonoidHom))
    (hDC : C.map a.toMonoidHom ≤ centralizer (C : Set S)) : False := by
  let D := C.map a.toMonoidHom
  let eD := (a.subgroupMap C).symm.trans eC
  obtain ⟨h32, h16⟩ := centralizer_orders f C D U hk eC eD eU hCD hCU hDC hUC
  have he : (centralizer (C : Set S)).map a.toMonoidHom = centralizer (D : Set S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      change a z * a y = a y * a z
      exact (a.map_mul z y).symm.trans ((congrArg a (hy z hz)).trans (a.map_mul y z))
    · intro hx
      refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
      intro z hz
      apply a.injective
      simpa only [map_mul, a.apply_symm_apply] using hx (a z) ⟨z, hz, rfl⟩
  have hc := congrArg (fun P : Subgroup S => Nat.card P) he
  rw [card_map_of_injective a.injective, h32] at hc
  omega

end Theory.GroupTheory.QuaternionShadow
