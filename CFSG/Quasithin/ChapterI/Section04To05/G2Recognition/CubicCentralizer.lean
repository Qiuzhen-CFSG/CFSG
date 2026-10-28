module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicLocal
public import Theory.GroupTheory.QuaternionSylowOddCentralizer
public import Theory.GroupTheory.QuaternionSylowOddDecomposition
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.SpecificGroups.SL2.ThreeCharacteristicTwo
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupTheory.OddFixedKernelInvolution

/-!
# The ambient cubic centralizer and its odd core

For an element x of order three in H₁, the quaternion core of H₂ is
Sylow in C_G(x): its characteristic central involution promotes the
order-eight subgroup from the order72 intersection with H. Brauer–Suzuki
and coprime lifting then give C_G(x)=O(C_G(x))H₂, with trivial intersection
of the two factors. The marked involution fixes exactly ⟨x⟩ in the odd
core. Consequently it inverts the quotient by ⟨x⟩, and that quotient is
abelian. Every subgroup and quotient uses its actual ambient embedding.

These are §3B(i), the centralizer assertion of §3B(ii), and §3B(iii) of
Fong–Wong, Nagoya Math. J.36 (1969), p.156, specialized to the genuine
Aschbacher–Smith I.4.5 configuration, p.417. The normalizer formula and
the remaining prime-three multiplicity and ambient recognition are not
claimed here. `Chapter14CubicCentralizer` applies this family to the actual
source-local data. Recognition remains with `qt-i45-g2-recognition`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal

def cubicCentralizer (x : c.H₁) : Subgroup G := centralizer ({((x:c.H):G)} : Set G)
def cubicOddCore (x : c.H₁) : Subgroup G :=
  (pPrimeCore 2 (cubicCentralizer c x)).map (cubicCentralizer c x).subtype

theorem cubic_centralizer_intersection (x : c.H₁) (hx : orderOf x = 3) :
    c.H ⊓ cubicCentralizer c x =
      (c.H₂.map c.H.subtype) ⊔ zpowers ((x:c.H):G) := by
  unfold cubicCentralizer
  rw [← map_subtype_centralizer_singleton c.H (x:c.H),
    left_cubic_local_centralizer c x hx,Subgroup.map_sup,MonoidHom.map_zpowers]
  rfl

theorem cubic_quaternion_sylow (x : c.H₁) (hx : orderOf x = 3) :
    ∃ P : Sylow 2 (cubicCentralizer c x),
      (P : Subgroup (cubicCentralizer c x)).map (cubicCentralizer c x).subtype =
        (c.H₂.pCoreIn 2).map c.H.subtype ∧ Nonempty (P ≃* QuaternionGroup 2) := by
  let C := cubicCentralizer c x
  let Q := (c.H₂.pCoreIn 2).map c.H.subtype
  have hQC : Q ≤ C := by
    rintro q ⟨a,ha,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (c.commute x x.property a (c.H₂.pCoreIn_le 2 ha)).symm)
  let R := Q.subgroupOf C
  let e : R ≃* QuaternionGroup 2 := (subgroupOfEquivOfLe hQC).trans
    (((c.H₂.pCoreIn 2).equivMapOfInjective c.H.subtype c.H.subtype_injective).symm.trans
      (factorCoreEquiv c c.H₂ c.H₂_model.some))
  have hR : Nat.card R = 8 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  obtain ⟨z,hz,hline,hH⟩ := exists_marked_involution c
  have hzI : z ∈ c.H₁ ⊓ c.H₂ := hline ▸ mem_zpowers z
  have hzQ : (z:G) ∈ Q := mem_map_of_mem c.H.subtype
    ((factor_core_intersection c).symm ▸ hzI).2
  let zz : C := ⟨z,hQC hzQ⟩
  have hz2 : orderOf zz = 2 := (orderOf_coe zz).symm.trans ((orderOf_coe z).trans hz)
  have hRC : R ≤ centralizer ({zz} : Set C) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hHmem : (a:G) ∈ c.H := (map_subtype_le _ : Q ≤ c.H) ha
    exact mem_centralizer_singleton_iff.mp (hH ▸ hHmem)
  have hcentral : Nat.card (centralizer ({zz} : Set C)) = 72 := by
    rw [← card_map_of_injective C.subtype_injective,map_subtype_centralizer_singleton]
    change Nat.card (C ⊓ centralizer ({(z:G)} : Set G) : Subgroup G) = 72
    rw [←hH,inf_comm]
    change Nat.card (c.H ⊓ centralizer ({((x:c.H):G)} : Set G) : Subgroup G) = 72
    rw [← map_subtype_centralizer_singleton c.H (x:c.H),
      card_map_of_injective c.H.subtype_injective]
    exact left_cubic_local_centralizer_card c x hx
  have hi : R.relIndex (centralizer ({zz} : Set C)) = 9 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup C) R
      (centralizer ({zz} : Set C)) bot_le hRC
    rw [relIndex_bot_left,relIndex_bot_left,hR,hcentral] at hh
    omega
  obtain ⟨P,hP⟩ := exists_sylow_of_quaternion_odd_centralizer_index zz hz2 R hRC
    hzQ ⟨e⟩ (by rw [hi]; decide)
  refine ⟨P,?_,?_⟩
  · rw [hP,map_subgroupOf_eq_of_le hQC]
  · exact ⟨(MulEquiv.subgroupCongr hP).trans e⟩

omit [Finite G] in
theorem cubic_line_le_oddCore (x : c.H₁) (hx : orderOf x = 3) :
    zpowers ((x:c.H):G) ≤ cubicOddCore c x := by
  let C := cubicCentralizer c x
  let w : C := ⟨x,mem_centralizer_singleton_iff.mpr rfl⟩
  have hwZ : w ∈ center C := mem_center_iff.mpr (fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp y.property))
  have hZ : zpowers w ≤ center C := zpowers_le.mpr hwZ
  let : (zpowers w).Normal := ⟨fun a ha g => by
    rw [mem_center_iff.mp (hZ ha) g,mul_inv_cancel_right]
    exact ha⟩
  have hw3 : orderOf w = 3 := (orderOf_coe w).symm.trans
    ((orderOf_coe (x:c.H)).trans ((orderOf_coe x).trans hx))
  have hle : zpowers w ≤ pPrimeCore 2 C := le_sSup ⟨inferInstance,by
    rw [Nat.card_zpowers,hw3]; decide⟩
  have hh := map_mono (f := C.subtype) hle
  rwa [MonoidHom.map_zpowers] at hh

theorem cubic_centralizer_split (x : c.H₁) (hx : orderOf x = 3) :
    cubicCentralizer c x = cubicOddCore c x ⊔ c.H₂.map c.H.subtype := by
  let C := cubicCentralizer c x
  obtain ⟨z,hz,_,hH⟩ := exists_marked_involution c
  have hzC : (z:G) ∈ C := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hH ▸ x.val.property)).symm
  let zz : C := ⟨z,hzC⟩
  have hz2 : orderOf zz = 2 := (orderOf_coe zz).symm.trans ((orderOf_coe z).trans hz)
  obtain ⟨P,_,hP⟩ := cubic_quaternion_sylow c x hx
  have hsplit := oddCore_sup_centralizer_of_quaternion_sylow P (n := 3) (by decide) hP zz hz2
  have hh := congrArg (fun K : Subgroup C => K.map C.subtype) hsplit
  rw [Subgroup.map_sup,map_subtype_centralizer_singleton,←MonoidHom.range_eq_map,C.range_subtype] at hh
  change cubicOddCore c x ⊔ (C ⊓ centralizer ({(z:G)} : Set G)) = C at hh
  rw [←hH,inf_comm,cubic_centralizer_intersection c x hx] at hh
  rw [←sup_assoc,sup_eq_left.mpr ((cubic_line_le_oddCore c x hx).trans le_sup_left)] at hh
  exact hh.symm
omit [Finite G] in
theorem opposite_factor_le_cubic_centralizer (x : c.H₁) :
    c.H₂.map c.H.subtype ≤ cubicCentralizer c x := by
  rintro a ⟨h,hh,rfl⟩
  exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
    (c.commute x x.property h hh).symm)

theorem cubic_oddCore_inf_factor (x : c.H₁) :
    cubicOddCore c x ⊓ c.H₂.map c.H.subtype = ⊥ := by
  let C := cubicCentralizer c x
  let L := c.H₂.map c.H.subtype
  have hLC : L ≤ C := opposite_factor_le_cubic_centralizer c x
  let e : L.subgroupOf C ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    (subgroupOfEquivOfLe hLC).trans
      ((c.H₂.equivMapOfInjective c.H.subtype c.H.subtype_injective).symm.trans c.H₂_model.some)
  have hL : pPrimeCore 2 (L.subgroupOf C) = ⊥ := pPrimeCore_eq_bot_of_equiv e
    (pPrimeCore_eq_bot_of_centralizer_pCore_le 2
      Matrix.SpecialLinearGroup.three_twoCore_self_centralizing)
  have hi := normal_coprime_inf_eq_bot (pPrimeCore 2 C) (L.subgroupOf C)
    pPrimeCore_coprime_card hL
  have hm := congrArg (fun A : Subgroup C => A.map C.subtype) hi
  rwa [Subgroup.map_inf _ _ _ C.subtype_injective,map_subgroupOf_eq_of_le hLC,Subgroup.map_bot] at hm

theorem cubic_oddCore_fixed (x : c.H₁) (hx : orderOf x = 3) :
    cubicOddCore c x ⊓ c.H = zpowers ((x:c.H):G) := by
  let D := cubicOddCore c x
  let L := c.H₂.map c.H.subtype
  let W := zpowers ((x:c.H):G)
  have hWD : W ≤ D := cubic_line_le_oddCore c x hx
  have hWH : W ≤ c.H := zpowers_le.mpr x.val.property
  have hLW : L ≤ normalizer (W : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    change L ≤ centralizer (zpowers ((x:c.H):G) : Set G)
    rw [zpowers_eq_closure,centralizer_closure]
    exact opposite_factor_le_cubic_centralizer c x
  apply le_antisymm ?_ (le_inf hWD hWH)
  intro a ha
  have hlocal : a ∈ L ⊔ W := (cubic_centralizer_intersection c x hx).le
    ⟨ha.2,(map_subtype_le _ : D ≤ cubicCentralizer c x) ha.1⟩
  change a ∈ (↑(L ⊔ W) : Set G) at hlocal
  rw [coe_mul_of_left_le_normalizer_right L W hLW] at hlocal
  obtain ⟨l,hl,w,hw,he⟩ := hlocal
  have hlD : l ∈ D := by
    have hh := D.mul_mem ha.1 (D.inv_mem (hWD hw))
    rwa [←he,mul_inv_cancel_right] at hh
  have hl1 : l=1 := mem_bot.mp ((cubic_oddCore_inf_factor c x).le ⟨hlD,hl⟩)
  change w ∈ W at hw
  simpa only [←he,hl1,one_mul] using hw
theorem cubic_oddCore_inversion (x : c.H₁) (hx : orderOf x = 3)
    (z : G) (hz : orderOf z = 2) (hH : c.H = centralizer ({z} : Set G)) :
    (∀ d ∈ cubicOddCore c x, z*d*z⁻¹*d ∈ zpowers ((x:c.H):G)) ∧
      ⁅cubicOddCore c x,cubicOddCore c x⁆ ≤ zpowers ((x:c.H):G) := by
  let C := cubicCentralizer c x
  let D := cubicOddCore c x
  let W := zpowers ((x:c.H):G)
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hH ▸ x.val.property)).symm
  have hzD : z ∈ normalizer (D : Set G) :=
    (normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C)) (C.le_normalizer hzC)
  let a := D.normalizerMonoidHom ⟨z,hzD⟩
  let R := W.subgroupOf D
  have hWD : W ≤ D := cubic_line_le_oddCore c x hx
  have hWH : W ≤ c.H := zpowers_le.mpr x.val.property
  have hDC : D ≤ centralizer (W : Set G) := by
    change D ≤ centralizer (zpowers ((x:c.H):G) : Set G)
    rw [zpowers_eq_closure,centralizer_closure]
    exact map_subtype_le (pPrimeCore 2 C)
  have hRZ : R ≤ center D := by
    intro w hw
    exact mem_center_iff.mpr (fun d => Subtype.ext ((hDC d.property) w hw).symm)
  let : R.Normal := ⟨fun w hw d => by
    rw [mem_center_iff.mp (hRZ hw) d,mul_inv_cancel_right]
    exact hw⟩
  have ha : Function.Involutive a := by
    intro d
    apply Subtype.ext
    change z*(z*(d:G)*z⁻¹)*z⁻¹=(d:G)
    have hz2 : z*z=1 := by simpa only [pow_two,hz] using pow_orderOf_eq_one z
    have hzi : z⁻¹=z := inv_eq_of_mul_eq_one_left hz2
    rw [hzi]
    calc
      _ = (z*z)*(d:G)*(z*z) := by group
      _ = d := by rw [hz2,one_mul,mul_one]
  have hf (d : D) : a d=d ↔ d ∈ R := by
    constructor
    · intro hd
      have hh : z*(d:G)*z⁻¹=(d:G) := congrArg Subtype.val hd
      apply (cubic_oddCore_fixed c x hx).le
      refine ⟨d.property,?_⟩
      rw [hH]
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hd
      apply Subtype.ext
      change z*(d:G)*z⁻¹=(d:G)
      have hh : (d:G)*z=z*(d:G) := mem_centralizer_singleton_iff.mp (hH ▸ hWH hd)
      rw [←hh,mul_inv_cancel_right]
  have ho : Odd (Nat.card R) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWD).toEquiv,Nat.card_zpowers,
      orderOf_coe,orderOf_coe,hx]
    decide
  obtain ⟨hi,hcomm⟩ := a.quotient_inversion_of_odd_fixed_kernel ha R ho hf
  refine ⟨fun d hd => hi ⟨d,hd⟩,?_⟩
  have hm := map_mono (f := D.subtype) hcomm
  rw [map_commutator_eq,map_subgroupOf_eq_of_le hWD] at hm
  simpa only [D.range_subtype] using hm
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
