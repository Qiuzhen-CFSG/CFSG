module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicFusion
public import Theory.GroupTheory.PGroup.OrderTwentySeven
public import Theory.SpecificGroups.SL2.NormalMonolith

/-!
# Exponent and quotient geometry of the marked cubic odd cores

Each cubic odd core has exponent three. Brauer–Wielandt factors it into
three fixed subgroups of the actual common torus. These are three-subgroups
of involution centralizers, whose Sylow three-subgroups are elementary of
order nine. The previously proved central cubic commutator bound makes
cubing multiplicative, so the three fixed factors give the exponent bound.

The quotient by the original cubic line is elementary abelian. Conjugation
by the opposite original SL₂(3) factor descends to this literal quotient;
the marked central involution acts by inversion. Unless the core has order
three, this involution is detected, and the SL₂(3) normal-subgroup theorem
makes the quotient action faithful. If the core has order 27, it is either
elementary abelian or extraspecial of exponent three, with center exactly
the original cubic line in the latter case.

These are the odd-core and module calculations used in the exceptional
q=3 analysis of Aschbacher–Smith I.4.5, printed p.417. Compare Fong–Wong,
Nagoya Math. J.36 (1969), §3B(iii), p.156, and the first paragraph of the
proof of §4D, pp.164–165 (DOI 10.1017/S0027763000013180). The latter's
subsequent branch argument excludes q=3. No invariant-line selection from
torus invariance is used here. The Sylow-nine and order-27 exclusions and
the equivalence with Atlas.G2.Model remain unproved. The companion
`Chapter14OddCoreGeometry` applies the calculation to the source-local data.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

private theorem H_three_subgroup_cubes (P : Subgroup c.H) (hp : IsPGroup 3 P)
    (a : c.H) (ha : a ∈ P) : a^3=1 := by
  obtain ⟨t⟩ := exists_cubic_torus c
  let E := zpowers (t.x:c.H) ⊔ zpowers (t.y:c.H)
  have hm : E.map c.H.subtype = zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hc : Nat.card E = 9 := by
    rw [← card_map_of_injective c.H.subtype_injective, hm]
    exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  have hi : E.index = 64 := by
    have hh := E.card_mul_index
    rw [hc,H_card c] at hh
    omega
  let S : Sylow 3 c.H := (IsPGroup.of_card (p := 3) (n := 2) hc).toSylow
    (by rw [hi]; decide)
  obtain ⟨R,hR⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq c.H R S
  have hga : g*a*g⁻¹ ∈ E := by
    change g*a*g⁻¹ ∈ (S:Subgroup c.H)
    rw [←hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hR ha)
  let : IsElementaryAbelian 3 (zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G) :=
    (cubic_plane_data c t.x t.y t.x_order t.y_order).1
  have hpow : (g*a*g⁻¹)^3=1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian _ (hm ▸ mem_map_of_mem c.H.subtype hga))
  apply (MulAut.conj g).injective
  change ((MulAut.conj g) a)^3=1 at hpow
  simpa only [map_pow,map_one] using hpow

include c in
private theorem involution_fixed_three_cubes (P : Subgroup G) (hp : IsPGroup 3 P)
    (u : G) (hu : orderOf u=2) (a : G) (ha : a ∈ P ⊓ centralizer ({u}:Set G)) : a^3=1 := by
  obtain ⟨z,hz,_,hH⟩ := exists_marked_involution c
  obtain ⟨g,hg⟩ := isConj_iff.mp (involutions_conjugate c u z hu ((orderOf_coe z).trans hz))
  let F := P ⊓ centralizer ({u}:Set G)
  let A := F.map (MulAut.conj g).toMonoidHom
  have hAH : A ≤ c.H := by
    rintro b ⟨a,ha,rfl⟩
    rw [hH]
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp ha.2)
    have hg' : MulAut.conj g u = (z:G) := hg
    change MulAut.conj g a * (z:G) = (z:G) * MulAut.conj g a
    simpa only [map_mul,hg'] using he
  have hpA : IsPGroup 3 (A.subgroupOf c.H) :=
    ((hp.to_le (show F ≤ P from inf_le_left)).map (MulAut.conj g).toMonoidHom).of_equiv
      (subgroupOfEquivOfLe hAH).symm
  have hmem : MulAut.conj g a ∈ A := mem_map_of_mem _ ha
  have hpow := H_three_subgroup_cubes c (A.subgroupOf c.H) hpA ⟨_,hAH hmem⟩ hmem
  apply (MulAut.conj g).injective
  have hpowG := congrArg Subtype.val hpow
  change ((MulAut.conj g) a)^3=1 at hpowG
  simpa only [map_pow,map_one] using hpowG

omit [Finite G] in
private theorem cube_mul_of_central_cubic_commutator (x y : G)
    (hc : ∀ a : G, a * ⁅y,x⁆ = ⁅y,x⁆ * a) (h3 : ⁅y,x⁆^3=1) :
    (x*y)^3 = x^3*y^3 := by
  let k := ⁅y,x⁆
  have hswap : y*x=k*x*y := by simp [k,commutatorElement_def,mul_assoc]
  have hxc (a : G) : x*(k*a)=k*(x*a) := by rw [←mul_assoc,hc x,mul_assoc]
  have hyc (a : G) : y*(k*a)=k*(y*a) := by rw [←mul_assoc,hc y,mul_assoc]
  have hs (a : G) : y*(x*a)=k*(x*(y*a)) := by rw [←mul_assoc,hswap]; simp only [mul_assoc]
  calc
    (x*y)^3=k^3*(x^3*y^3) := by
      simp only [pow_succ,pow_zero,one_mul,mul_assoc,hs,hxc,hyc]
    _ = x^3*y^3 := by rw [h3,one_mul]


/-- The original cubic line, restricted to the literal ambient odd core. -/
def cubicCoreLine (x : c.H₁) : Subgroup (cubicOddCore c x) :=
  (zpowers ((x:c.H):G)).subgroupOf (cubicOddCore c x)

omit [Finite G] in
theorem cubicCoreLine_le_center (x : c.H₁) :
    cubicCoreLine c x ≤ center (cubicOddCore c x) := by
  intro w hw
  apply mem_center_iff.mpr
  intro d
  apply Subtype.ext
  have hd : (d:G) ∈ Subgroup.centralizer (zpowers ((x:c.H):G) : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
    exact (map_subtype_le (pPrimeCore 2 (cubicCentralizer c x))) d.property
  exact (hd w hw).symm

omit [Finite G] in
instance cubicCoreLine_normal (x : c.H₁) : (cubicCoreLine c x).Normal :=
  ⟨fun w hw d => by
    rw [mem_center_iff.mp (cubicCoreLine_le_center c x hw) d,mul_inv_cancel_right]
    exact hw⟩

omit [Finite G] in
theorem cubicCoreLine_card (x : c.H₁) (hx : orderOf x=3) :
    Nat.card (cubicCoreLine c x)=3 := by
  rw [cubicCoreLine,Nat.card_congr (subgroupOfEquivOfLe (cubic_line_le_oddCore c x hx)).toEquiv,
    Nat.card_zpowers,orderOf_coe,orderOf_coe,hx]

namespace CubicTorus
variable {c} (t : CubicTorus c)

private theorem left_oddCore_cube_mul (a b : cubicOddCore c t.x) :
    (a*b)^3=a^3*b^3 := by
  let D := cubicOddCore c t.x
  let W := zpowers ((t.x:c.H):G)
  have hcomm : ⁅D,D⁆ ≤ W := (cubic_oddCore_inversion c t.x t.x_order
    t.z ((orderOf_coe t.z).trans t.z_order) t.centralizer).2
  have hmem : (⁅b,a⁆:D).val ∈ W :=
    hcomm (commutator_mem_commutator b.property a.property)
  apply cube_mul_of_central_cubic_commutator
  · intro d
    apply Subtype.ext
    have hd : (d:G) ∈ Subgroup.centralizer (W:Set G) := by
      change (d:G) ∈ Subgroup.centralizer (zpowers ((t.x:c.H):G) : Set G)
      rw [zpowers_eq_closure,centralizer_closure]
      exact (map_subtype_le (pPrimeCore 2 (cubicCentralizer c t.x))) d.property
    exact (hd _ hmem).symm
  · apply Subtype.ext
    exact orderOf_dvd_iff_pow_eq_one.mp (by
      simpa only [W,Nat.card_zpowers,orderOf_coe,t.x_order] using W.orderOf_dvd_natCard hmem)

/-- Every element of the actual left cubic odd core cubes to one. -/
theorem left_oddCore_cube (d : cubicOddCore c t.x) : d^3=1 := by
  let D := cubicOddCore c t.x
  let C := cubicCentralizer c t.x
  have hnorm : normalizer (C:Set G) ≤ normalizer (D:Set G) :=
    normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C)
  have hzC : (t.z:G) ∈ C := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.x.val.property)).symm
  have hnN : (t.n:G) ∈ cubicNormalizer c t.x := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers ((t.n:G)*((t.x:c.H):G)*(t.n:G)⁻¹) = _
    rw [show (t.n:G)*((t.x:c.H):G)*(t.n:G)⁻¹=(((t.x:c.H):G))⁻¹ from
      congrArg Subtype.val t.invert_left,zpowers_inv]
  have hNC : cubicNormalizer c t.x ≤ normalizer (C:Set G) := by
    have hh := normalizer_le_normalizer_centralizer (zpowers ((t.x:c.H):G))
    have he : Subgroup.centralizer (zpowers ((t.x:c.H):G) : Set G)=C := by
      rw [zpowers_eq_closure,centralizer_closure]; rfl
    rwa [he] at hh
  let a : normalizer (D:Set G) := ⟨t.z,hnorm (C.le_normalizer hzC)⟩
  let b : normalizer (D:Set G) := ⟨t.n,hnorm (hNC hnN)⟩
  have ha : a^2=1 := Subtype.ext (by
    change (t.z:G)^2=1
    simpa only [orderOf_coe,t.z_order] using pow_orderOf_eq_one (t.z:G))
  have hb : b^2=1 := Subtype.ext (by
    change (t.n:G)^2=1
    simpa only [orderOf_coe,t.n_order] using pow_orderOf_eq_one (t.n:G))
  have hab : Commute a b := Subtype.ext
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.n.property)).symm
  have hab2 : orderOf ((t.z:G)*(t.n:G))=2 := by
    have hp : ((t.z:G)*(t.n:G))^2=1 := by
      have hh := hab.mul_pow 2
      rw [ha,hb,one_mul] at hh
      exact congrArg Subtype.val hh
    have hne : (t.z:G)*(t.n:G)≠1 := by
      intro hh
      have hninv : (t.n:G)⁻¹=(t.n:G) := inv_eq_of_mul_eq_one_left
        (by simpa only [orderOf_coe,t.n_order,pow_two] using pow_orderOf_eq_one (t.n:G))
      have hzn : t.z=t.n := Subtype.ext ((eq_inv_of_mul_eq_one_left hh).trans hninv)
      apply t.outside
      rw [←hzn]
      exact mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1)
    exact (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hp) |>.resolve_left
      (fun he => hne (orderOf_eq_one_iff.mp he))
  obtain ⟨u,hu,v,hv,w,hw,he⟩ := D.exists_three_odd_centralizers
    (cubic_oddCore_odd c t.x) a b ha hb hab d d.property
  have hu3 : (⟨u,hu.1⟩:D)^3=1 := Subtype.ext
    (involution_fixed_three_cubes c D t.left_oddCore_isThreeGroup t.z
      ((orderOf_coe t.z).trans t.z_order) u hu)
  have hv3 : (⟨v,hv.1⟩:D)^3=1 := Subtype.ext
    (involution_fixed_three_cubes c D t.left_oddCore_isThreeGroup t.n
      ((orderOf_coe t.n).trans t.n_order) v hv)
  have hw3 : (⟨w,hw.1⟩:D)^3=1 := Subtype.ext
    (involution_fixed_three_cubes c D t.left_oddCore_isThreeGroup
      ((t.z:G)*(t.n:G)) hab2 w hw)
  have he' : d=(⟨u,hu.1⟩:D)*⟨v,hv.1⟩*⟨w,hw.1⟩ := Subtype.ext he
  rw [he',t.left_oddCore_cube_mul,t.left_oddCore_cube_mul,hu3,hv3,hw3,one_mul,one_mul]

omit [Finite G] in
/-- Interchange the factors while retaining the literal common torus. -/
def swap : CubicTorus (swapFactors c) where
  z := t.z
  n := t.n
  x := t.y
  y := t.x
  z_order := t.z_order
  n_order := t.n_order
  x_order := t.y_order
  y_order := t.x_order
  central_line := by change zpowers t.z=c.H₂⊓c.H₁; rw [inf_comm]; exact t.central_line
  centralizer := t.centralizer
  outside := by change t.n∉c.H₂⊔c.H₁; rw [sup_comm]; exact t.outside
  invert_left := t.invert_right
  invert_right := t.invert_left

theorem right_oddCore_cube (d : cubicOddCore (swapFactors c) t.y) : d^3=1 :=
  t.swap.left_oddCore_cube d

theorem left_oddCore_exponent : Monoid.exponent (cubicOddCore c t.x)=3 := by
  apply Nat.dvd_antisymm (Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr t.left_oddCore_cube)
  let x : cubicOddCore c t.x := ⟨t.x,cubic_line_le_oddCore c t.x t.x_order (mem_zpowers _)⟩
  have hx : orderOf x=3 := (orderOf_coe x).symm.trans
    ((orderOf_coe (t.x:c.H)).trans ((orderOf_coe t.x).trans t.x_order))
  exact hx ▸ Monoid.order_dvd_exponent x

theorem right_oddCore_exponent : Monoid.exponent (cubicOddCore (swapFactors c) t.y)=3 :=
  t.swap.left_oddCore_exponent

theorem left_oddCore_quotient_elementary :
    IsElementaryAbelian 3 (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) := by
  let D := cubicOddCore c t.x
  let W := cubicCoreLine c t.x
  let q := QuotientGroup.mk' W
  have hcomm := (cubic_oddCore_inversion c t.x t.x_order t.z
    ((orderOf_coe t.z).trans t.z_order) t.centralizer).2
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
  · intro a b
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective W a
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective W b
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hcomm (commutator_mem_commutator a.property b.property)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective W a
    rw [←map_pow,t.left_oddCore_cube,map_one]

theorem right_oddCore_quotient_elementary :
    IsElementaryAbelian 3
      (cubicOddCore (swapFactors c) t.swap.x ⧸ cubicCoreLine (swapFactors c) t.swap.x) :=
  t.swap.left_oddCore_quotient_elementary

omit [Finite G] in
theorem left_oddCore_quotient_card :
    Nat.card (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) * 3 =
      Nat.card (cubicOddCore c t.x) := by
  have hh := card_eq_card_quotient_mul_card_subgroup (cubicCoreLine c t.x)
  rw [cubicCoreLine_card c t.x t.x_order] at hh
  exact hh.symm

/-- The exact order-27 alternatives, retaining the actual central cubic line. -/
theorem left_oddCore_twentySeven (hcard : Nat.card (cubicOddCore c t.x)=27) :
    IsElementaryAbelian 3 (cubicOddCore c t.x) ∨
      (IsExtraspecial 3 (cubicOddCore c t.x) ∧
        (center (cubicOddCore c t.x)).map (cubicOddCore c t.x).subtype =
          zpowers ((t.x:c.H):G)) := by
  let D := cubicOddCore c t.x
  by_cases hc : IsMulCommutative D
  · left
    let := hc
    exact { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr t.left_oddCore_cube }
  · right
    have hZ : Nat.card (center D)=3 := OrderTwentySeven.center_card hcard hc
    have hWZ : cubicCoreLine c t.x = center D := eq_of_le_of_card_ge
      (cubicCoreLine_le_center c t.x) (by rw [hZ,cubicCoreLine_card c t.x t.x_order])
    have hquot : IsElementaryAbelian 3 (D ⧸ center D) := by
      let := t.left_oddCore_quotient_elementary
      let e := QuotientGroup.quotientMulEquivOfEq hWZ
      exact IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
    have hqcard : Nat.card (D ⧸ center D)=9 := OrderTwentySeven.quotient_center_card hcard hc
    have hnt : Nontrivial (D ⧸ center D) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hqcard]; decide)
    refine ⟨⟨hZ,hquot,hnt⟩,?_⟩
    rw [←hWZ,cubicCoreLine,map_subgroupOf_eq_of_le (cubic_line_le_oddCore c t.x t.x_order)]

theorem right_oddCore_twentySeven
    (hcard : Nat.card (cubicOddCore (swapFactors c) t.y)=27) :
    IsElementaryAbelian 3 (cubicOddCore (swapFactors c) t.y) ∨
      (IsExtraspecial 3 (cubicOddCore (swapFactors c) t.y) ∧
        (center (cubicOddCore (swapFactors c) t.y)).map (cubicOddCore (swapFactors c) t.y).subtype =
          zpowers ((t.y:c.H):G)) :=
  t.swap.left_oddCore_twentySeven hcard

end CubicTorus
/-- The opposite original factor acts on the actual cubic odd core. -/
def cubicOppositeAction (x : c.H₁) : c.H₂ →* MulAut (cubicOddCore c x) := by
  let D := cubicOddCore c x
  let C := cubicCentralizer c x
  let f : c.H₂ →* normalizer (D:Set G) := {
    toFun y := ⟨y, (normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C))
      (C.le_normalizer (opposite_factor_le_cubic_centralizer c x
        (mem_map_of_mem c.H.subtype y.property)))⟩
    map_one' := Subtype.ext rfl
    map_mul' _ _ := Subtype.ext rfl }
  exact D.normalizerMonoidHom.comp f

omit [Finite G] in
private theorem cubicOppositeAction_fixed_line (x : c.H₁) (y : c.H₂)
    (w : cubicOddCore c x) (hw : w ∈ cubicCoreLine c x) :
    cubicOppositeAction c x y w=w := by
  apply Subtype.ext
  change ((y:c.H):G)*(w:G)*(((y:c.H):G))⁻¹=(w:G)
  have hy : ((y:c.H):G) ∈ centralizer (zpowers ((x:c.H):G) : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
    exact opposite_factor_le_cubic_centralizer c x (mem_map_of_mem c.H.subtype y.property)
  rw [←hy w hw,mul_inv_cancel_right]

/-- Conjugation descends to the quotient by the original central cubic line. -/
def cubicOppositeQuotientAction (x : c.H₁) :
    c.H₂ →* MulAut (cubicOddCore c x ⧸ cubicCoreLine c x) where
  toFun y := QuotientGroup.congr _ _ (cubicOppositeAction c x y) (by
    apply le_antisymm
    · rintro w ⟨v,hv,rfl⟩
      change cubicOppositeAction c x y v ∈ cubicCoreLine c x
      rw [cubicOppositeAction_fixed_line c x y v hv]
      exact hv
    · intro w hw
      exact ⟨w,hw,cubicOppositeAction_fixed_line c x y w hw⟩)
  map_one' := by
    ext w
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c x) w
    change QuotientGroup.mk' (cubicCoreLine c x) (cubicOppositeAction c x 1 d) =
      QuotientGroup.mk' (cubicCoreLine c x) d
    rw [map_one]; rfl
  map_mul' y z := by
    ext w
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c x) w
    change QuotientGroup.mk' (cubicCoreLine c x) (cubicOppositeAction c x (y*z) d) =
      QuotientGroup.mk' (cubicCoreLine c x) (cubicOppositeAction c x y (cubicOppositeAction c x z d))
    rw [map_mul]; rfl

omit [Finite G] in
theorem cubicOppositeQuotientAction_mk (x : c.H₁) (y : c.H₂) (d : cubicOddCore c x) :
    cubicOppositeQuotientAction c x y (QuotientGroup.mk' (cubicCoreLine c x) d) =
      QuotientGroup.mk' (cubicCoreLine c x) (cubicOppositeAction c x y d) := rfl

namespace CubicTorus
variable {c} (t : CubicTorus c)

/-- The original marked central involution acts by inversion on the quotient. -/
theorem left_oddCore_quotient_inverted (d : cubicOddCore c t.x) :
    cubicOppositeQuotientAction c t.x ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
      (QuotientGroup.mk' (cubicCoreLine c t.x) d) =
        (QuotientGroup.mk' (cubicCoreLine c t.x) d)⁻¹ := by
  rw [cubicOppositeQuotientAction_mk]
  apply eq_inv_iff_mul_eq_one.mpr
  rw [←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (cubic_oddCore_inversion c t.x t.x_order t.z
    ((orderOf_coe t.z).trans t.z_order) t.centralizer).1 d d.property

/-- Except for the smallest core, the action of the opposite SL₂(3) on the
literal elementary quotient is faithful. -/
theorem left_oddCore_quotient_action_faithful
    (hlarge : Nat.card (cubicOddCore c t.x)≠3) :
    Function.Injective (cubicOppositeQuotientAction c t.x) := by
  let D := cubicOddCore c t.x
  let W := cubicCoreLine c t.x
  let q := QuotientGroup.mk' W
  let ρ := cubicOppositeQuotientAction c t.x
  let z : c.H₂ := ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
  have hz : orderOf z=2 := (orderOf_coe z).symm.trans t.z_order
  have hzρ : ρ z≠1 := by
    intro he
    have hW : W=⊤ := by
      apply top_unique
      intro d _
      have hinv := t.left_oddCore_quotient_inverted d
      change ρ z (q d)=(q d)⁻¹ at hinv
      rw [he] at hinv
      change q d=(q d)⁻¹ at hinv
      have htwo : (q d)^2=1 := by
        rw [pow_two]
        calc
          q d * q d = (q d)⁻¹ * q d := congrArg (fun a => a * q d) hinv
          _ = 1 := inv_mul_cancel _
      have hthree : (q d)^3=1 := by rw [←map_pow,t.left_oddCore_cube,map_one]
      apply (QuotientGroup.eq_one_iff _).mp
      change q d=1
      simpa only [show 3=2+1 from rfl,pow_succ,htwo,one_mul] using hthree
    apply hlarge
    have hh := cubicCoreLine_card c t.x t.x_order
    rw [show cubicCoreLine c t.x=⊤ from hW,card_top] at hh
    exact hh
  let e := c.H₂_model.some
  let f := ρ.comp e.symm.toMonoidHom
  have hez : e z = -1 := by
    have hz2 : (e z)*(e z)=1 := by
      simpa only [←pow_two,e.orderOf_eq,hz] using pow_orderOf_eq_one (e z)
    have hzne : e z≠1 := by
      intro hh
      have hh' : z=1 := e.injective (hh.trans e.map_one.symm)
      simp [hh'] at hz
    exact (by decide +kernel : ∀ a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      a*a=1 → a≠1 → a = -1) _ hz2 hzne
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp
    (Matrix.SpecialLinearGroup.eq_bot_of_neg_one_not_mem (by decide : (2:ZMod 3)≠0)
      f.ker (by
        intro h
        apply hzρ
        change ρ (e.symm (-1))=1 at h
        rw [←hez,e.symm_apply_apply] at h
        exact h))
  intro a b hab
  apply e.injective
  apply hf
  change ρ (e.symm (e a))=ρ (e.symm (e b))
  simpa only [e.symm_apply_apply] using hab

end CubicTorus

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
