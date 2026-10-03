module

public import Stellmacher.Recognition.Parrott.SylowSeedFrame
public import Stellmacher.Recognition.Parrott.SylowFourLift
public import Stellmacher.Recognition.Parrott.DerivedMarkedPairCorrection
public import Theory.GroupAction.ElementaryJordanChainBasis
public import Stellmacher.Recognition.Parrott.SylowMarkedQuotientAction
public import Theory.GroupAction.MarkedJordanChainLift

/-!
# Outer generators for Parrott's supplied Sylow subgroup

The outer involution in the normalizer core splits every order-four quotient
lift. Starting with the quotient generator in C_T(t), the split lift stays in
the same supplied Sylow subgroup because its quotient class is unchanged.
Its cyclic subgroup and the original core generate that Sylow subgroup.

A chain with the prescribed t and v automatically supplies the required
bases: successive kernels of the displacement homomorphism separate its
entries, and the orders 8, 16, 32 identify the generated subgroups. The
conditional assembly theorems record this reduction. A chain with t and v
correct modulo ⟨z⟩ suffices: one core conjugation corrects both marks while
preserving the literal subgroups, the quotient generator, and fourth power
one. The marked quotient action supplies that chain by lifting its Jordan
chain through the central involution. Thus the final existence theorem
discharges every premise while retaining the prescribed t, v, F and Sylow.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.674, 677–678, especially equation (1).
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] {z : G} {e : ParrottSecondElementaryData z}

set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => pCore 2 H
set_option quotPrecheck false in
local notation "E" => (commutator J).map ((H).subtype.comp (J).subtype)

/-- A quotient generator in the supplied Sylow generates it together with
the original two-core. No assertion about the lift's order is used here. -/
public theorem ParrottSecondElementaryData.sylow_eq_zpowers_sup_core
    (e : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (x : H) (hx : (x : G) ∈ (e.sylow : Subgroup G))
    (horder : orderOf (QuotientGroup.mk' J x) = 4) :
    (e.sylow : Subgroup G) = zpowers (x : G) ⊔ (J).map (H).subtype := by
  let q := QuotientGroup.mk' J
  let T := (e.localSylow : Subgroup H)
  have hxT : x ∈ T := by
    rw [e.sylow_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact (H).subtype_injective hyx ▸ hy
  have hcard : Nat.card (T.map q) = 4 := by
    have hTcard : Nat.card T = 2048 := by
      rw [e.localSylow.card_eq_multiplicity, (h.card_and_solvable z).1]
      decide +kernel
    have hJT : J ≤ T := pCore_isPGroup.le_sylow_of_normal e.localSylow
    have hJcard : Nat.card ((J).subgroupOf T) = 512 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hJT).toEquiv]
      exact h.core_card
    have hh := ((J).subgroupOf T).index_mul_card
    change (J).relIndex T * Nat.card ((J).subgroupOf T) = Nat.card T at hh
    rw [hJcard, hTcard] at hh
    have hi : (J).relIndex T = 4 := by omega
    have heq := relIndex_ker T q
    rw [QuotientGroup.ker_mk'] at heq
    exact heq.symm.trans hi
  have hmap : T.map q = zpowers (q x) := by
    symm
    exact eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem q hxT))
      (by rw [Nat.card_zpowers, horder, hcard])
  have hT : T = zpowers x ⊔ J := by
    have hh := congrArg (Subgroup.comap q) hmap
    rw [QuotientGroup.comap_map_mk', ← MonoidHom.map_zpowers,
      QuotientGroup.comap_map_mk'] at hh
    rw [sup_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal e.localSylow)] at hh
    exact hh.trans (sup_comm _ _)
  rw [e.sylow_map]
  change T.map (H).subtype = _
  rw [hT, Subgroup.map_sup, MonoidHom.map_zpowers]
  rfl

/-- The actual supplied Sylow has an outer generator of fourth power one.
The marked t,v and the elementary subgroup are retained; no action identities
for this particular generator are asserted. -/
public theorem ParrottNormalizerFusionData.exists_outer_generator
    (n : ParrottNormalizerFusionData e)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    ∃ x : H, (x : G) ∈ (e.sylow : Subgroup G) ∧
      orderOf (QuotientGroup.mk' J x) = 4 ∧ x ^ 4 = 1 ∧
      (e.sylow : Subgroup G) = zpowers (x : G) ⊔ (J).map (H).subtype := by
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  have hC : Nat.card ((e.sylow : Subgroup G) ⊓ centralizer ({n.t} : Set G) :
      Subgroup G) = 1024 := by
    rw [← n.core_eq_sylow_centralizer, card_map_of_injective N.subtype_injective]
    exact n.core_card
  obtain ⟨y, hy, hyorder⟩ := e.t_centralizer_exists_quotient_order_four h
    n.t n.t_mem_inf.1 n.t_not_mem_zpowers hC
  obtain ⟨u, huK, hu2, huJ⟩ :=
    e.exists_normalizer_core_involution_outside_original_core h hN n.sylow_lt_normalizer
  have hTH : (e.sylow : Subgroup G) ≤ H := by
    rw [e.sylow_map]
    exact map_subtype_le _
  have huH : u ∈ H := hTH (n.core_le_sylow huK)
  let uH : H := ⟨u, huH⟩
  have huHJ : uH ∉ J := fun hh => huJ (mem_map_of_mem (H).subtype hh)
  have huH2 : orderOf uH = 2 := (Subgroup.orderOf_coe uH).symm.trans hu2
  obtain ⟨x, hxy, hx4⟩ := parrott_quotient_exists_lift_fourth_power_eq_one z h
    ⟨uH, huHJ, huH2⟩ (QuotientGroup.mk' J y) hyorder
  have hdiff : x * y⁻¹ ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' J (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hxT : (x : G) ∈ (e.sylow : Subgroup G) := by
    have hh := e.sylow.mul_mem (e.core_le_sylow (mem_map_of_mem (H).subtype hdiff)) hy.1
    change (x : G) * (y : G)⁻¹ * (y : G) ∈ (e.sylow : Subgroup G) at hh
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  have hxorder : orderOf (QuotientGroup.mk' J x) = 4 := hxy ▸ hyorder
  exact ⟨x, hxT, hxorder, hx4, e.sylow_eq_zpowers_sup_core h x hxT hxorder⟩

/-- The exact commutator chain forces both required basis identities.
Only membership in the prescribed subgroups is needed in addition to the
chain: its successive displacements prove independence. -/
public theorem ParrottNormalizerFusionData.elementary_bases_of_chain (n : ParrottNormalizerFusionData e)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (x : H) (u w : G) (hu : u ∈ E ⊓ e.F) (hw : w ∈ E)
    (hxt : Tits.parrottCommutator (x : G) n.t = 1)
    (hxv : Tits.parrottCommutator (x : G) n.v = n.t)
    (hxu : Tits.parrottCommutator (x : G) u = n.v)
    (hxw : Tits.parrottCommutator (x : G) w = u) :
    closure ({z, n.t, n.v, u} : Set G) = E ⊓ e.F ∧
      closure ({z, n.t, n.v, u, w} : Set G) = E := by
  let V := E
  let i := V.subtype
  obtain ⟨_, _, _, _, _, hElem, hCard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map ((H).subtype.comp (J).subtype)
  have hV : Nat.card V = 32 := by
    rw [card_map_of_injective (K := commutator J)
      (f := (H).subtype.comp (J).subtype)
      ((H).subtype_injective.comp (J).subtype_injective)]
    exact hCard
  let zV : V := ⟨z, e.z_mem_inf.1⟩
  let tV : V := ⟨n.t, n.t_mem_inf.1⟩
  let vV : V := ⟨n.v, n.v_mem_inf.1⟩
  let uV : V := ⟨u, hu.1⟩
  let wV : V := ⟨w, hw⟩
  let U := (E ⊓ e.F).subgroupOf V
  have hUmap : U.map i = E ⊓ e.F := map_subgroupOf_eq_of_le inf_le_left
  have hU : Nat.card U = 16 := by
    rw [← card_map_of_injective (K := U) V.subtype_injective, hUmap]
    exact e.inf_card
  have hxN : (x : G)⁻¹ ∈ normalizer (V : Set G) := by
    rw [parrott_derived_normalizer_of_nTwo hN z h]
    exact (H).inv_mem x.property
  let a := V.normalizerMonoidHom ⟨(x : G)⁻¹, hxN⟩
  let s : V →* V := {
    toFun := fun v => a v * v
    map_one' := by simp
    map_mul' := by intro b c; simp only [map_mul]; ac_rfl }
  have hs (v : V) : i (s v) = Tits.parrottCommutator (x : G) (i v) := by
    have hsq : (v : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (v : G) v.property
    have hinv : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq)
    change (x : G)⁻¹ * (v : G) * ((x : G)⁻¹)⁻¹ * (v : G) =
      (x : G)⁻¹ * (v : G)⁻¹ * (x : G) * (v : G)
    rw [inv_inv, hinv]
  have sz : s zV = 1 := by
    apply V.subtype_injective
    rw [hs, map_one]
    exact (Tits.parrottCommutator_eq_one_iff _ _).mpr
      (mem_centralizer_singleton_iff.mp x.property)
  have st : s tV = 1 := by
    apply V.subtype_injective
    rw [hs, map_one]
    exact hxt
  have sv : s vV = tV := V.subtype_injective ((hs vV).trans hxv)
  have su : s uV = vV := V.subtype_injective ((hs uV).trans hxu)
  have sw : s wV = uV := V.subtype_injective ((hs wV).trans hxw)
  have ht : tV ≠ 1 := by
    intro ht
    have htG : n.t = 1 := congrArg i ht
    exact n.t_not_mem_zpowers (htG ▸ (zpowers z).one_mem)
  have hZmap : (closure ({zV, tV, vV} : Set V)).map i =
      (zpowers z ⊔ zpowers n.t) ⊔ zpowers n.v := by
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton]
    change closure ({z, n.t, n.v} : Set G) = _
    rw [show ({z, n.t, n.v} : Set G) = ({z} ∪ {n.t}) ∪ {n.v} by
      ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto,
      Subgroup.closure_union, Subgroup.closure_union]
    simp only [← zpowers_eq_closure]
  have hZ : Nat.card (closure ({zV, tV, vV} : Set V)) = 8 := by
    rw [← card_map_of_injective (K := closure ({zV, tV, vV} : Set V))
      V.subtype_injective, hZmap, ← n.omega_center_eq]
    exact n.ambient_omega_center_card
  obtain ⟨hUB, hVB⟩ := Theory.GroupAction.elementary_thirty_two_basis_of_chain s zV tV vV uV wV U hV hU hZ
    e.z_mem_inf n.t_mem_inf n.v_mem_inf hu ht sz st sv su sw
  constructor
  · have hh := congrArg (Subgroup.map i) hUB
    rw [MonoidHom.map_closure, hUmap] at hh
    simpa only [Set.image_insert_eq, Set.image_singleton, i, zV, tV, vV, uV, wV,
      Subgroup.coe_subtype] using hh
  · have hh := congrArg (Subgroup.map i) hVB
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map] at hh
    have hi : i.range = V := range_subtype V
    rw [hi] at hh
    simpa only [Set.image_insert_eq, Set.image_singleton, i, zV, tV, vV, uV, wV,
      Subgroup.coe_subtype] using hh


/-- Assemble an action frame from a compatible chain in the actual derived
group. This discharges the two basis fields and the Sylow generation field. -/
public theorem ParrottNormalizerFusionData.exists_sylow_action_of_chain
    (n : ParrottNormalizerFusionData e)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (x : H) (hx : (x : G) ∈ (e.sylow : Subgroup G))
    (hxorder : orderOf (QuotientGroup.mk' J x) = 4) (hx4 : x ^ 4 = 1)
    (u w : G) (hu : u ∈ E ⊓ e.F) (hw : w ∈ E)
    (hxt : Tits.parrottCommutator (x : G) n.t = 1)
    (hxv : Tits.parrottCommutator (x : G) n.v = n.t)
    (hxu : Tits.parrottCommutator (x : G) u = n.v)
    (hxw : Tits.parrottCommutator (x : G) w = u) :
    Nonempty (ParrottSylowActionData n) := by
  obtain ⟨hinf, hderived⟩ := n.elementary_bases_of_chain h hN x u w hu hw hxt hxv hxu hxw
  exact ⟨{
    u := u
    w := w
    x := x
    inf_basis := hinf
    derived_basis := hderived
    sylow_eq := e.sylow_eq_zpowers_sup_core h x hx hxorder
    eq01_x := congrArg (H).subtype hx4
    eq01_xt := hxt
    eq01_xv := hxv
    eq01_xu := hxu
    eq01_xw := hxw }⟩

/-- A chain whose last two entries agree with the prescribed marks modulo
⟨z⟩ supplies an action frame. One element of the original core corrects both
marks simultaneously, and conjugating the entire chain by it preserves the
supplied Sylow, the elementary subgroup, and fourth power one. -/
public theorem ParrottNormalizerFusionData.exists_sylow_action_of_chain_mod_center
    (n : ParrottNormalizerFusionData e)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (x : H) (hx : (x : G) ∈ (e.sylow : Subgroup G))
    (hxorder : orderOf (QuotientGroup.mk' J x) = 4) (hx4 : x ^ 4 = 1)
    (t0 v0 u w : G) (ht0 : t0 ∈ E) (hv0 : v0 ∈ E)
    (ht : t0 * n.t⁻¹ ∈ zpowers z) (hv : v0 * n.v⁻¹ ∈ zpowers z)
    (hu : u ∈ E ⊓ e.F) (hw : w ∈ E)
    (hxt : Tits.parrottCommutator (x : G) t0 = 1)
    (hxv : Tits.parrottCommutator (x : G) v0 = t0)
    (hxu : Tits.parrottCommutator (x : G) u = v0)
    (hxw : Tits.parrottCommutator (x : G) w = u) :
    Nonempty (ParrottSylowActionData n) := by
  obtain ⟨j, hj, hjt, hjv⟩ := n.exists_derived_marked_pair_correction h t0 v0 ht0 hv0 ht hv
  obtain ⟨jH, hjJ, rfl⟩ := hj
  let c := MulAut.conj (jH : G)
  let x' : H := jH * x * jH⁻¹
  have hx' : (x' : G) = c (x : G) := rfl
  have hjT : (jH : G) ∈ (e.sylow : Subgroup G) :=
    e.core_le_sylow (mem_map_of_mem (H).subtype hjJ)
  have hx'T : (x' : G) ∈ (e.sylow : Subgroup G) :=
    e.sylow.mul_mem (e.sylow.mul_mem hjT hx) (e.sylow.inv_mem hjT)
  have hx'order : orderOf (QuotientGroup.mk' J x') = 4 := by
    have hjq : QuotientGroup.mk' J jH = 1 := (QuotientGroup.eq_one_iff _).mpr hjJ
    simpa only [x', map_mul, map_inv, hjq, one_mul, inv_one, mul_one] using hxorder
  have hx'4 : x' ^ 4 = 1 := by
    have hh := congrArg (MulAut.conj jH) hx4
    simpa only [map_pow, map_one, MulAut.conj_apply, x'] using hh
  have hjE : (jH : G) ∈ normalizer (E : Set G) := by
    rw [parrott_derived_normalizer_of_nTwo hN z h]
    exact jH.property
  have hjF : (jH : G) ∈ normalizer (e.F : Set G) := e.sylow_le_normalizer hjT
  have hcu : c u ∈ E ⊓ e.F :=
    ⟨(mem_normalizer_iff.mp hjE u).mp hu.1, (mem_normalizer_iff.mp hjF u).mp hu.2⟩
  have hcw : c w ∈ E := (mem_normalizer_iff.mp hjE w).mp hw
  have hct : c t0 = n.t := hjt
  have hcv : c v0 = n.v := hjv
  have hc (a b : G) : c (Tits.parrottCommutator a b) =
      Tits.parrottCommutator (c a) (c b) := by
    simp only [Tits.parrottCommutator, map_mul, map_inv]
  apply n.exists_sylow_action_of_chain h hN x' hx'T hx'order hx'4 (c u) (c w) hcu hcw
  · simpa only [hc, hct, map_one, hx'] using congrArg c hxt
  · simpa only [hc, hct, hcv, hx'] using congrArg c hxv
  · simpa only [hc, hcv, hx'] using congrArg c hxu
  · simpa only [hc, hx'] using congrArg c hxw

/-- Lift the marked quotient chain to actual derived elements. The invariant
hyperplane E ∩ F contains u; t and v are retained modulo the central involution. -/
public theorem ParrottNormalizerFusionData.outer_chain_of_marked_quotient_action
    (n : ParrottNormalizerFusionData e)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (x : H) (hx : (x : G) ∈ (e.sylow : Subgroup G)) (hx4 : x ^ 4 = 1)
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (q : E →* W) (hq : Function.Surjective q)
    (hker : q.ker = (zpowers z).subgroupOf E) (hW : Nat.card W = 16)
    (b : MulAut W)
    (hformula : ∀ g g' : E, (g' : G) = (x : G)⁻¹ * (g : G) * (x : G) →
      b (q g) = q g')
    (hfixed : Nat.card (FixedPoints.subgroup (zpowers b) W) = 2)
    (hbt : b (q ⟨n.t, n.t_mem_inf.1⟩) = q ⟨n.t, n.t_mem_inf.1⟩)
    (hbv : b (q ⟨n.v, n.v_mem_inf.1⟩) * q ⟨n.v, n.v_mem_inf.1⟩ =
      q ⟨n.t, n.t_mem_inf.1⟩) :
    ∃ t0 v0 u w : G,
      t0 ∈ E ∧ v0 ∈ E ∧ u ∈ E ⊓ e.F ∧ w ∈ E ∧
      t0 * n.t⁻¹ ∈ zpowers z ∧ v0 * n.v⁻¹ ∈ zpowers z ∧
      Tits.parrottCommutator (x : G) t0 = 1 ∧
      Tits.parrottCommutator (x : G) v0 = t0 ∧
      Tits.parrottCommutator (x : G) u = v0 ∧
      Tits.parrottCommutator (x : G) w = u := by
  let V := E
  let i := V.subtype
  obtain ⟨_, _, _, _, _, hElem, hCard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map ((H).subtype.comp (J).subtype)
  have hV : Nat.card V = 32 := by
    rw [card_map_of_injective (K := commutator J)
      (f := (H).subtype.comp (J).subtype)
      ((H).subtype_injective.comp (J).subtype_injective)]
    exact hCard
  let tV : V := ⟨n.t, n.t_mem_inf.1⟩
  let vV : V := ⟨n.v, n.v_mem_inf.1⟩
  let U := (E ⊓ e.F).subgroupOf V
  have hUmap : U.map i = E ⊓ e.F := map_subgroupOf_eq_of_le inf_le_left
  have hUcard : Nat.card U = 16 := by
    rw [← card_map_of_injective (K := U) V.subtype_injective, hUmap]
    exact e.inf_card
  have hU : U.index = 2 := by
    have hc := U.card_mul_index
    rw [hUcard, hV] at hc
    omega
  have hxN : (x : G)⁻¹ ∈ normalizer (V : Set G) := by
    rw [parrott_derived_normalizer_of_nTwo hN z h]
    exact (H).inv_mem x.property
  let r : normalizer (V : Set G) := ⟨(x : G)⁻¹, hxN⟩
  let a := V.normalizerMonoidHom r
  have hr4 : r ^ 4 = 1 := by
    apply Subtype.ext
    change ((x : G)⁻¹) ^ 4 = 1
    have hh : (x : G) ^ 4 = 1 := congrArg (H).subtype hx4
    rw [inv_pow, hh, inv_one]
  have ha4 : a ^ 4 = 1 := by
    rw [← map_pow, hr4, map_one]
  have hcompat (g : V) : q (a g) = b (q g) :=
    (hformula g (a g) (by change (x : G)⁻¹ * (g : G) * ((x : G)⁻¹)⁻¹ = _; rw [inv_inv])).symm
  have ht : q tV ≠ 1 := by
    intro ht
    have htker : tV ∈ q.ker := ht
    rw [hker] at htker
    exact n.t_not_mem_zpowers htker
  have hstable : ∀ u ∈ U, a u ∈ U := by
    intro u hu
    refine ⟨(a u).property, ?_⟩
    have hxF : (x : G)⁻¹ ∈ normalizer (e.F : Set G) :=
      (normalizer (e.F : Set G)).inv_mem (e.sylow_le_normalizer hx)
    have huF : (u : G) ∈ e.F := hu.2
    have hh := (mem_normalizer_iff.mp hxF (u : G)).mp huF
    change (x : G)⁻¹ * (u : G) * ((x : G)⁻¹)⁻¹ ∈ e.F
    exact hh
  obtain ⟨t0, v0, u, w, ht0, hv0, hu, hxt, hxv, hxu, hxw⟩ :=
    Theory.GroupAction.marked_jordan_chain_lift a b q hq ha4 hcompat hW hfixed
      tV vV ht hbt hbv U hU hstable
  have hs (g : V) : i (a g * g) = Tits.parrottCommutator (x : G) (i g) := by
    have hsq : (g : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (g : G) g.property
    have hinv : (g : G)⁻¹ = g := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq)
    change (x : G)⁻¹ * (g : G) * ((x : G)⁻¹)⁻¹ * (g : G) =
      (x : G)⁻¹ * (g : G)⁻¹ * (x : G) * (g : G)
    rw [inv_inv, hinv]
  have difference {g k : V} (heq : q g = q k) : (g : G) * (k : G)⁻¹ ∈ zpowers z := by
    have hh : g / k ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_div, heq, div_eq_mul_inv, mul_inv_cancel]
    rw [hker] at hh
    change ((g / k : V) : G) ∈ zpowers z at hh
    simpa only [Subgroup.coe_div, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hh
  refine ⟨t0, v0, u, w, t0.property, v0.property, hu, w.property,
    difference ht0, difference hv0, ?_, ?_, ?_, ?_⟩
  · exact (hs t0).symm.trans (congrArg i hxt)
  · exact (hs v0).symm.trans (congrArg i hxv)
  · exact (hs u).symm.trans (congrArg i hxu)
  · exact (hs w).symm.trans (congrArg i hxw)

/-- The quotient action and the fourth-power lift together produce an actual
action frame for the supplied Sylow subgroup. -/
public theorem ParrottNormalizerFusionData.exists_sylow_action
    (n : ParrottNormalizerFusionData e)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    Nonempty (ParrottSylowActionData n) := by
  obtain ⟨x, hx, hxorder, hx4, _⟩ := n.exists_outer_generator h hN
  obtain ⟨hElem, hW, q, b, hq, hker, hformula, hfixed, hbt, hbv⟩ :=
    n.marked_quotient_action h x hx hxorder
  let : IsElementaryAbelian 2 (
      (commutator (pCore 2 (centralizer ({z} : Set G)))) ⧸
        (center (pCore 2 (centralizer ({z} : Set G)))).subgroupOf
          (commutator (pCore 2 (centralizer ({z} : Set G))))) := hElem
  obtain ⟨t0, v0, u, w, ht0, hv0, hu, hw, ht, hv, hxt, hxv, hxu, hxw⟩ :=
    n.outer_chain_of_marked_quotient_action h hN x hx hx4 q hq hker hW b
      hformula hfixed hbt hbv
  exact n.exists_sylow_action_of_chain_mod_center h hN x hx hxorder hx4
    t0 v0 u w ht0 hv0 ht hv hu hw hxt hxv hxu hxw

end Stellmacher.Recognition
