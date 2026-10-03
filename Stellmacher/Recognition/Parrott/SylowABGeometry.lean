module

public import Stellmacher.Recognition.Parrott.SylowThreeGeneratorSelection
public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOrder
public import Stellmacher.Recognition.Parrott.NormalizerCoreSquareRoots
public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOmega

/-!
# Choosing a by the supplied Sylow-three action

For every supplied outer action frame, the second core's derived group is
⟨b,F⟩. If b centralized u, it would centralize E∩F, forcing that derived
group to equal E∨F, contrary to its known intersection with E. Hence [b,u]=z.

The outer square has commutator v with w and therefore lies outside the
original core. Transporting this involution by Q, and applying the outer
square-root bridge, puts a Q-conjugate of x in the original core. Its action
on v forces the same conjugator to send t to z. Conjugating u back now
produces a with [a,b]=t and [a,x] in ⟨t⟩. It lies in F outside E, which
supplies its basis and [a,w]=z. Only [b,w]=1 remains an input to the final
three-generator assembly; the involution choice and subsequent adjustments
are already proved below this module.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–679, equations (2)–(8). The root-transport proof adapts the
argument in SylowSquareTransport to the earlier action frame, retaining a
conjugator in Q and without importing the completed-generator modules.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

private theorem core_derived_pc [Finite G] (h : ParrottCentralizerHypotheses z)
    {g k : G} (hg : g ∈ J) (hk : k ∈ E) :
    Tits.parrottCommutator g k ∈ zpowers z := by
  let K := pCore 2 H
  let embed := (H).subtype.comp K.subtype
  obtain ⟨gH, hgK, rfl⟩ := hg
  obtain ⟨kK, hkK, rfl⟩ := hk
  obtain ⟨hZ, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  have hcomm : ⁅commutator K, (⊤ : Subgroup K)⁆ ≤ center K := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      commutator_upperCentralSeries_top_le K 1
  have hh := mem_map_of_mem embed (hcomm (commutator_mem_commutator
    ((commutator K).inv_mem hkK) (show (⟨gH, hgK⟩ : K)⁻¹ ∈ ⊤ from mem_top _)))
  rw [hZ] at hh
  have heq : embed ⁅kK⁻¹, (⟨gH, hgK⟩ : K)⁻¹⁆ =
      (Tits.parrottCommutator (gH : G) (embed kK))⁻¹ := by
    simp only [commutatorElement_def,
      Tits.parrottCommutator, mul_inv_rev, inv_inv, map_mul, map_inv]
    change (embed kK)⁻¹ * (gH : G)⁻¹ * embed kK * (gH : G) = _
    group
  rw [heq] at hh
  simpa only [inv_inv, embed, K, Subgroup.coe_subtype] using (zpowers z).inv_mem hh


private theorem central_commutator_eq_z [Finite G] (h : ParrottCentralizerHypotheses z)
    {g k : G} (hc : Tits.parrottCommutator g k ∈ zpowers z)
    (hne : ¬ Commute g k) : Tits.parrottCommutator g k = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hc
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hc
  have hi2 : i < 2 := Finset.mem_range.mp hi
  interval_cases i
  · exact (hne ((Tits.parrottCommutator_eq_one_iff _ _).mp
      (by simpa using heq.symm))).elim
  · simpa using heq.symm

/-- Equation (2) for b,u is forced for every supplied action frame. -/
public theorem ParrottSylowActionData.b_commutator_u [Finite G]
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z)
    (hN : IsNTwoGroup G) : Tits.parrottCommutator n.b f.u = z := by
  let N := normalizer (e.F : Set G)
  let X := (pCore 2 N).map N.subtype
  let D := (commutator X).map X.subtype
  have hbD : n.b ∈ D := n.core_fixed_le_derived (by
    rw [n.core_fixed]; exact mem_zpowers _)
  have hFD : e.F ≤ D := e.elementary_le_normalizer_core_derived h hN n.sylow_lt_normalizer
  have hDcard : Nat.card D = 64 := e.normalizer_core_derived_order h hN n.sylow_lt_normalizer
  have hbF : n.b ∉ e.F := by
    intro hb
    let : IsElementaryAbelian 2 e.F := e.elementary
    have hh : n.b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian n.b hb
    rw [n.b_sq] at hh
    have ho := n.v_order
    rw [hh, orderOf_one] at ho
    omega
  have hgen : zpowers n.b ⊔ e.F = D := by
    let B := zpowers n.b ⊔ e.F
    have hBD : B ≤ D := sup_le (zpowers_le.mpr hbD) hFD
    have hFB : e.F < B := lt_of_le_of_ne le_sup_right (by
      intro heq
      exact hbF (heq ▸ (show n.b ∈ B from mem_sup_left (mem_zpowers _))))
    have hlt : Nat.card e.F < Nat.card B := by
      have hle := card_le_of_le hFB.le
      exact lt_of_le_of_ne hle (fun heq => hFB.ne (eq_of_le_of_card_ge hFB.le heq.ge))
    have hdvd := card_dvd_of_le (show e.F ≤ B from le_sup_right)
    rw [e.card] at hlt hdvd
    obtain ⟨k, hk⟩ := hdvd
    apply eq_of_le_of_card_ge hBD
    rw [hDcard]
    omega
  have hu : f.u ∈ E ⊓ e.F := by
    rw [← f.inf_basis]; exact subset_closure (by simp)
  have hb := n.three_generator_b_properties h
  apply central_commutator_eq_z h (core_derived_pc h hb.1 hu.1)
  intro hbu
  have hbC : n.b ∈ centralizer ((E ⊓ e.F : Subgroup G) : Set G) := by
    rw [← f.inf_basis, centralizer_closure]
    apply mem_centralizer_iff.mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact (mem_centralizer_singleton_iff.mp (map_subtype_le _ hb.1)).symm
    · exact hb.2.1.symm.eq
    · exact (show Commute n.b n.v by rw [← n.b_sq]; exact Commute.self_pow _ _).symm.eq
    · exact hbu.symm.eq
  have hDC : D ≤ centralizer ((E ⊓ e.F : Subgroup G) : Set G) := by
    rw [← hgen]
    apply sup_le (zpowers_le.mpr hbC)
    let : IsElementaryAbelian 2 e.F := e.elementary
    intro g hg k hk
    exact setLike_mul_comm (s := e.F) hk.2 hg
  have hDC := hDC.trans_eq (e.elementary_inf_centralizer h)
  have hDA : D = E ⊔ e.F := eq_of_le_of_card_ge hDC
    (by rw [hDcard, e.elementary_join_card h])
  have hED : E ≤ D := hDA ▸ le_sup_left
  have hEF : E ≤ e.F := by
    have hDE := e.normalizer_core_derived_inf_original_derived h hN n.sylow_lt_normalizer
    have hh : E ≤ D ⊓ E := le_inf hED le_rfl
    exact (hh.trans_eq hDE).trans inf_le_right
  have hEcard : Nat.card E = 32 := by
    rw [card_map_of_injective (K := commutator (pCore 2 H))
      ((H).subtype_injective.comp (pCore 2 H).subtype_injective)]
    exact (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  exact e.ne_derived (eq_of_le_of_card_ge hEF (by rw [e.card, hEcard])).symm

private theorem conjugate_of_pc {x w u : G} (hu : u ^ 2 = 1)
    (h : Tits.parrottCommutator x w = u) : x⁻¹ * w * x = w * u := by
  have hh := (Tits.parrottCommutator_eq_iff _ _ _).mp h
  have huu : u*u=1 := by simpa only [pow_two] using hu
  have he := congrArg (fun p : G => x⁻¹*p*u) hh
  simpa only [mul_assoc, inv_mul_cancel_left, huu, mul_one] using he.symm

/-- The square of the outer generator has the next displacement on w. -/
public theorem ParrottSylowActionData.square_commutator_w [Finite G]
    (f : ParrottSylowActionData n) :
    Tits.parrottCommutator (f.x ^ 2) f.w = n.v := by
  let : IsElementaryAbelian 2 e.F := e.elementary
  have hu : f.u ∈ e.F := by
    have hh : f.u ∈ E ⊓ e.F := by rw [← f.inf_basis]; exact subset_closure (by simp)
    exact hh.2
  have hu2 : f.u^2=1 := elemPow_eq_one_of_isElementaryAbelian _ hu
  have hv2 : n.v^2=1 := n.v_order ▸ pow_orderOf_eq_one n.v
  have hw := conjugate_of_pc hu2 f.eq01_xw
  have huu := conjugate_of_pc hv2 f.eq01_xu
  have he : (f.x^2)⁻¹ * f.w * (f.x^2) = f.w * n.v := by
    calc
      _ = f.x⁻¹ * (f.x⁻¹ * f.w * f.x) * f.x := by simp only [pow_two, mul_inv_rev]; group
      _ = f.x⁻¹ * (f.w * f.u) * f.x := by rw [hw]
      _ = (f.x⁻¹ * f.w * f.x) * (f.x⁻¹ * f.u * f.x) := by group
      _ = f.w * n.v := by rw [hw, huu, mul_assoc, ← mul_assoc f.u f.u, ← pow_two, hu2, one_mul]
  calc
    _ = ((f.x^2)⁻¹ * f.w * (f.x^2))⁻¹ * f.w := by simp only [Tits.parrottCommutator]; group
    _ = n.v := by
      rw [he, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hv2)

/-- A conjugator in the supplied Q transports x into the original core. -/
public theorem ParrottSylowActionData.exists_three_conjugate_in_core [Finite G]
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z)
    (hN : IsNTwoGroup G) :
    ∃ q : n.Q, ((q : normalizer (e.F : Set G)) : G) * f.x *
      ((q : normalizer (e.F : Set G)) : G)⁻¹ ∈ J := by
  let HC := centralizer ({z} : Set G)
  let JC := pCore 2 HC
  let EC := (commutator JC).map (HC.subtype.comp JC.subtype)
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let X := K.map N.subtype
  let U := omega₁ K (p := 2)
  let W := U.map (N.subtype.comp K.subtype)
  have hxX : f.x ∈ X := by
    change f.x ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype
    rw [n.core_eq_sylow_centralizer]
    exact ⟨(f.sylow_eq.symm ▸ mem_sup_left (mem_zpowers f.x)),
      mem_centralizer_singleton_iff.mpr
        ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt)⟩
  have hxW : f.x ∉ W := by
    intro hx
    have hWC : W = X ⊓ centralizer
        ((center U).map ((N.subtype.comp K.subtype).comp U.subtype) : Set G) :=
      n.omega_eq_centralizer
    rw [hWC] at hx
    have hv : n.v ∈ (center U).map ((N.subtype.comp K.subtype).comp U.subtype) := by
      have hZ : (center U).map ((N.subtype.comp K.subtype).comp U.subtype) =
          (zpowers z ⊔ zpowers n.t) ⊔ zpowers n.v := n.omega_center_eq
      rw [hZ]
      exact mem_sup_right (mem_zpowers n.v)
    have hc : Commute f.x n.v := (mem_centralizer_iff.mp hx.2 n.v hv).symm
    have ht : n.t = 1 := f.eq01_xv.symm.trans
      ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
    have ho := n.t_order
    rw [ht, orderOf_one] at ho
    norm_num at ho
  have hsqJ : f.x ^ 2 ∉ JC.map HC.subtype := by
    intro hx
    have hw : f.w ∈ EC := by
      change f.w ∈ E
      rw [← f.derived_basis]; exact subset_closure (by simp)
    have hh := core_derived_pc h hx hw
    rw [f.square_commutator_w] at hh
    exact n.v_not_mem_core_center (n.core_center_eq.symm ▸ mem_sup_left hh)
  have hsq2 : (f.x ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using f.eq01_x
  have hsqOrder : orderOf (f.x ^ 2) = 2 := orderOf_eq_prime hsq2
    (fun heq => hsqJ (heq ▸ (JC.map HC.subtype).one_mem))
  obtain ⟨q, hq⟩ := e.normalizer_core_involution_transport h hN n.sylow_lt_normalizer
    n.Q n.core_fixed_le_derived (f.x ^ 2) (X.pow_mem hxX 2) hsq2
  let qN : N := q
  have hqE : (qN : G) * f.x ^ 2 * (qN : G)⁻¹ ∈ EC :=
    e.outer_involution_normalizer_conjugate_mem_derived h (f.x ^ 2) hsqJ hsqOrder qN hq
  let a := (qN : G) * f.x * (qN : G)⁻¹
  have haX : a ∈ X := by
    obtain ⟨xN, hxN, hex⟩ := hxX
    refine ⟨qN * xN * qN⁻¹, (inferInstance : K.Normal).conj_mem xN hxN qN, ?_⟩
    change (qN : G) * (xN : G) * (qN : G)⁻¹ = a
    change (xN : G) = f.x at hex
    rw [hex]
  have ha2 : a ^ 2 ∈ EC := by
    have heq : a ^ 2 = (qN : G) * f.x ^ 2 * (qN : G)⁻¹ :=
      (map_pow (MulAut.conj (qN : G)) f.x 2).symm
    rwa [heq]
  have hNW : N ≤ normalizer (W : Set G) := by
    let V := U.map K.subtype
    let : U.Characteristic := omega₁_characteristic K
    let : V.Normal := ConjAct.normal_of_characteristic_of_normal
    have hh := le_normalizer_map («H» := V) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, V, W, map_map] using hh
  refine ⟨q, ?_⟩
  by_contra haJ
  have haW : a ∈ W := e.normalizer_core_outer_square_mem_derived_mem_omega h hN
    n.sylow_lt_normalizer a haX ha2 haJ
  exact hxW ((mem_normalizer_iff.mp (hNW qN.property) f.x).mpr haW)

private theorem pc_swap (g k : G) :
    Tits.parrottCommutator g k = (Tits.parrottCommutator k g)⁻¹ := by
  simp only [Tits.parrottCommutator]; group

private theorem map_pc (r : G ≃* G) (g k : G) :
    r (Tits.parrottCommutator g k) = Tits.parrottCommutator (r g) (r k) := by
  simp only [Tits.parrottCommutator, map_mul, map_inv]

/-- The Q action chooses a with its elementary basis, equations (2),(5),
and the required a,x alternative, for every supplied action frame. -/
public theorem ParrottSylowActionData.exists_a_selection [Finite G]
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z)
    (hN : IsNTwoGroup G) :
    ∃ a : G, closure ({z,n.t,n.v,f.u,a} : Set G) = e.F ∧
      Tits.parrottCommutator a f.w = z ∧
      Tits.parrottCommutator a n.b = n.t ∧
      (Tits.parrottCommutator a f.x = 1 ∨ Tits.parrottCommutator a f.x = n.t) := by
  classical
  let : IsElementaryAbelian 2 e.F := e.elementary
  obtain ⟨q, hqx⟩ := f.exists_three_conjugate_in_core h hN
  let qG : G := ((q : normalizer (e.F : Set G)) : G)
  let r : G ≃* G := MulAut.conj qG
  have hqA : qG ∈ (n.Q : Subgroup (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype := mem_map_of_mem _ q.property
  have hrv : r n.v = n.v := by
    change qG*n.v*qG⁻¹=n.v
    rw [n.v_fixed qG hqA, mul_inv_cancel_right]
  have hrb : r n.b = n.b := by
    change qG*n.b*qG⁻¹=n.b
    rw [(n.three_generator_b_properties h).2.2 qG hqA, mul_inv_cancel_right]
  have hrtpc : Tits.parrottCommutator (r f.x) n.v = r n.t := by
    rw [← hrv, ← map_pc, f.eq01_xv]
  have hrt : r n.t = z := by
    rw [← hrtpc]
    apply central_commutator_eq_z h (core_derived_pc h hqx n.v_mem_inf.1)
    intro hc
    have hh : r n.t = 1 := hrtpc.symm.trans ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
    have ht : n.t=1 := r.injective (hh.trans (map_one r).symm)
    exact n.t_not_mem_zpowers (ht ▸ (zpowers z).one_mem)
  have hst : r.symm z = n.t := (r.symm_apply_eq).mpr hrt.symm
  have hsb : r.symm n.b = n.b := (r.symm_apply_eq).mpr hrb.symm
  let a := r.symm f.u
  have hu : f.u ∈ E ⊓ e.F := by
    rw [← f.inf_basis]; exact subset_closure (by simp)
  have hw : f.w ∈ E := by
    rw [← f.derived_basis]; exact subset_closure (by simp)
  have haF : a ∈ e.F := by
    have hqN : qG⁻¹ ∈ normalizer (e.F : Set G) :=
      (normalizer (e.F : Set G)).inv_mem (q : normalizer (e.F : Set G)).property
    simpa only [a, r, MulAut.conj_symm_apply, inv_inv] using
      (mem_normalizer_iff.mp hqN f.u).mp hu.2
  have hz2 : z^2=1 := h.involution ▸ pow_orderOf_eq_one z
  have hzinv : z⁻¹=z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz2)
  have hab : Tits.parrottCommutator a n.b = n.t := by
    change Tits.parrottCommutator (r.symm f.u) n.b = n.t
    rw [← hsb, ← map_pc, pc_swap f.u n.b, f.b_commutator_u h hN, hzinv, hst]
  have haE : a ∉ E := by
    intro ha
    have hh := core_derived_pc h (n.three_generator_b_properties h).1 ha
    rw [pc_swap n.b a, hab] at hh
    exact n.t_not_mem_zpowers (by simpa only [inv_inv] using (zpowers z).inv_mem hh)
  have habasis : closure ({z,n.t,n.v,f.u,a} : Set G) = e.F := by
    have hreorder : ({z,n.t,n.v,f.u,a} : Set G) = {z,n.t,n.v,f.u} ∪ {a} := by
      ext g; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto
    rw [hreorder, Subgroup.closure_union, ← zpowers_eq_closure, f.inf_basis]
    apply eq_of_le_of_card_ge (sup_le inf_le_right (zpowers_le.mpr haF))
    rw [card_sup_zpowers_of_normalizing_involution (E ⊓ e.F) a
      (elemPow_eq_one_of_isElementaryAbelian a haF) (fun hh => haE hh.1)]
    · rw [e.inf_card, e.card]
    · apply Subgroup.centralizer_le_normalizer
      intro g hg
      exact setLike_mul_comm (s := e.F) hg.2 haF
  have haw : Tits.parrottCommutator a f.w = z := by
    apply central_commutator_eq_z h (core_derived_pc h (e.le_core haF) hw)
    intro hc
    apply haE
    rw [← parrott_derived_centralizer z h, ← f.derived_basis, centralizer_closure]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact setLike_mul_comm (s := e.F) e.z_mem_inf.2 haF
    · exact setLike_mul_comm (s := e.F) n.t_mem_inf.2 haF
    · exact setLike_mul_comm (s := e.F) n.v_mem_inf.2 haF
    · exact setLike_mul_comm (s := e.F) hu.2 haF
    · exact hc.symm.eq
  have haxmem : Tits.parrottCommutator a f.x ∈ zpowers n.t := by
    have hh := mem_map_of_mem r.symm.toMonoidHom (core_derived_pc h hqx hu.1)
    rw [MonoidHom.map_zpowers] at hh
    change r.symm (Tits.parrottCommutator (r f.x) f.u) ∈ zpowers (r.symm z) at hh
    rw [map_pc, r.symm_apply_apply, hst] at hh
    rw [pc_swap a f.x]
    exact (zpowers n.t).inv_mem hh
  refine ⟨a, habasis, haw, hab, ?_⟩
  rw [mem_zpowers_iff_mem_range_orderOf, n.t_order] at haxmem
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp haxmem
  have hi2 : i < 2 := Finset.mem_range.mp hi
  interval_cases i
  · exact Or.inl (by simpa using heq.symm)
  · exact Or.inr (by simpa using heq.symm)

/-- All first-three-generator choices are discharged except the b,w equation.
The supplied z,t,v,F,T are retained throughout. -/
public theorem ParrottSylowActionData.exists_three_generators_of_commutator_bw
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowActionData n) (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z)
    (hbw : Tits.parrottCommutator n.b f.w = 1) :
    Nonempty (ParrottSylowThreeGeneratorData n) := by
  obtain ⟨a, haF, haw, hab, hax⟩ := f.exists_a_selection h hN
  exact f.exists_three_generators_of_ab_selection hns hN h a haF hbw haw
    (f.b_commutator_u h hN) hab hax

end Stellmacher.Recognition
