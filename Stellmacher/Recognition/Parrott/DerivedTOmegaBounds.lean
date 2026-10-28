module

public import Stellmacher.Recognition.Parrott.ElementaryJoin
public import Stellmacher.Recognition.Parrott.DerivedTDisplacement
public import Stellmacher.Recognition.Parrott.DerivedTQuotient
public import Theory.GroupAction.FiveFourInvolutionFiveOrbit

/-!
# The derived omega bounds for the first centralizer

For C=C_T(t) of order 1024, the displacement calculation gives E∩F≤C′.
The image of C′ in J/J′ is fixed by the square of an order-four actor.
Every nonzero coset containing an involution has orbit size five; uniqueness
of such a square-fixed coset identifies it with the supplied coset aE.
Consequently every square-one element of C′ lies in E∨F.

Since F is elementary abelian, the lower bound lifts to Ω₁(C′), and
its square-one generators give the upper bound. All subgroups are the
actual ambient images; no characteristic geometry is assumed.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the last two paragraphs of p.676.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] {z : G}

/-- Transfer the two local derived calculations to the actual ambient
image of the omega subgroup. -/
public theorem derived_t_omega_bounds_of_local_calculations
    (d : ParrottSecondElementaryData z) (C : Subgroup G) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let W := (omega₁ (commutator C) (p := 2)).map
      (C.subtype.comp (commutator C).subtype)
    E ⊓ d.F ≤ (commutator C).map C.subtype →
    (∀ x ∈ (commutator C).map C.subtype, x ^ 2 = 1 → x ∈ E ⊔ d.F) →
    E ⊓ d.F ≤ W ∧ W ≤ E ⊔ d.F := by
  intro H J E W hlow hupp
  let : IsElementaryAbelian 2 d.F := d.elementary
  constructor
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := hlow hx
    let b : commutator C := ⟨c, hc⟩
    have hb : b ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (c : G) hx.2
    have hbmem : b ∈ omega₁ (commutator C) (p := 2) :=
      subset_closure (by simpa only [Set.mem_ofPred_eq, pow_one] using hb)
    exact mem_map_of_mem (C.subtype.comp (commutator C).subtype) hbmem
  · change (omega₁ (commutator C) (p := 2)).map
      (C.subtype.comp (commutator C).subtype) ≤ E ⊔ d.F
    rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    intro b hb
    have hb2 : b ^ 2 = 1 := by simpa only [Set.mem_ofPred_eq, pow_one] using hb
    apply hupp ((b : C) : G) (mem_map_of_mem C.subtype b.property)
    simpa only [map_pow, map_one, MonoidHom.comp_apply, Subgroup.coe_subtype] using
      congrArg (C.subtype.comp (commutator C).subtype) hb2

private theorem sylow_fixes_chosen_coset
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let q := QuotientGroup.mk' (commutator J)
    ∀ f : (H ⧸ J) →* MulAut (J ⧸ commutator J),
      (∀ (a : H) (b b' : J), (b' : H) = a * (b : H) * a⁻¹ →
        f (QuotientGroup.mk' J a) (q b) = q b') →
      ∀ y : H, (y : G) ∈ (d.sylow : Subgroup G) →
        f (QuotientGroup.mk' J y) (q ⟨d.a, d.a_mem_core⟩) = q ⟨d.a, d.a_mem_core⟩ := by
  intro H J q f heval y hy
  let D := commutator J
  let DH := D.map J.subtype
  let E := D.map (H.subtype.comp J.subtype)
  let FH := zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))
  have hDH : DH.map H.subtype = E := map_map _ _ _
  have hfixed : (DH ⊓ centralizer ({d.a} : Set H)).map H.subtype =
      E ⊓ centralizer ({(d.a : G)} : Set G) := by
    apply le_antisymm
    · rintro b ⟨c, hc, rfl⟩
      exact ⟨hDH ▸ mem_map_of_mem H.subtype hc.1,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp hc.2))⟩
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := hDH.symm ▸ hb.1
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hb.2))
  have hFHmap : FH.map H.subtype = d.F := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hfixed]
    exact d.fixed_join.symm
  have hFH : d.F.subgroupOf H = FH := by
    rw [← hFHmap]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hFHle : d.F ≤ H := d.le_sylow.trans (by rw [d.sylow_map]; exact map_subtype_le _)
  have hyN : y ∈ normalizer (FH : Set H) := by
    rw [← hFH, ← subgroupOf_normalizer_eq hFHle]
    exact d.sylow_le_normalizer hy
  let : IsElementaryAbelian 2 D := (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  rw [elementary_involution_fixed_join_normalizer DH d.a d.a_order d.a_not_mem_derived] at hyN
  let qH := QuotientGroup.mk' DH
  have hycomm : qH y * qH d.a = qH d.a * qH y := mem_centralizer_singleton_iff.mp hyN
  let aJ : J := ⟨d.a, d.a_mem_core⟩
  let b : J := ⟨y * (aJ : H) * y⁻¹,
    Subgroup.Normal.conj_mem (inferInstance : J.Normal) aJ aJ.property y⟩
  have hb : qH (b : H) = qH (aJ : H) := by
    change qH (y * d.a * y⁻¹) = qH d.a
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
    exact hycomm
  have hbq : q b = q aJ := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨c, hc, hcb⟩ := QuotientGroup.eq_iff_div_mem.mp hb
    exact (show c = b / aJ from Subtype.ext hcb) ▸ hc
  exact (heval y aJ b rfl).trans hbq

/-- Every square-one element of the first centralizer's derived subgroup lies in E∨F. -/
public theorem t_centralizer_commutator_involution_mem_join
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let i := H.subtype.comp J.subtype
    let E := (commutator J).map i
    ∀ t ∈ E, t ∉ zpowers z →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      Nat.card C = 1024 →
        ∀ x ∈ (commutator C).map C.subtype, x ^ 2 = 1 → x ∈ E ⊔ d.F := by
  intro H J i E t ht htz C hC x hx hx2
  classical
  by_cases hxE : x ∈ E
  · exact mem_sup_left hxE
  have hxK := d.sylow_subgroup_commutator_le_core h C inf_le_left hx
  obtain ⟨xH, hxJ, rfl⟩ := hxK
  let b : J := ⟨xH, hxJ⟩
  let D := commutator J
  let DH := D.map J.subtype
  let q := QuotientGroup.mk' D
  let V := J ⧸ D
  obtain ⟨f, hf, heval⟩ := parrott_core_quotient_action z h
  obtain ⟨hElem, hVcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 V := hElem
  obtain ⟨y, hy, hyorder, hfixed⟩ :=
    d.t_centralizer_derived_quotient_square_fixed h t ht htz hC f hf heval
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let fM : M →* MulAut V := f.comp e.symm.toMonoidHom
  have hfM : Function.Injective fM := hf.comp e.symm.injective
  let u : M := e ((QuotientGroup.mk' J y) ^ 2)
  have hu : orderOf u = 2 := by
    rw [e.orderOf_eq, orderOf_pow, hyorder]
    decide
  have horbit (c : J) (hc2 : c ^ 2 = 1) (hcD : c ∉ D) :
      (Set.range (fun g => fM g (q c))).ncard = 5 := by
    have hcH : (c : H) ∉ DH := by
      rintro ⟨v, hv, hvc⟩
      exact hcD ((show v = c from Subtype.ext hvc) ▸ hv)
    have hcorder : orderOf (c : H) = 2 := orderOf_eq_prime
      (by exact congrArg J.subtype hc2) (fun hh => hcH (hh ▸ DH.one_mem))
    have hi := parrott_core_involution_coset_centralizer_index z h c c.property hcorder hcH
    have hc := centralizer_index_eq_subgroup_quotient_orbit_card J D f heval c
    have hrange : Set.range (fun g => fM g (q c)) = Set.range (fun g => f g (q c)) := by
      ext v
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨e.symm g, rfl⟩
      · rintro ⟨g, rfl⟩
        refine ⟨e g, ?_⟩
        change f (e.symm (e g)) (q c) = _
        rw [e.symm_apply_apply]
    rw [hrange]
    exact hc.symm.trans hi
  let aJ : J := ⟨d.a, d.a_mem_core⟩
  have haD : aJ ∉ D := fun hh => d.a_not_mem_derived (mem_map_of_mem J.subtype hh)
  have hbD : b ∉ D := fun hh => hxE (mem_map_of_mem i hh)
  have ha2 : aJ ^ 2 = 1 := Subtype.ext (d.a_order ▸ pow_orderOf_eq_one d.a)
  have hb2 : b ^ 2 = 1 := Subtype.ext (Subtype.ext hx2)
  have haV : q aJ ≠ 1 := fun hh => haD ((QuotientGroup.eq_one_iff aJ).mp hh)
  have hbV : q b ≠ 1 := fun hh => hbD ((QuotientGroup.eq_one_iff b).mp hh)
  have hfu (w : V) : fM u w = f (QuotientGroup.mk' J y) (f (QuotientGroup.mk' J y) w) := by
    change f (e.symm (e ((QuotientGroup.mk' J y) ^ 2))) w = _
    rw [e.symm_apply_apply, map_pow, pow_two, MulAut.mul_apply]
  have hay := d.sylow_fixes_chosen_coset h f heval y hy.1
  have hau : fM u (q aJ) = q aJ := by
    rw [hfu, hay, hay]
  have hbu : fM u (q b) = q b := by
    rw [hfu]
    exact hfixed b hx
  have heq := Theory.GroupAction.five_four_involution_fixed_five_orbit_unique
    hVcard φ hφ fM hfM u hu (q aJ) (q b) haV hbV
    (horbit aJ ha2 haD) (horbit b hb2 hbD) hau hbu
  have hdiff : aJ⁻¹ * b ∈ D := (QuotientGroup.eq_one_iff _).mp (by
    change q (aJ⁻¹ * b) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel])
  have haF : (d.a : G) ∈ d.F := by
    rw [d.fixed_join]
    exact mem_sup_left (mem_zpowers _)
  have hdif : i (aJ⁻¹ * b) ∈ E ⊔ d.F := mem_sup_left (mem_map_of_mem i hdiff)
  have hh := (E ⊔ d.F).mul_mem (mem_sup_right haF) hdif
  simpa only [map_mul, map_inv, i, MonoidHom.comp_apply, Subgroup.coe_subtype,
    aJ, b, mul_inv_cancel_left] using hh

/-- The actual derived omega subgroup lies between E∩F and E∨F.
Only the local order-1024 hypothesis is needed, in addition to t∈E∖⟨z⟩. -/
public theorem derived_t_omega_bounds [Finite G]
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E, t ∉ zpowers z →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      Nat.card C = 1024 →
      let W := (omega₁ (commutator C) (p := 2)).map
        (C.subtype.comp (commutator C).subtype)
      E ⊓ d.F ≤ W ∧ W ≤ E ⊔ d.F := by
  intro H J E t ht htz C hC W
  exact d.derived_t_omega_bounds_of_local_calculations C
    (d.elementary_inf_le_t_centralizer_commutator h t ht htz hC)
    (d.t_centralizer_commutator_involution_mem_join h t ht htz hC)

end Stellmacher.Recognition.ParrottSecondElementaryData
