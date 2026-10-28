module

public import Stellmacher.Recognition.Parrott.CosetSelection
public import Theory.GroupAction.FiveFourInvolutionFiveOrbit

/-!
# The single core-involution coset fixed by an outer involution

Put H=C_G(z), J=O₂(H), and D=J′. Every nonzero D-coset containing an
involution has an orbit of length five. If the involution also commutes
with an outer involution y, its coset is fixed by yJ. The faithful
five-four action on J/D has only one such nonidentity fixed vector.
Thus any two core involutions outside D commuting with y differ by D.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.674, Lemma 4 on p.675, and the omega calculation on p.676.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- Core involutions commuting with an outer involution occupy at most one
nonzero coset of the actual derived core. -/
public theorem parrott_outer_core_involutions_single_coset
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let DH := (commutator J).map J.subtype
    ∀ y : H, orderOf y = 2 → y ∉ J →
      ∀ a b : H, a ∈ J → b ∈ J → a ^ 2 = 1 → b ^ 2 = 1 →
        Commute a y → Commute b y → a ∉ DH → b ∉ DH → a⁻¹ * b ∈ DH := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let V := J ⧸ D
  let qJ := QuotientGroup.mk' J
  let qD := QuotientGroup.mk' D
  change ∀ y : H, orderOf y = 2 → y ∉ J → _
  intro y hy hyJ a b haJ hbJ ha2 hb2 hay hby haD hbD
  obtain ⟨f, hf, heval⟩ := parrott_core_quotient_action z h
  obtain ⟨hElem, hVcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 V := hElem
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let fM : M →* MulAut V := f.comp e.symm.toMonoidHom
  have hfM : Function.Injective fM := hf.comp e.symm.injective
  let u : M := e (qJ y)
  have hu : orderOf u = 2 := by
    rw [e.orderOf_eq]
    apply orderOf_eq_prime
    · rw [← map_pow, show y ^ 2 = 1 from hy ▸ pow_orderOf_eq_one y, map_one]
    · exact fun hh => hyJ ((QuotientGroup.eq_one_iff y).mp hh)
  have horbit (x : H) (hxJ : x ∈ J) (hx2 : x ^ 2 = 1) (hxD : x ∉ DH) :
      (Set.range (fun g => fM g (qD ⟨x, hxJ⟩))).ncard = 5 := by
    let xJ : J := ⟨x, hxJ⟩
    have hxorder : orderOf x = 2 := orderOf_eq_prime hx2
      (fun hh => hxD (hh ▸ DH.one_mem))
    have hi := parrott_core_involution_coset_centralizer_index z h x hxJ hxorder hxD
    have hc := centralizer_index_eq_subgroup_quotient_orbit_card J D f heval xJ
    have hcard : (Set.range (fun g => f g (qD xJ))).ncard = 5 := hc.symm.trans hi
    have hrange : Set.range (fun g => fM g (qD xJ)) =
        Set.range (fun g => f g (qD xJ)) := by
      ext v
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨e.symm g, rfl⟩
      · rintro ⟨g, rfl⟩
        refine ⟨e g, ?_⟩
        change f (e.symm (e g)) (qD xJ) = _
        rw [e.symm_apply_apply]
    change (Set.range (fun g => fM g (qD xJ))).ncard = 5
    rw [hrange]
    exact hcard
  have hfixed (x : H) (hxJ : x ∈ J) (hxy : Commute x y) :
      fM u (qD ⟨x, hxJ⟩) = qD ⟨x, hxJ⟩ := by
    let xJ : J := ⟨x, hxJ⟩
    have hh := heval y xJ xJ (mul_inv_eq_iff_eq_mul.mpr hxy.symm.eq).symm
    simpa only [fM, u, qJ, qD, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply] using hh
  let aJ : J := ⟨a, haJ⟩
  let bJ : J := ⟨b, hbJ⟩
  have haV : qD aJ ≠ 1 := fun hh => haD
    (mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff aJ).mp hh))
  have hbV : qD bJ ≠ 1 := fun hh => hbD
    (mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff bJ).mp hh))
  have heq := Theory.GroupAction.five_four_involution_fixed_five_orbit_unique
    hVcard φ hφ fM hfM u hu (qD aJ) (qD bJ) haV hbV
    (horbit a haJ ha2 haD) (horbit b hbJ hb2 hbD)
    (hfixed a haJ hay) (hfixed b hbJ hby)
  have hmem : aJ⁻¹ * bJ ∈ D := (QuotientGroup.eq_one_iff _).mp (by
    change qD (aJ⁻¹ * bJ) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel])
  exact mem_map_of_mem J.subtype hmem

end Stellmacher.Recognition
