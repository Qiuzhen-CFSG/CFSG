module

public import Stellmacher.Recognition.Parrott.LocalGeneratorData
public import Stellmacher.Recognition.Parrott.SecondCentralizer
public import Theory.GroupTheory.InvolutionPairCentralInvolution

/-!
# The dihedral subgroup in Parrott's braid argument

The compatible generators r and s lie in different involution classes, so rs
has even order and its half-order power is a central involution of ⟨r,s⟩.
If rs has order ten, its fifth power belongs to the z-class (the other
centralizer has order 1536), whereas its product with r belongs to the v-class.
Transporting the proved outside-core fusion in the second centralizer then
places r in the actual two-core of the latter involution's centralizer.

The last lemma reduces the lower bound on the order of rs to the explicit
fourth-power word identity from the source. Noncommutation of r and y follows
from generation of the actual centralizer and its order, not from an additional
nondegeneracy assumption. The word identity and the order alternatives remain
separate obligations; no eighth-power relation is asserted here.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§6, printed p.684, Verification of VI(i).
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private def centralizerConj (g x : G) :
    centralizer ({x} : Set G) ≃* centralizer ({g * x * g⁻¹} : Set G) := by
  let a := MulAut.conj g
  have hm : (centralizer ({x} : Set G)).map a.toMonoidHom =
      centralizer ({a x} : Set G) := by
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
        map_centralizer_le_centralizer_image ({x} : Set G) a.toMonoidHom
    · intro y hy
      refine ⟨a.symm y, ?_, a.apply_symm_apply y⟩
      apply mem_centralizer_singleton_iff.mpr
      apply a.injective
      simpa only [map_mul, a.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy
  exact (a.subgroupMap _).trans (MulEquiv.subgroupCongr hm)

/-- In a centralizer from the v-class, an involution from the z-class lies
in the actual two-core. This transports the supplied second-centralizer fusion. -/
public theorem ParrottSecondCentralizerData.conjugate_core_mem
    (c : ParrottSecondCentralizerData n)
    {q r : G} (hq : IsConj n.v q) (hr : orderOf r = 2)
    (hrz : IsConj r z) (hcomm : Commute r q) :
    r ∈ (pCore 2 (centralizer ({q} : Set G))).map
      (centralizer ({q} : Set G)).subtype := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hq
  let E := centralizerConj g n.v
  let R : centralizer ({g * n.v * g⁻¹} : Set G) :=
    ⟨r, mem_centralizer_singleton_iff.mpr hcomm.eq⟩
  let R' := E.symm R
  have himage : g * (R' : G) * g⁻¹ = r := by
    change (E R' : G) = r
    rw [show E R' = R from E.apply_symm_apply R]
  have hconj : IsConj (R' : G) r := isConj_iff.mpr ⟨g, himage⟩
  have horder : orderOf (R' : G) = 2 := by
    rw [← himage] at hr
    exact ((MulAut.conj g).orderOf_eq (R' : G)).symm.trans hr
  have hcore : R' ∈ pCore 2 (centralizer ({n.v} : Set G)) := by
    by_contra hout
    have hout' : (R' : G) ∉ (pCore 2 (centralizer ({n.v} : Set G))).map
        (centralizer ({n.v} : Set G)).subtype := by
      rintro ⟨u, hu, heq⟩
      exact hout ((Subtype.ext heq : u = R') ▸ hu)
    have hv := c.outside_core_fusion (R' : G) R'.property horder hout'
    exact n.not_isConj (hv.trans (hconj.trans hrz)).symm
  have hcoreR : R ∈ pCore 2 (centralizer ({g * n.v * g⁻¹} : Set G)) := by
    rw [← pCore_map_iso 2 E]
    exact ⟨R', hcore, E.apply_symm_apply R⟩
  exact mem_map_of_mem _ hcoreR

end Stellmacher.Recognition

namespace Stellmacher.Recognition.ParrottNormalizerGeneratorData
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)
include k

/-- The compatible generators belong to distinct ambient involution classes. -/
public theorem braid_not_isConj : ¬ IsConj f.r k.s := by
  intro hrs
  exact n.not_isConj (f.r_conjugate.symm.trans (hrs.trans k.s_conjugate))

variable [Finite G]

/-- The canonical half-order power is an involution centralizing both generators. -/
public theorem braid_central_involution :
    let i := (f.r * k.s) ^ (orderOf (f.r * k.s) / 2)
    i ∈ zpowers f.r ⊔ zpowers k.s ∧ orderOf i = 2 ∧
      Commute i f.r ∧ Commute i k.s :=
  Theory.GroupTheory.half_order_involution_of_not_isConj
    f.r k.s f.r_order k.s_order k.braid_not_isConj

/-- The product of these nonconjugate involutions has even order. -/
public theorem braid_order_even : Even (orderOf (f.r * k.s)) := by
  apply even_iff_two_dvd.mpr
  have hi := k.braid_central_involution
  have hd := orderOf_pow_dvd (x := f.r * k.s) (orderOf (f.r * k.s) / 2)
  rw [hi.2.1] at hd
  exact hd

/-- Under order ten, the canonical central involution is the fifth power. -/
public theorem braid_ten_central_involution (horder : orderOf (f.r * k.s) = 10) :
    orderOf ((f.r * k.s) ^ 5) = 2 ∧
      Commute ((f.r * k.s) ^ 5) f.r ∧ Commute ((f.r * k.s) ^ 5) k.s := by
  simpa only [horder, show 10 / 2 = 5 by decide] using k.braid_central_involution.2

omit [Finite G] in
/-- A dihedral conjugation identifies the fifth-power reflection with the s-class. -/
public theorem braid_fifth_reflection_conjugate : IsConj k.s ((f.r * k.s) ^ 5 * f.r) := by
  have hr : f.r⁻¹ = f.r := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.eq20_r)
  have hs : k.s⁻¹ = k.s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using k.s_sq)
  have hss : k.s * k.s = 1 := by simpa only [pow_two] using k.s_sq
  have hinvert : SemiconjBy k.s (f.r * k.s)⁻¹ (f.r * k.s) := by
    change k.s * (f.r * k.s)⁻¹ = (f.r * k.s) * k.s
    rw [mul_inv_rev, hr, hs, ← mul_assoc, hss, one_mul, mul_assoc, hss, mul_one]
  apply isConj_iff.mpr
  refine ⟨(f.r * k.s) ^ 3, ?_⟩
  calc
    (f.r * k.s) ^ 3 * k.s * ((f.r * k.s) ^ 3)⁻¹ =
        (f.r * k.s) ^ 3 * ((f.r * k.s) ^ 3 * k.s) := by
      rw [mul_assoc, ← inv_pow, (hinvert.pow_right 3).eq]
    _ = (f.r * k.s) ^ 6 * k.s := by rw [← mul_assoc, ← pow_add]
    _ = (f.r * k.s) ^ 5 * f.r := by
      rw [pow_succ, mul_assoc, mul_assoc, hss, mul_one]

/-- The reflection ir lies in the v-class and centralizes r. -/
public theorem braid_ten_reflection (horder : orderOf (f.r * k.s) = 10) :
    let q := (f.r * k.s) ^ 5 * f.r
    orderOf q = 2 ∧ IsConj n.v q ∧ Commute f.r q := by
  have hi := k.braid_ten_central_involution horder
  have hc := k.braid_fifth_reflection_conjugate
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  refine ⟨?_, k.s_conjugate.symm.trans hc, hi.2.1.symm.mul_right (Commute.refl _)⟩
  rw [← hg]
  exact ((MulAut.conj g).orderOf_eq k.s).trans k.s_order


/-- In the order-ten branch, r lies in O₂(C_G(ir)) for i=(rs)⁵. -/
public theorem braid_ten_core_mem (c : ParrottSecondCentralizerData n)
    (horder : orderOf (f.r * k.s) = 10) :
    let q := (f.r * k.s) ^ 5 * f.r
    f.r ∈ (pCore 2 (centralizer ({q} : Set G))).map
      (centralizer ({q} : Set G)).subtype := by
  have hq := k.braid_ten_reflection horder
  exact c.conjugate_core_mem hq.2.1 f.r_order f.r_conjugate hq.2.2

/-- A fifth-order rotation cannot lie in the order-1536 second centralizer,
so the central involution in the order-ten branch is conjugate to z. -/
public theorem braid_ten_fifth_conjugate (c : ParrottSecondCentralizerData n)
    (horder : orderOf (f.r * k.s) = 10) : IsConj z ((f.r * k.s) ^ 5) := by
  have hi := k.braid_ten_central_involution horder
  rcases n.involution_classes _ hi.1 with hz | hv
  · exact hz
  · exfalso
    have hcard : Nat.card (centralizer ({(f.r * k.s) ^ 5} : Set G)) = 1536 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hv
      rw [← hg, ← Nat.card_congr (centralizerConj g n.v).toEquiv]
      exact c.card
    have hp : f.r * k.s ∈ centralizer ({(f.r * k.s) ^ 5} : Set G) :=
      mem_centralizer_singleton_iff.mpr (Commute.self_pow (f.r * k.s) 5).eq
    have hd := (centralizer ({(f.r * k.s) ^ 5} : Set G)).orderOf_dvd_natCard hp
    rw [hcard, horder] at hd
    norm_num at hd

omit k in
/-- The generator extending the order-2048 Sylow subgroup to the
order-10240 centralizer cannot already belong to that Sylow subgroup. -/
public theorem braid_r_not_mem_sylow (f : ParrottCentralizerGeneratorData n)
    (h : ParrottCentralizerHypotheses z) :
    f.r ∉ (e.sylow : Subgroup G) := by
  intro hr
  have hH : centralizer ({z} : Set G) = (e.sylow : Subgroup G) := by
    rw [← f.centralizer_generators, sup_eq_left]
    exact zpowers_le.mpr hr
  have hcard := (h.card_and_solvable z).1
  rw [hH, e.sylow_card h] at hcard
  norm_num at hcard

omit k in
/-- The source fifth-power relation and actual generation imply ryr ≠ y. -/
public theorem braid_ryr_ne_y (f : ParrottCentralizerGeneratorData n)
    (h : ParrottCentralizerHypotheses z) :
    f.r * f.y * f.r ≠ f.y := by
  intro heq
  have hry2 : (f.r * f.y) ^ 2 = 1 := by
    calc
      (f.r * f.y) ^ 2 = (f.r * f.y * f.r) * f.y := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [heq, ← pow_two, f.y_sq]
  have ho : orderOf (f.r * f.y) = 1 := by
    have h2 := orderOf_dvd_of_pow_eq_one hry2
    have h5 := orderOf_dvd_of_pow_eq_one f.eq20_ry
    have hd := Nat.dvd_gcd h2 h5
    norm_num at hd
    exact orderOf_eq_one_iff.mpr hd
  have hry := orderOf_eq_one_iff.mp ho
  have hry' : f.r = f.y := by
    have hi := eq_inv_iff_mul_eq_one.mpr hry
    rw [inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.y_sq)] at hi
    exact hi
  exact braid_r_not_mem_sylow f h (hry' ▸ f.toParrottSylowGeneratorData.local_mem_sylow.2.2.2.2.2.2.2.2.2.2)

/-- The fourth-power word identity excludes the even orders two and four. -/
public theorem braid_order_ge_six_of_fourth_conjugation
    (h : ParrottCentralizerHypotheses z)
    (hword : (f.r * k.s) ^ 4 * f.y * (k.s * f.r) ^ 4 = f.r * f.y * f.r) :
    6 ≤ orderOf (f.r * k.s) := by
  by_contra hlt
  have hpos := orderOf_pos (f.r * k.s)
  have heven := k.braid_order_even
  have hn : orderOf (f.r * k.s) = 2 ∨ orderOf (f.r * k.s) = 4 := by
    obtain ⟨m, hm⟩ := heven
    omega
  have hd : orderOf (f.r * k.s) ∣ 4 := by rcases hn with hn | hn <;> simp [hn]
  have hp := orderOf_dvd_iff_pow_eq_one.mp hd
  have hp' : (k.s * f.r) ^ 4 = 1 := by
    have hr : f.r⁻¹ = f.r := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.eq20_r)
    have hs : k.s⁻¹ = k.s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using k.s_sq)
    simpa only [← inv_pow, mul_inv_rev, hr, hs, inv_one] using congrArg Inv.inv hp
  rw [hp, hp', one_mul, mul_one] at hword
  exact braid_ryr_ne_y f h hword.symm

end Stellmacher.Recognition.ParrottNormalizerGeneratorData
