module

public import Stellmacher.Recognition.Parrott.NormalizerRootWordData
public import Stellmacher.Recognition.Parrott.CentralizerInvolutionSeed

/-!
# Uniqueness of Parrott's normalizer-core words

The words xⁱcʲbᵏq, with i,j < 4, k < 2 and q in the supplied F, have
unique parameters. The image of x has order four modulo the original core J:
x² = yz, and y lies outside J. After cancelling x, membership in C_G(u)
detects k, since c and F centralize u but [b,u] = z ≠ 1. Finally c has order
four modulo F: c² = wu and w is outside F, since [a,w] = z while a lies in F.
Cancellation then identifies q.

The proof retains the literal supplied witnesses and already works for the
Sylow frame. The centralizer-frame theorem is its direct specialization.
Counting and exhaustion remain in NormalizerRootWordData.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–682, equations (1)–(19) and the normalizer-core coordinates.
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem four_cosets (K : Subgroup G) (x t : G)
    (hx : x ∈ normalizer (K : Set G)) (ht : t ∈ normalizer (K : Set G))
    (hx4 : x ^ 4 = 1) (hx2 : x ^ 2 ∉ K)
    (i j : Fin 4) (q r : G) (hq : q ∈ K) (hr : r ∈ K)
    (heq : x ^ i.val * t * q = x ^ j.val * t * r) : i = j := by
  let N := normalizer (K : Set G)
  let D := K.subgroupOf N
  let : D.Normal := normal_subgroupOf_of_le_normalizer (le_refl N)
  let π := QuotientGroup.mk' D
  let X : N := ⟨x, hx⟩
  let T : N := ⟨t, ht⟩
  let Q : N := ⟨q, K.le_normalizer hq⟩
  let R : N := ⟨r, K.le_normalizer hr⟩
  have hQ : π Q = 1 := (QuotientGroup.eq_one_iff Q).mpr hq
  have hR : π R = 1 := (QuotientGroup.eq_one_iff R).mpr hr
  have h4 : (π X) ^ 4 = 1 := by
    rw [← map_pow]
    have hh : X ^ 4 = 1 := Subtype.ext hx4
    rw [hh, map_one]
  have h2 : (π X) ^ 2 ≠ 1 := by
    rw [← map_pow]
    exact fun hh => hx2 ((QuotientGroup.eq_one_iff (X ^ 2)).mp hh)
  have ho : orderOf (π X) = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) h4
  have hh : X ^ i.val * T * Q = X ^ j.val * T * R := Subtype.ext heq
  have hh' := congrArg π hh
  simp only [map_mul, map_pow, hQ, hR, mul_one, mul_right_cancel_iff] at hh'
  have hh'' := pow_inj_mod.mp hh'
  rw [ho, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hh''
  exact Fin.ext hh''

private theorem w_not_elementary (f : ParrottSylowGeneratorData n)
    (h : ParrottCentralizerHypotheses z) : f.w ∉ e.F := by
  intro hw
  let _ := e.elementary
  have ha : f.a ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  have hc : Commute f.a f.w := congrArg e.F.subtype
    (mul_comm (⟨f.a, ha⟩ : e.F) ⟨f.w, hw⟩)
  have hz1 : z = 1 := f.eq02_aw.symm.trans
    ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
  have hz := h.involution
  rw [hz1, orderOf_one] at hz
  norm_num at hz

/-- The supplied normalizer-core word has unique parameters, already for a
Sylow frame. No further centralizer or normalizer generators are needed. -/
public theorem ParrottSylowGeneratorData.normalizerRootWord_injective
    [Finite G] (f : ParrottSylowGeneratorData n)
    (h : ParrottCentralizerHypotheses z) : Function.Injective f.normalizerRootWord := by
  let H := centralizer ({z} : Set G)
  let J := (pCore 2 H).map H.subtype
  have hzJ : z ∈ J := e.le_core e.z_mem_inf.2
  have hx2 : f.x ^ 2 ∉ J := by
    rw [f.eq04]
    exact fun hh => f.y_not_mem_core h ((J.mul_mem_cancel_right hzJ).mp hh)
  have hHJ : H ≤ normalizer (J : Set G) := by
    have hh := le_normalizer_map (H := pCore 2 H) H.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hxN : f.x ∈ normalizer (J : Set G) :=
    hHJ (e.sylow_le_centralizer f.local_mem_sylow.2.2.2.2.2.2.2.2.2.1)
  have hbJ : f.b ∈ J := by
    change f.b ∈ (pCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype
    rw [← f.core_generators]
    exact subset_closure (by simp)
  have hcJ : f.c ∈ J := by
    change f.c ∈ (pCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype
    rw [← f.core_generators]
    exact subset_closure (by simp)
  have htail (j : Fin 4) (k : Fin 2) (q : e.F) :
      f.c ^ j.val * f.b ^ k.val * q ∈ J :=
    J.mul_mem (J.mul_mem (J.pow_mem hcJ _) (J.pow_mem hbJ _)) (e.le_core q.property)
  have huF : f.u ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  let C := centralizer ({f.u} : Set G)
  have hFC : e.F ≤ C := by
    let _ := e.elementary
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg e.F.subtype (mul_comm (⟨a, ha⟩ : e.F) ⟨f.u, huF⟩))
  have hcC : f.c ∈ C := mem_centralizer_singleton_iff.mpr
    ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq09_cu).eq
  have hbC : f.b ∉ C := by
    intro hb
    have hz1 : z = 1 := f.eq02_bu.symm.trans
      ((Tits.parrottCommutator_eq_one_iff _ _).mpr
        (mem_centralizer_singleton_iff.mp hb))
    have hz := h.involution
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  have hdetect (j : Fin 4) (k : Fin 2) (q : e.F) :
      f.c ^ j.val * f.b ^ k.val * q ∈ C ↔ k = 0 := by
    rw [C.mul_mem_cancel_right (hFC q.property), C.mul_mem_cancel_left (C.pow_mem hcC _)]
    fin_cases k <;> simp [hbC]
  have hcN : f.c ∈ normalizer (e.F : Set G) :=
    e.sylow_le_normalizer f.local_mem_sylow.2.2.2.2.2.2.2.1
  have hbN : f.b ∈ normalizer (e.F : Set G) :=
    e.sylow_le_normalizer f.local_mem_sylow.2.2.2.2.2.2.1
  have hc4 : f.c ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, f.eq13, f.comm_uw.symm.mul_pow,
      f.w_sq, f.u_sq, mul_one]
  have hc2 : f.c ^ 2 ∉ e.F := by
    rw [f.eq13]
    exact fun hh => w_not_elementary f h ((e.F.mul_mem_cancel_right huF).mp hh)
  rintro ⟨i, j, k, q⟩ ⟨i', j', k', q'⟩ heq
  change f.x ^ i.val * f.c ^ j.val * f.b ^ k.val * q =
    f.x ^ i'.val * f.c ^ j'.val * f.b ^ k'.val * q' at heq
  have hii : i = i' := four_cosets J f.x 1 hxN (one_mem _) f.eq01_x hx2
    i i' _ _ (htail j k q) (htail j' k' q') (by simpa only [mul_one, mul_assoc] using heq)
  subst i'
  have heq' : f.c ^ j.val * f.b ^ k.val * q =
      f.c ^ j'.val * f.b ^ k'.val * q' := by
    apply mul_left_cancel (a := f.x ^ i.val)
    simpa only [mul_assoc] using heq
  have hkk : k = k' := by
    have hh : k = 0 ↔ k' = 0 := by
      rw [← hdetect j k q, ← hdetect j' k' q', heq']
    fin_cases k <;> fin_cases k' <;> simp_all
  subst k'
  have hjj : j = j' := four_cosets e.F f.c (f.b ^ k.val) hcN
    ((normalizer (e.F : Set G)).pow_mem hbN _) hc4 hc2 j j' q q'
    q.property q'.property heq'
  subst j'
  have hqq : q = q' := Subtype.ext (mul_left_cancel heq')
  subst q'
  rfl

/-- Uniqueness for the exact Sylow frame underlying the supplied centralizer
frame; none of its coordinates or elementary witnesses are replaced. -/
public theorem ParrottCentralizerGeneratorData.normalizerRootWord_injective
    [Finite G] (f : ParrottCentralizerGeneratorData n)
    (h : ParrottCentralizerHypotheses z) :
    Function.Injective f.toParrottSylowGeneratorData.normalizerRootWord :=
  f.toParrottSylowGeneratorData.normalizerRootWord_injective h

end Stellmacher.Recognition
