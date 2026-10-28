module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Disjoint conjugate kernels in a two-group

Let D be normal in R inside a finite two-group P, and let y normalize R,
lie outside R, and have square in R. The intersection D ∩ D^y is normalized
by R⟨y⟩, since y exchanges its two factors. If every involution in D has
centralizer in P of order at most |R|, a nontrivial intersection would contain
a central involution of R⟨y⟩, contradicting that bound. Thus the intersection
is trivial.

When R/D is elementary abelian, conjugation followed by the quotient map
embeds D in R/D. Consequently D is elementary abelian too. The final lemma
rules out an involution which is a product of a commuting element of D and
an element of order four. These statements supply the maximality, quotient,
and lifting steps of the source; they do not construct its exceptional covers.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.3.6, printed p.1179 / PDF p.1196.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- Conjugation embeds a kernel disjoint from its conjugate into the
elementary quotient, so the kernel is elementary. -/
public theorem elementary_of_disjoint_conjugate (R : Subgroup G) (D : Subgroup R) [D.Normal]
    (y : G) (hy : y ∈ normalizer (R : Set G))
    (hdis : Disjoint (D.map R.subtype)
      ((D.map R.subtype).map (MulAut.conj y).toMonoidHom))
    [IsElementaryAbelian 2 (R ⧸ D)] : IsElementaryAbelian 2 D := by
  let a : MulAut R := R.normalizerMonoidHom ⟨y, hy⟩
  let f : D →* R ⧸ D := (QuotientGroup.mk' D).comp (a.toMonoidHom.comp D.subtype)
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply (eq_bot_iff_forall _).mpr
    intro d hd
    have hd' : a (d : R) ∈ D := (QuotientGroup.eq_one_iff _).mp hd
    have hval : y * ((d : R) : G) * y⁻¹ = 1 := disjoint_def.mp hdis
      (show y * ((d : R) : G) * y⁻¹ ∈ D.map R.subtype from ⟨a d, hd', rfl⟩)
      ⟨d, ⟨d, d.property, rfl⟩, rfl⟩
    apply Subtype.ext
    apply a.injective
    change a (d : R) = a 1
    rw [map_one]
    exact Subtype.ext hval
  refine {
    toIsMulCommutative := isMulCommutative_iff.mpr (fun d e => hinj ?_)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun d => hinj ?_) }
  · simp only [map_mul]
    exact (isMulCommutative_iff.mp (inferInstance : IsMulCommutative (R ⧸ D))) _ _
  · rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ D)) (f d)

/-- A product of commuting elements with square one cannot acquire an
order-four factor while the other factor has square one. -/
public theorem no_order_four_factor {r f e : G} (hcomm : Commute r f)
    (he : e = r * f) (he2 : e ^ 2 = 1) (hr2 : r ^ 2 = 1)
    (hf : orderOf f = 4) : False := by
  have hf2 : f ^ 2 = 1 := by
    simpa only [he, hcomm.mul_pow, hr2, one_mul] using he2
  have hd := orderOf_dvd_of_pow_eq_one hf2
  rw [hf] at hd
  norm_num at hd

variable [Finite G]

/-- The nontrivial intersection of two conjugate kernels would supply an
involution with a strictly larger centralizer. -/
public theorem disjoint_conjugate_of_maximal_centralizer
    (P R D : Subgroup G) (hP : IsPGroup 2 P) (hRP : R ≤ P) (hDR : D ≤ R)
    (hDn : R ≤ normalizer (D : Set G)) (y : G) (hyP : y ∈ P)
    (hyR : y ∈ normalizer (R : Set G)) (hyout : y ∉ R) (hy2 : y ^ 2 ∈ R)
    (hmax : ∀ j : G, j ∈ D → orderOf j = 2 →
      Nat.card (P ⊓ centralizer ({j} : Set G) : Subgroup G) ≤ Nat.card R) :
    Disjoint D (D.map (MulAut.conj y).toMonoidHom) := by
  let f := (MulAut.conj y).toMonoidHom
  let X := D ⊓ D.map f
  let J := R ⊔ zpowers y
  have hJ : J ≤ P := sup_le hRP (zpowers_le.mpr hyP)
  have hXJ : X ≤ J := inf_le_left.trans (hDR.trans le_sup_left)
  have hyD2 : (D.map f).map f = D := by
    rw [map_map]
    have he : f.comp f = (MulAut.conj (y ^ 2)).toMonoidHom := by
      ext x
      simp [f, MulAut.conj_apply, pow_two, mul_assoc]
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp (hDn hy2)
  have hyX : y ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (D ⊓ D.map f).map f = D ⊓ D.map f
    rw [map_inf _ _ f (MulAut.conj y).injective, hyD2, inf_comm]
  have hRnD' : R ≤ normalizer (D.map f : Set G) := by
    have hyReq : R.map f = R := mem_normalizer_iff_map_conj_eq.mp hyR
    rw [← hyReq]
    exact (map_mono hDn).trans (le_normalizer_map f)
  have hJnX : J ≤ normalizer (X : Set G) :=
    sup_le ((le_inf hDn hRnD').trans inf_normalizer_le_normalizer_inf) (zpowers_le.mpr hyX)
  by_contra hdis
  have hne : X ≠ ⊥ := by
    exact fun h => hdis (disjoint_iff.mpr h)
  let XJ := X.subgroupOf J
  let : XJ.Normal := (normal_subgroupOf_iff_le_normalizer hXJ).mpr hJnX
  let : Nontrivial XJ := by
    have : Nontrivial X := (nontrivial_iff_ne_bot _).mpr hne
    exact (subgroupOfEquivOfLe hXJ).toEquiv.nontrivial
  have hpJ : IsPGroup 2 J := hP.to_le hJ
  let : Fact (IsPGroup 2 J) := ⟨hpJ⟩
  obtain ⟨Z, _, hZX, hZcard, hZcentral⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) XJ inferInstance
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (hZcard ▸ dvd_rfl)
  have hjG : orderOf ((j : J) : G) = 2 := by simpa only [orderOf_coe] using hj
  have hcent : J ≤ centralizer ({((j : J) : G)} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp (hZcentral j.property) ⟨x, hx⟩))
  have hRJ : R < J := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hyJ : y ∈ J := (le_sup_right : zpowers y ≤ J) (mem_zpowers y)
    rw [← heq] at hyJ
    exact hyout hyJ
  have hlt : Nat.card R < Nat.card J := lt_of_not_ge (fun h =>
    hRJ.ne (eq_of_le_of_card_ge hRJ.le h))
  have hle : Nat.card J ≤ Nat.card R :=
    (card_le_of_le (le_inf hJ hcent)).trans (hmax _ (hZX j.property).1 hjG)
  exact (not_lt_of_ge hle) hlt

end Subgroup
