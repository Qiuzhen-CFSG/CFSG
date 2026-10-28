module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Control
public import Mathlib.GroupTheory.Transfer

/-!
# The literal four-group and normal odd complement in the middle quotient

For the local elementary sixteen A, the image of T/A in N_G(A)/A has
order four and exponent two. Its normalizer is itself: pull normalizers
back along the quotient map and use the already proved equality N_K(T)=T.
The normalizer-index congruence makes it Sylow. Burnside transfer then
constructs a normal odd complement, of index four, in this literal quotient.

Source: M. Aschbacher, “A 2-local characterization of M12”, Lemma 3.1,
Illinois J. Math. 47 (2003), printed pp.36–37. These conclusions use the
explicit MiddleLocalData and do not construct that local data.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace MiddleLocalData
variable (m : MiddleLocalData z)

abbrev NormalizerQuotient := normalizer (m.A : Set G) ⧸
  m.A.subgroupOf (normalizer (m.A : Set G))

abbrev normalizerSylowSubgroup : Subgroup (normalizer (m.A : Set G)) :=
  (middleSylowImage m.S).subgroupOf (normalizer (m.A : Set G))

abbrev normalizerFour : Subgroup m.NormalizerQuotient :=
  m.normalizerSylowSubgroup.map
    (QuotientGroup.mk' (m.A.subgroupOf (normalizer (m.A : Set G))))

theorem normalizerSylowSubgroup_card (h : Hypotheses z) :
    Nat.card m.normalizerSylowSubgroup = 64 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe m.sylow_le_normalizer).toEquiv,
    card_map_of_injective (Centralizer z).subtype_injective,
    h.centralizer_sylow_two_card]

theorem normalizerSylowSubgroup_self_normalizing (h : Hypotheses z) :
    normalizer (m.normalizerSylowSubgroup : Set (normalizer (m.A : Set G))) =
      m.normalizerSylowSubgroup := by
  rw [← subgroupOf_normalizer_eq m.sylow_le_normalizer]
  ext x
  change (x : G) ∈ normalizer (middleSylowImage m.S : Set G) ↔
    (x : G) ∈ middleSylowImage m.S
  constructor
  · intro hx
    exact m.normalizer_sylow_intersection h ▸ ⟨x.property, hx⟩
  · intro hx
    exact (middleSylowImage m.S).le_normalizer hx

omit [Finite G] in
private theorem quotient_kernel_le_sylow :
    (QuotientGroup.mk' (m.A.subgroupOf (normalizer (m.A : Set G)))).ker ≤
      m.normalizerSylowSubgroup := by
  rw [QuotientGroup.ker_mk']
  exact fun _ hx => m.A_le_sylow hx

theorem normalizerFour_card (h : Hypotheses z) : Nat.card m.normalizerFour = 4 := by
  let K := normalizer (m.A : Set G)
  let V := m.A.subgroupOf K
  let U := m.normalizerSylowSubgroup
  let f := (QuotientGroup.mk' V).comp U.subtype
  have hr : f.range = m.normalizerFour := by
    rw [MonoidHom.range_comp, range_subtype]
  have hk : f.ker = V.subgroupOf U := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hVU : V ≤ U := fun _ hx => m.A_le_sylow hx
  have hc : Nat.card f.ker = 16 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe m.A.le_normalizer).toEquiv, m.card]
  have he := f.ker.card_mul_index
  rw [index_ker, hc, hr, m.normalizerSylowSubgroup_card h] at he
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16) he

omit [Finite G] in
theorem normalizerFour_square (x : m.normalizerFour) : x ^ 2 = 1 := by
  obtain ⟨t, ht, he⟩ := x.property
  apply Subtype.ext
  change (x : m.NormalizerQuotient) ^ 2 = 1
  rw [← he, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact m.sylow_square t ht

omit [Finite G] in
theorem normalizerFour_elementary : IsElementaryAbelian 2 m.normalizerFour where
  toIsMulCommutative := ⟨⟨fun a b =>
    (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one
      (m.normalizerFour_square x)) a b).eq⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr m.normalizerFour_square

theorem normalizerFour_self_normalizing (h : Hypotheses z) :
    normalizer (m.normalizerFour : Set m.NormalizerQuotient) = m.normalizerFour := by
  let q := QuotientGroup.mk' (m.A.subgroupOf (normalizer (m.A : Set G)))
  have hs : Function.Surjective q := QuotientGroup.mk'_surjective _
  apply (comap_injective hs)
  rw [comap_normalizer_eq_of_surjective _ hs]
  have hc : m.normalizerFour.comap q = m.normalizerSylowSubgroup :=
    comap_map_eq_self m.quotient_kernel_le_sylow
  rw [hc, m.normalizerSylowSubgroup_self_normalizing h]

noncomputable def normalizerQuotientSylow (h : Hypotheses z) : Sylow 2 m.NormalizerQuotient :=
  (IsPGroup.of_card (p := 2) (n := 2) (m.normalizerFour_card h)).toSylow (by
    have hc := Sylow.card_quotient_normalizer_modEq_card_quotient
      (p := 2) (n := 2) (m.normalizerFour_card h)
    have hnorm := m.normalizerFour_self_normalizing h
    have hi : Nat.card (normalizer (m.normalizerFour : Set m.NormalizerQuotient) ⧸
        m.normalizerFour.comap (normalizer (m.normalizerFour : Set m.NormalizerQuotient)).subtype) = 1 := by
      rw [hnorm]
      simp
    rw [hi] at hc
    intro hd
    have := (hc.dvd_iff (dvd_refl 2)).mpr hd
    norm_num at this)

theorem normalizerQuotientSylow_central (h : Hypotheses z) :
    normalizer (m.normalizerQuotientSylow h : Set m.NormalizerQuotient) ≤
      centralizer (m.normalizerQuotientSylow h : Set m.NormalizerQuotient) := by
  change normalizer (m.normalizerFour : Set m.NormalizerQuotient) ≤ _
  rw [m.normalizerFour_self_normalizing h]
  let : IsElementaryAbelian 2 m.normalizerFour := m.normalizerFour_elementary
  exact m.normalizerFour.le_centralizer

/-- Burnside's kernel is a normal complement to the literal image of T/A. -/
theorem exists_normalizer_odd_complement (h : Hypotheses z) :
    ∃ J : Subgroup m.NormalizerQuotient, J.Normal ∧
      J.IsComplement' m.normalizerFour ∧
      Nat.card J * 4 = Nat.card m.NormalizerQuotient ∧ Odd (Nat.card J) := by
  let P := m.normalizerQuotientSylow h
  let f := MonoidHom.transferSylow P (m.normalizerQuotientSylow_central h)
  have hc : f.ker.IsComplement' m.normalizerFour :=
    MonoidHom.ker_transferSylow_isComplement' P (m.normalizerQuotientSylow_central h)
  refine ⟨f.ker, inferInstance, hc, ?_, ?_⟩
  · simpa only [m.normalizerFour_card h] using hc.card_mul_card
  · exact Nat.not_even_iff_odd.mp (fun he =>
      MonoidHom.not_dvd_card_ker_transferSylow P (m.normalizerQuotientSylow_central h)
        (even_iff_two_dvd.mp he))

end MiddleLocalData
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
end
