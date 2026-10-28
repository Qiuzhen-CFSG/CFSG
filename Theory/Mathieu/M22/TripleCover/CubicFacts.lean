module

public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.Mathieu.M22.TripleCoverLocalRank

/-!
# Cubic torsion in the actual Mathieu triple cover

The native hexad embeds A₆ in M₂₂. Its inverse image in a cubic central
cover has order 1080 and contains a Sylow three-subgroup of the full
cover. Every element killed by nine therefore transfers to this central
A₆ extension, where the proved cubic calculation kills its cube.
Perfect central descent also bounds the actual outer automorphism group
by two; the embedded A₆ supplies three-rank at least two.

These are the precise model facts for the order-three containment in
A.3.18 consumed by the small-cover step of 13.8.21(2). The argument is
abstract until its final specialization, avoiding repeated reductions of
the binary matrix carrier. Its ATLAS construction and attribution remain
in the imported TripleCover module.
Source: Aschbacher–Smith, A.3.18 and 13.8.21(2), printed pp.51–52,956.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22TripleCover

theorem cube_eq_one_of_ninth_of_central_quotient
    {E : Type*} [Group E] [Finite E]
    (e0 : (E ⧸ center E) ≃* M22) (hcenter : Nat.card (center E) = 3)
    {x : E} (hx : x ^ 9 = 1) : x ^ 3 = 1 := by
  let f := e0.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e0.surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hkf : f.ker = center E := by
    ext x
    change e0 (QuotientGroup.mk' (center E) x) = 1 ↔ _
    rw [e0.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨P,q,hq,hqc,hqk⟩ := CubicCoverPreimage.exists_restriction
    f hf hkf.le hexadAlternatingSixEmbedding hexadAlternatingSixEmbedding_injective
  have hk : Nat.card q.ker = 3 := hqk.trans (hkf ▸ hcenter)
  have hPcard : Nat.card P = 1080 := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv,hk,
      nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  let T : Sylow 3 P := default
  let Q := (T : Subgroup P).map P.subtype
  have hQcard : Nat.card Q = 27 := by
    rw [card_map_of_injective P.subtype_injective,Sylow.card_eq_multiplicity,hPcard]
    decide +kernel
  have hQp : IsPGroup 3 Q := T.isPGroup'.map P.subtype
  let S : Sylow 3 E := hQp.toSylow (by
    have hh := Q.card_mul_index
    have hEcard : Nat.card E = 1330560 := by
      have hc := (center E).card_mul_index
      rw [hcenter,Subgroup.index_eq_card,Nat.card_congr e0.toEquiv,m22_order] at hc
      omega
    rw [hQcard,hEcard] at hh
    have hi : Q.index = 49280 := by omega
    rw [hi]
    decide)
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨T',hT'⟩ := hp.exists_le_sylow
  let y : T' := ⟨x,hT' (mem_zpowers x)⟩
  let e := T'.equiv S
  let z : P := ⟨e y,map_subtype_le _ (e y).property⟩
  have hz9 : z ^ 9 = 1 := by
    apply Subtype.ext
    exact congrArg (fun t : S => (t : E)) (show e y ^ 9 = 1 from by
      rw [←map_pow,show y ^ 9 = 1 from Subtype.ext hx,map_one])
  have hz3 := GLS3.Chapter5.OddCentralCovers.central_six_cube_eq_one_of_ninth q hq hqc hk z hz9
  have hy3 : y ^ 3 = 1 := e.injective (by
    rw [map_pow,map_one]
    exact Subtype.ext (congrArg (fun t : P => (t : E)) hz3))
  exact congrArg Subtype.val hy3

theorem cube_eq_one_of_ninth {x : M22TripleCover} (hx : x ^ 9 = 1) : x ^ 3 = 1 :=
  cube_eq_one_of_ninth_of_central_quotient centralQuotientEquiv center_card hx

theorem outer_two : IsPGroup 2 (MulAut.Outer M22TripleCover) := by
  apply IsPGroup.of_card_dvd_pow (n := 1)
  exact (card_dvd_of_injective (MulAut.centralQuotientOuter centralQuotientEquiv)
    (MulAut.centralQuotientOuter_injective centralQuotientEquiv)).trans
      ScalarAutomorphisms.m22_outer_card_dvd_two

theorem two_le_threeRank : 2 ≤ primeRank 3 M22TripleCover :=
  (triple_cover_twoLocalThreeRank_ge_two centralQuotientEquiv center_card).trans
    (twoLocalPrimeRank_le_primeRank 3)

end Sporadic.Mathieu.M22TripleCover
