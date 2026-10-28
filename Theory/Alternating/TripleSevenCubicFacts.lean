module
public import Theory.Alternating.TripleSevenLocalRank
public import Theory.Alternating.SevenQuasisimpleExtension
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.Alternating.PrimeRank
/-!
# Cubic torsion and outer automorphisms of the triple A₇ cover

Restrict the literal triple cover to the standard A₆ subgroup. Its central
preimage has index seven and contains a Sylow three-subgroup. The already
proved exponent-three theorem for arbitrary central cubic extensions of
A₆ therefore excludes order nine throughout the triple A₇ cover. Perfect
central descent embeds its outer group in Out(A₇), a two-group; its
surjective A₇ image also forces three-rank at least two.

These are exactly the component facts needed for A.3.18 containment in the
raw seven-point row of original15.3.21. Source: GLS3 5.2.3(d);
Aschbacher–Smith A.3.18,15.3.17–21, pp.51–52,1126–1127.
-/

public section
open Subgroup Theory.GroupTheory
namespace GLS3.Chapter5.OddCentralCovers

theorem tripleSeven_cube_eq_one_of_ninth {x : TripleSeven} (hx : x ^ 9 = 1) : x ^ 3 = 1 := by
  let f := tripleSevenCovering.toMonoidHom
  obtain ⟨P,q,hq,hqc,hqk⟩ := CubicCoverPreimage.exists_restriction f
    tripleSevenCovering.surjective tripleSevenCovering.ker_le_center sixToSeven sixToSeven_injective
  have hk : Nat.card q.ker = 3 := hqk.trans tripleSevenCovering_kernel_card
  have hPcard : Nat.card P = 1080 := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv,hk,
      nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  have hGcard : Nat.card TripleSeven = 7560 := by
    rw [f.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f tripleSevenCovering.surjective).toEquiv,
      show Nat.card f.ker = 3 from tripleSevenCovering_kernel_card,
      nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  let T : Sylow 3 P := default
  let Q := (T : Subgroup P).map P.subtype
  have hQcard : Nat.card Q = 27 := by
    rw [card_map_of_injective P.subtype_injective,Sylow.card_eq_multiplicity,hPcard]
    decide +kernel
  have hQp : IsPGroup 3 Q := T.isPGroup'.map P.subtype
  let S : Sylow 3 TripleSeven := hQp.toSylow (by
    have hh := Q.card_mul_index
    rw [hQcard,hGcard] at hh
    have hi : Q.index = 280 := by omega
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
    exact congrArg (fun t : S => (t : TripleSeven)) (show e y ^ 9 = 1 from by
      rw [←map_pow,show y ^ 9 = 1 from Subtype.ext hx,map_one])
  have hz3 := central_six_cube_eq_one_of_ninth q hq hqc hk z hz9
  have hy3 : y ^ 3 = 1 := e.injective (by
    rw [map_pow,map_one]
    exact Subtype.ext (congrArg (fun t : P => (t : TripleSeven)) hz3))
  exact congrArg Subtype.val hy3
theorem tripleSeven_outer_two : IsPGroup 2 (MulAut.Outer TripleSeven) := by
  have ho : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 7))) := by
    let A := alternatingGroup (Fin 7)
    have hcard : Nat.card (Equiv.Perm (Fin 7) ⧸ A) = 2 ^ 1 := by
      rw [← A.index_eq_card]
      exact alternatingGroup.index_eq_two
    apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
    obtain ⟨σ,rfl⟩ :=
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide)).surjective a
    exact ⟨QuotientGroup.mk' A σ,rfl⟩
  exact ho.of_injective (MulAut.centralQuotientOuter tripleSevenQuotientCenterEquiv)
    (MulAut.centralQuotientOuter_injective tripleSevenQuotientCenterEquiv)

theorem tripleSeven_two_le_threeRank : 2 ≤ primeRank 3 TripleSeven := by
  by_contra hh
  let P : Sylow 3 TripleSeven := default
  have hc : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)
  have hr := P.primeRank_le_one_of_surjective hc tripleSevenProjection tripleSevenProjection_surjective
  rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3 Nat.prime_three (by decide)] at hr
  omega
end GLS3.Chapter5.OddCentralCovers
