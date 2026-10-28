module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelTwelve.TorusOrbits
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
/-!
# No subnormal two-perfect subgroup of order twelve in an even-exponent PSL₃ Borel

Let q = 2ⁿ with n positive and even. If a subnormal two-perfect subgroup E
of the projective Borel had order twelve, Cauchy's theorem would supply an
element of order three. Sylow conjugacy inside the actual Borel puts it in
the projective diagonal torus, including the cubic scalar quotient.

The Borel's upper-unitriangular subgroup is its two-core. A normal two-group
normalizes every subnormal two-perfect subgroup, so the conjugated E contains
the entire unipotent orbit of its diagonal element. The matrix calculation in
`BorelTwelve.TorusOrbits` gives at least q² distinct elements in this orbit.
Since q ≥ 4, this contradicts |E| = 12. No identification with A₄, center
hypothesis, or block-exclusion premise is required.

Source: the PSL₃ Borel paragraph in the proof of Aschbacher–Smith E.6.8,
printed p.248 (combined manuscript, 1 March 2004). The relative normalization
step is the p-residual supplement argument of A.4.2(2), printed p.57.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace Matrix.PSL3.LinearThree.BorelTwelve
variable (F : Type*) [Field F] [Finite F]

private theorem unipotent_normalizes {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (E : Subgroup (borel F)) (hE : E.IsSubnormal) (hpE : IsPPerfect 2 E) :
    unipotent F ≤ normalizer (E.map (borel F).subtype) := by
  have hn := le_normalizer_of_isSubnormal_isPPerfect E (pCore 2 (borel F))
    hE hpE pCore_isPGroup (by rw [normalizer_eq_top]; exact le_top)
  rw [BorelQuotient.twoCore_eq F hF] at hn
  have hm := (map_mono hn (f := (borel F).subtype)).trans
    (le_normalizer_map (borel F).subtype)
  rwa [map_subgroupOf_eq_of_le (unipotent_le_borel F)] at hm

/-- A subnormal two-perfect Borel subgroup whose order is divisible by three
has at least q² elements. -/
theorem card_sq_le_of_three_dvd {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (E : Subgroup (borel F)) (hE : E.IsSubnormal) (hpE : IsPPerfect 2 E)
    (hthree : 3 ∣ Nat.card E) : Nat.card F ^ 2 ≤ Nat.card E := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 3 hthree
  let xG : PSL(3,F) := x.val.val
  have ho : orderOf xG = 3 :=
    (orderOf_coe x.val).trans ((orderOf_coe x).trans hx)
  have hxp : IsPGroup 3 (zpowers xG) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ho, pow_one])
  obtain ⟨g,hg,hgt⟩ := ThreeAlignment.conjugate_borel_threeSubgroup_into_torus F hF
    (zpowers xG) hxp (zpowers_le.mpr x.val.property)
  let c : MulAut (borel F) := MulAut.conj ⟨g,hg⟩
  let E' : Subgroup (borel F) := E.map c.toMonoidHom
  have hE' : E'.IsSubnormal := IsSubnormal.map c.surjective hE
  have hpE' : IsPPerfect 2 E' := hpE.of_surjective (c.subgroupMap E).toMonoidHom
    (c.subgroupMap E).surjective
  have hcard : Nat.card (E'.map (borel F).subtype) = Nat.card E := by
    exact (Nat.card_congr (equivMapOfInjective E' (borel F).subtype
      Subtype.val_injective).toEquiv).symm.trans
        (Nat.card_congr (c.subgroupMap E).toEquiv).symm
  have ht : (MulAut.conj g) xG ∈ torus F :=
    hgt (mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_zpowers xG))
  obtain ⟨d,hd⟩ := ht
  have hdE : torusMap F d ∈ E'.map (borel F).subtype := by
    rw [hd]
    exact mem_map_of_mem (borel F).subtype
      (mem_map_of_mem c.toMonoidHom x.property)
  have hd1 : torusMap F d ≠ 1 := by
    intro he
    have hx1 : xG = 1 := (MulAut.conj g).injective (hd.symm.trans (he.trans (map_one _).symm))
    rw [hx1, orderOf_one] at ho
    norm_num at ho
  have hb := card_sq_le_of_torus_mem F (E'.map (borel F).subtype)
    (unipotent_normalizes F hF E' hE' hpE') d hdE hd1
  rwa [hcard] at hb

/-- Positive even binary-field exponents rule out subnormal two-perfect
subgroups of order twelve in the actual projective Borel. -/
theorem card_ne_twelve {n : ℕ} (hn : 1 ≤ n) (heven : Even n)
    (hF : Nat.card F = 2 ^ n) (E : Subgroup (borel F))
    (hE : E.IsSubnormal) (hpE : IsPPerfect 2 E) : Nat.card E ≠ 12 := by
  intro hc
  have hb := card_sq_le_of_three_dvd F hF E hE hpE (by rw [hc]; decide)
  have hn2 : 2 ≤ n := by obtain ⟨k,hk⟩ := heven; omega
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn2
  rw [hc] at hb
  nlinarith
end Matrix.PSL3.LinearThree.BorelTwelve
