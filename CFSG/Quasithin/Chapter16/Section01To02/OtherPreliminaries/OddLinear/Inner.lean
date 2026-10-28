module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.PSL2Even
public import GorensteinWalter.PSL2Center
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Inner involution centralizers in Fermat–Mersenne PSL₂

The torus calculation proves that each involution centralizer is a two-group.
A central involution of a Sylow subgroup therefore has that Sylow subgroup
as its whole centralizer. Involution fusion carries this equality to every
involution. Triviality of the PSL₂ center detects the order of an inner
automorphism's conjugating element.

This proves the inner case of Aschbacher–Smith 16.1.5(2), printed p.1171,
and also includes the small parameters five and seven. The outer case is
not asserted. The input centralizer calculation is the independent matrix
lemma in `MainConverse.OddClassicalLocal.PSL2Even`.
-/

public section

open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.OddLinear

/-- Each involution centralizer is a Sylow two-subgroup in the actual model. -/
theorem pslTwo_involution_centralizer_sylow {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hF : Nat.card F = p) (hp : CFSG.Quasithin.IsFermatOrMersennePrime p)
    (hp5 : 5 ≤ p) (z : PSL(2,F)) (hz : orderOf z = 2) :
    ∃ S : Sylow 2 PSL(2,F), (S : Subgroup _) = centralizer ({z} : Set _) := by
  have ho : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp.1, hp.1.odd_of_ne_two (by omega), by omega, by simpa using hF⟩
  let S : Sylow 2 PSL(2,F) := Classical.choice Sylow.nonempty
  obtain ⟨m, hm, ⟨eS⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F ho S
  let : Nontrivial S := eS.toEquiv.nontrivial
  let : Nontrivial (center S) := S.isPGroup'.center_nontrivial
  have hcd : 2 ∣ Nat.card (center S) :=
    (S.isPGroup'.to_subgroup (center S)).card_eq_or_dvd.resolve_left
      (ne_of_gt Finite.one_lt_card)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2 hcd
  let tG : PSL(2,F) := (t : S)
  have htG : orderOf tG = 2 :=
    (Subgroup.orderOf_coe (t : S)).trans ((Subgroup.orderOf_coe t).trans ht)
  have hSt : (S : Subgroup _) ≤ centralizer ({tG} : Set _) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp t.property ⟨x, hx⟩))
  have hC := CFSG.Quasithin.MainConverse.psl2_fermatMersenne_involution_centralizer_isPGroup
    F hF hp hp5 tG htG
  have hEq : centralizer ({tG} : Set _) = (S : Subgroup _) :=
    S.is_maximal' hC hSt
  have hzne : z ≠ 1 := by intro h; simp [h] at hz
  have htne : tG ≠ 1 := by intro h; simp [h] at htG
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F ho tG z
    ⟨htne, by simpa [htG] using pow_orderOf_eq_one tG⟩
    ⟨hzne, by simpa [hz] using pow_orderOf_eq_one z⟩
  let e : MulAut PSL(2,F) := MulAut.conj g
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup PSL(2,F)).map e.toMonoidHom = centralizer ({z} : Set _)
  rw [← hEq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e y * z = z * e y
    have h := congrArg e (mem_centralizer_singleton_iff.mp hy)
    change e tG = z at hg
    simpa only [map_mul, hg] using h
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    change e tG = z at hg
    simpa only [map_mul, hg, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

/-- The fixed subgroup of every inner involutory automorphism is an actual
Sylow two-subgroup, with no replacement by an abstract isomorphic group. -/
theorem pslTwo_inner_involution {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hF : Nat.card F = p) (hp : IsFermatOrMersennePrime p) (hp5 : 5 ≤ p)
    (r : MulAut PSL(2,F)) (hr : orderOf r = 2)
    (hi : ∃ g : PSL(2,F), r = MulAut.conj g) :
    ∃ S : Sylow 2 PSL(2,F), (S : Subgroup _) = r.fixedSubgroup := by
  obtain ⟨g, rfl⟩ := hi
  have hg : orderOf g = 2 :=
    (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot (psl2_center_eq_bot F)) g).symm.trans hr
  simpa only [MulAut.fixedSubgroup_conj] using
    pslTwo_involution_centralizer_sylow hF hp hp5 g hg

/-- These inner fixed subgroups are solvable, as needed to exclude them
from the component-bearing centralizers in 16.1.7. -/
theorem pslTwo_inner_involution_solvable {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hF : Nat.card F = p) (hp : IsFermatOrMersennePrime p) (hp5 : 5 ≤ p)
    (r : MulAut PSL(2,F)) (hr : orderOf r = 2)
    (hi : ∃ g : PSL(2,F), r = MulAut.conj g) : Group.IsSolvable r.fixedSubgroup := by
  obtain ⟨S, hS⟩ := pslTwo_inner_involution hF hp hp5 r hr hi
  have htwo : IsPGroup 2 r.fixedSubgroup := hS ▸ S.isPGroup'
  let : Group.IsNilpotent r.fixedSubgroup := htwo.isNilpotent
  infer_instance

end CFSG.Quasithin.Chapter16.OtherPreliminaries.OddLinear
