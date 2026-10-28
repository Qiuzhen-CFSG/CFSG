module
public import Theory.LinearAlgebra.QuadraticForm.BinarySmallCubicCensus
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Linear
public import Theory.GroupTheory.CyclicThreeNormalizer
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.Representation.NormalInvariants

/-!
# Normal cubic subgroups on small binary symplectic modules

A normal subgroup C of order three acts without nonzero fixed points in a
faithful irreducible module. For its generator t, the form q(v)=B(v,tv) is
quadratic with polar form B and is preserved by the centralizer of C.
An odd prime subgroup of this centralizer has a proper nondegenerate fixed
space. Orbit counting on all vectors and on q=1 vectors, using the counts
0,3,6,36, forces that prime to be three. Burnside's two-prime theorem makes
the centralizer solvable, and its index at most two finishes the argument.

This proves just the solvability needed for the cubic G.9.4 rows in the
original symplectic context of G.11.5. No full linear or unitary normalizer
recognition is needed. Source: Aschbacher--Smith, printed pp.354--355,365.
-/

public section
open Module Representation


namespace Representation.SmallSymplecticNormalThree
open Subgroup
variable {G C V : Type*} [Group G] [Finite G] [Group C] [Finite C]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

@[instance_reducible] private def pointsAction (ρ : Representation (ZMod 2) G V)
    (Q : QuadraticForm (ZMod 2) V) (hi : ∀ g v, Q (ρ g v) = Q v) :
    MulAction G {v : V // Q v = 1} where
  smul g v := ⟨ρ g v, (hi g v).trans v.property⟩
  one_smul v := Subtype.ext (LinearMap.congr_fun ρ.map_one v)
  mul_smul g h v := Subtype.ext (LinearMap.congr_fun (ρ.map_mul g h) v)

omit [Finite G] in
private theorem points_modEq (ρ : Representation (ZMod 2) G V)
    (Q : QuadraticForm (ZMod 2) V) (hi : ∀ g v, Q (ρ g v) = Q v)
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G) :
    Nat.card {v : V // Q v = 1} ≡
      Nat.card {v : ρ.invariants // Q v = 1} [MOD p] := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := pointsAction ρ Q hi
  let e : MulAction.fixedPoints G {v : V // Q v = 1} ≃
      {v : ρ.invariants // Q v = 1} := {
    toFun := fun v => ⟨⟨v.val.val, fun g => congrArg Subtype.val (v.property g)⟩, v.val.property⟩
    invFun := fun v => ⟨⟨v.val.val,v.property⟩, fun g => Subtype.ext (v.val.property g)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hm := hp.card_modEq_card_fixedPoints {v : V // Q v = 1}
  rwa [Nat.card_congr e] at hm

omit [Finite C] in
private theorem points_three_dvd (τ : Representation (ZMod 2) C V)
    (hC : Nat.card C = 3) (ht : τ.invariants = ⊥)
    (Q : QuadraticForm (ZMod 2) V) (hi : ∀ c v, Q (τ c v) = Q v) :
    3 ∣ Nat.card {v : V // Q v = 1} := by
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hm := points_modEq τ Q hi hp
  have : IsEmpty {v : τ.invariants // Q v = 1} := ⟨fun v => by
    have hv : (v.val : V) = 0 := by simpa only [ht, Submodule.mem_bot] using v.val.property
    have he := v.property
    rw [hv,Q.map_zero] at he
    exact zero_ne_one he⟩
  have hz : Nat.card {v : τ.invariants // Q v = 1} = 0 := Nat.card_of_isEmpty
  rw [hz] at hm
  exact Nat.modEq_zero_iff_dvd.mp hm

omit [Finite G] in
private theorem vectors_modEq (ρ : Representation (ZMod 2) G V)
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G) :
    2 ^ finrank (ZMod 2) V ≡ 2 ^ finrank (ZMod 2) ρ.invariants [MOD p] := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : MulAction G V := {
    smul g v := ρ g v
    one_smul v := LinearMap.congr_fun ρ.map_one v
    mul_smul g h v := LinearMap.congr_fun (ρ.map_mul g h) v }
  have hm := hp.card_modEq_card_fixedPoints V
  have he : MulAction.fixedPoints G V ≃ ρ.invariants := {
    toFun := fun v => ⟨v.val,v.property⟩
    invFun := fun v => ⟨v.val,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr he, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ρ.invariants), Nat.card_zmod] at hm
  exact hm

private noncomputable def commutingRestriction (ρ : Representation (ZMod 2) G V)
    (τ : Representation (ZMod 2) C V)
    (hc : ∀ g c, Commute (ρ g) (τ c)) : Representation (ZMod 2) C ρ.invariants where
  toFun c := (τ c).restrict (fun v hv g => by
    change ρ g (τ c v) = τ c v
    rw [← Module.End.mul_apply, (hc g c).eq, Module.End.mul_apply, hv g])
  map_one' := by ext v; exact LinearMap.congr_fun τ.map_one v
  map_mul' c d := by ext v; exact LinearMap.congr_fun (τ.map_mul c d) v

omit [Finite G] [Finite C] [FiniteDimensional (ZMod 2) V] in
private theorem commutingRestriction_invariants (ρ : Representation (ZMod 2) G V)
    (τ : Representation (ZMod 2) C V)
    (hc : ∀ g c, Commute (ρ g) (τ c)) (ht : τ.invariants = ⊥) :
    (commutingRestriction ρ τ hc).invariants = ⊥ := by
  apply bot_unique
  intro v hv
  have he : (v : V) ∈ τ.invariants := fun c => congrArg Subtype.val (hv c)
  rw [ht,Submodule.mem_bot] at he
  exact Subtype.ext he

omit [Finite C] in
/-- A commuting cubic symmetry and the quadratic census exclude odd primes other than three. -/
private theorem prime_eq_three (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hG : Nat.card G = p)
    (τ : Representation (ZMod 2) C V) (hC : Nat.card C = 3)
    (ht : τ.invariants = ⊥) (hc : ∀ g c, Commute (ρ g) (τ c))
    (Q : QuadraticForm (ZMod 2) V)
    (ha : Q.polarBilin.IsAlt) (hn : Q.polarBilin.Nondegenerate)
    (hi : ∀ g v, Q (ρ g v) = Q v) (hj : ∀ c v, Q (τ c v) = Q v)
    (hd : finrank (ZMod 2) V ≤ 6) : p = 3 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype G := Fintype.ofFinite G
  have hnz : (Fintype.card G : ZMod 2) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card,hG]
    intro hz
    have hh := (ZMod.natCast_eq_zero_iff p 2).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hh).symm
  let : Invertible (Fintype.card G : ZMod 2) := invertibleOfNonzero hnz
  have hpl : 2 ≤ p := hp.two_le
  have hpG : IsPGroup p G := IsPGroup.of_card (n := 1) (by simpa using hG)
  have hpolar (g : G) (u v : V) : Q.polarBilin (ρ g u) (ρ g v) = Q.polarBilin u v := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hi]
  have hnd := SymplecticConjugatePair.OddOrder.invariants_nondegenerate ρ Q.polarBilin ha hn hpolar
  let R := Q.comp ρ.invariants.subtype
  have hR : R.polarBilin = LinearMap.BilinForm.restrict Q.polarBilin ρ.invariants := by
    rw [QuadraticMap.polarBilin_comp]
    rfl
  have hRa : R.polarBilin.IsAlt := by
    intro v
    exact ha v
  have hRn : R.polarBilin.Nondegenerate := hR.symm ▸ hnd
  let σ := commutingRestriction ρ τ hc
  have hs : σ.invariants = ⊥ := commutingRestriction_invariants ρ τ hc ht
  have hsQ (c : C) (v : ρ.invariants) : R (σ c v) = R v := hj c v
  have hproper : ρ.invariants ≠ ⊤ := by
    intro he
    have htr (g : G) : g = 1 := by
      apply hf
      ext v
      have hv : v ∈ ρ.invariants := he ▸ Submodule.mem_top
      simpa using hv g
    have hone := Nat.card_eq_one_iff_exists.mpr ⟨1,htr⟩
    exact hp.ne_one (hG.symm.trans hone)
  have hlt : finrank (ZMod 2) ρ.invariants < finrank (ZMod 2) V :=
    Submodule.finrank_lt hproper
  have he := SymplecticConjugatePair.OddOrder.even_finrank_of_nondegenerate Q.polarBilin ha hn
  have hRe := SymplecticConjugatePair.OddOrder.even_finrank_of_nondegenerate R.polarBilin hRa hRn
  have hcases := QuadraticForm.BinarySmall.nonsingular_card_cases Q hn hd he (points_three_dvd τ hC ht Q hj)
  have hRcases := QuadraticForm.BinarySmall.nonsingular_card_cases R hRn (by omega) hRe
    (points_three_dvd σ hC hs R hsQ)
  have hV := vectors_modEq ρ hpG
  have hQ := points_modEq ρ Q hi hpG
  change Nat.card {v : V // Q v = 1} ≡ Nat.card {v : ρ.invariants // R v = 1} [MOD p] at hQ
  rcases hcases with ⟨h0,c0⟩ | ⟨h2,c2⟩ | ⟨h4,c4⟩ | ⟨h6,c6⟩ <;>
    rcases hRcases with ⟨r0,d0⟩ | ⟨r2,d2⟩ | ⟨r4,d4⟩ | ⟨r6,d6⟩ <;>
    simp only [*] at hV hQ <;> try omega
  all_goals
    have hvd := hV.symm.dvd'
    have hqd := hQ.symm.dvd'
    have hgd := Nat.dvd_gcd hvd hqd
    norm_num at hgd
    have hle : p ≤ 9 := (Nat.le_of_dvd (by norm_num) hgd).trans (by norm_num)
    interval_cases p <;> solve | rfl | norm_num at hp | norm_num at hp2 | norm_num at hgd
end Representation.SmallSymplecticNormalThree

namespace Representation.SmallSymplecticNormalThree
open Subgroup
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (B : LinearMap.BilinForm (ZMod 2) V)
  (ha : B.IsAlt) (hn : B.Nondegenerate)
  (hi : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
  (C : Subgroup G) (hC : Nat.card C = 3)
  (ht : Representation.invariants (ρ.comp C.subtype) = ⊥)

omit [FiniteDimensional (ZMod 2) V] in
include hC ht in
private theorem cubic_polynomial (t : G) (htC : t ∈ C) (ht1 : t ≠ 1) :
    ∀ v, ρ t (ρ t v) + ρ t v = v := by
  obtain ⟨he,hpow⟩ := cyclicThree_generator C hC t htC ht1
  have hcube : ∀ v, ρ t (ρ t (ρ t v)) = v := by
    intro v
    have hh : ρ t ^ 3 = 1 := by rw [← map_pow,hpow,map_one]
    simpa only [pow_succ,pow_zero,one_mul,Module.End.mul_apply,Module.End.one_apply] using
      LinearMap.congr_fun hh v
  intro v
  have hfixed : ρ t (ρ t (ρ t v) + ρ t v + v) = ρ t (ρ t v) + ρ t v + v := by
    rw [map_add,map_add,hcube]
    abel
  have hh : ρ t (ρ t v) + ρ t v + v ∈ Representation.invariants (ρ.comp C.subtype) := by
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
      (ρ := ρ.comp C.subtype) (g := (⟨t,htC⟩ : C)) (fun c => mem_zpowers_of_prime_card hC (by
        exact fun e => ht1 (congrArg Subtype.val e))) ]
    exact hfixed
  rw [ht,Submodule.mem_bot] at hh
  have hneg : -(v) = v := by
    rw [← neg_one_smul (ZMod 2),show (-1 : ZMod 2) = 1 by decide,one_smul]
  exact (eq_neg_of_add_eq_zero_left hh).trans hneg

private noncomputable def cubicForm (t : G) : QuadraticForm (ZMod 2) V :=
  LinearMap.BilinMap.toQuadraticMap (B.compl₂ (ρ t))

omit [FiniteDimensional (ZMod 2) V] in
include ha hi hC ht in
private theorem cubicForm_polar (t : G) (htC : t ∈ C) (ht1 : t ≠ 1) :
    (cubicForm ρ B t).polarBilin = B := by
  ext u v
  rw [cubicForm,LinearMap.BilinMap.polarBilin_toQuadraticMap]
  change B u (ρ t v) + B v (ρ t u) = B u v
  have hsym : ∀ u v, B u v = B v u := by
    intro u v
    have hh := ha.neg_eq u v
    have hneg : -(B u v) = B u v := by
      rw [← neg_one_smul (ZMod 2),show (-1 : ZMod 2) = 1 by decide,one_smul]
    exact hneg.symm.trans hh
  rw [hsym v (ρ t u)]
  have htv : B (ρ t u) v = B u (ρ t (ρ t v)) := by
    have h := hi t u (ρ t (ρ t v))
    have hcube : ρ t (ρ t (ρ t v)) = v := by
      obtain ⟨_,hp⟩ := cyclicThree_generator C hC t htC ht1
      have hh : ρ t ^ 3 = 1 := by rw [← map_pow,hp,map_one]
      simpa [pow_succ,Module.End.mul_apply] using LinearMap.congr_fun hh v
    rwa [hcube] at h
  rw [htv,← map_add,add_comm (ρ t v),cubic_polynomial ρ C hC ht t htC ht1]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hi in
private theorem cubicForm_preserves (t : G) (g : G) (hg : Commute g t) (v : V) :
    cubicForm ρ B t (ρ g v) = cubicForm ρ B t v := by
  change B (ρ g v) (ρ t (ρ g v)) = B v (ρ t v)
  have hc : ρ t (ρ g v) = ρ g (ρ t v) := by
    rw [← Module.End.mul_apply,← Module.End.mul_apply,← map_mul,← map_mul,hg.eq]
  rw [hc,hi]
end Representation.SmallSymplecticNormalThree

namespace Representation.SmallSymplecticNormalThree
open Subgroup
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A faithful irreducible symplectic binary action of degree at most six with
normal cubic subgroup is solvable. -/
theorem isSolvable_of_normal_cubic
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    [Representation.IsIrreducible ρ]
    (B : LinearMap.BilinForm (ZMod 2) V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hi : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hd : finrank (ZMod 2) V ≤ 6)
    (C : Subgroup G) [C.Normal] (hC : Nat.card C = 3) : Group.IsSolvable G := by
  let : IsCyclic C := isCyclic_of_prime_card hC
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t,ht1⟩ := exists_ne (1 : C)
  have ht : Representation.invariants (ρ.comp C.subtype) = ⊥ := by
    by_contra he
    have hk := le_ker_of_normal_invariants_ne_bot ρ C he
    have ht' : (t : G) = 1 := hf ((hk t.property).trans ρ.map_one.symm)
    exact ht1 (Subtype.ext ht')
  let Q := cubicForm ρ B (t : G)
  have hpolar : Q.polarBilin = B := cubicForm_polar ρ B ha hi C hC ht t t.property
    (fun he => ht1 (Subtype.ext he))
  have hQ (g : G) (hg : g ∈ centralizer (C : Set G)) (v : V) : Q (ρ g v) = Q v :=
    cubicForm_preserves ρ B hi (t : G) g
      (show Commute g (t : G) from ((mem_centralizer_iff.mp hg) t t.property).symm) v
  have hCQ (c : C) (v : V) : Q (ρ c v) = Q v :=
    hQ c (by intro x hx; exact congrArg Subtype.val (mul_comm' (⟨x,hx⟩ : C) c)) v
  let D := centralizer (C : Set G)
  let : Group.IsSolvable D := by
    apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hpd
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    right
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨a,ha'⟩ := exists_prime_orderOf_dvd_card' (G := D) p hpd
    let A := zpowers a
    let f := D.subtype.comp A.subtype
    have hfi : Function.Injective f := D.subtype_injective.comp A.subtype_injective
    let σ := ρ.comp f
    apply prime_eq_three σ (hf.comp hfi) hp hp2
      ((Nat.card_zpowers a).trans ha') (ρ.comp C.subtype) hC ht _ Q
      (hpolar.symm ▸ ha) (hpolar.symm ▸ hn) _ hCQ hd
    · intro g c
      change Commute (ρ ((g.val : D) : G)) (ρ (c : G))
      apply Commute.map
      exact ((mem_centralizer_iff.mp g.val.property) c c.property).symm
    · intro g v
      exact hQ _ g.val.property v
  have hAut : Nat.card (MulAut C) = 2 := by rw [IsCyclic.card_mulAut,hC]; decide
  let f : G →* MulAut C := MulAut.conjNormal
  have hiD : D.index ≤ 2 := by
    change (centralizer (C : Set G)).index ≤ 2
    rw [← MulAut.conjNormal_ker_eq_centralizer C,Subgroup.index_ker]
    exact hAut ▸ f.range.card_le_card_group
  exact D.isSolvable_of_index_le_four (by omega)
end Representation.SmallSymplecticNormalThree
