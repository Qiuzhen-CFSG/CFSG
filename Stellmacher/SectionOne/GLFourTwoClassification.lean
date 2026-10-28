module

public import Stellmacher.SectionOne.Defs
public import Theory.Frattini.CoprimeAction
public import Theory.GroupAction.Quadratic
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupAction.NoCyclicNineOnSixteen
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

/-!
# The `GL₄(2)` endpoint in Stellmacher's Lemma (1.3)

This module proves the finite-linear classification used in the first two cases of
Stellmacher's proof of Lemma (1.3).  A faithful action on an elementary abelian group
of order `2⁴` embeds the normal odd `p`-subgroup `F` in `GL₄(2)`, whose order restricts
`|F|` to `3`, `9`, `5`, or `7`.  The order-seven case is ruled out by the fixed-point
congruence for a `7`-group.  If a group of order nine were cyclic, its unique subgroup
of order three would make the complement of its fixed set into a free `F`-set;
Burnside's lemma and the divisors of `16` give a contradiction. This source-neutral
exclusion is imported from `Theory.GroupAction.NoCyclicNineOnSixteen`.

For the fixed-space calculation, conjugation by the given involution is a
fixed-point-free involution on the abelian group `F`, hence inversion.  The norm over
`F` vanishes because `[V,F]=V`; pairing inverse elements in that norm shows
`C_V(x) ≤ [V,x]`.  The reverse containment follows in characteristic two, and the
kernel-range count for `v ↦ v⁻¹(xv)` forces `|C_V(x)|=4`.  Finally, the noncyclic
group of order nine is viewed as a two-dimensional `ZMod 3` vector space, yielding
the displayed equivalence with `C₃ × C₃`.

Source: `refs/latex/stellmacher-n-group.tex`, proof of Lemma (1.3), first two cases
(journal pp. 15--16).
-/

open scoped BigOperators IsMulCommutative

@[expose] public section

namespace Stellmacher.SectionOne

universe u v

private abbrev F2 := ZMod 2
private abbrev GL4 := Matrix.GeneralLinearGroup (Fin 4) F2

private theorem gl4_pgroup_card_cases
    {H : Type*} [Group H] [Finite H]
    (p : ℕ) [Fact p.Prime]
    (hpH : IsPGroup p H) (hH : Nontrivial H)
    (hodd : Nat.Coprime 2 (Nat.card H))
    (f : H →* GL4) (hf : Function.Injective f) :
    Nat.card H = 3 ∨ Nat.card H = 9 ∨
      Nat.card H = 5 ∨ Nat.card H = 7 := by
  have hdiv : Nat.card H ∣ 20160 := by
    rw [← show Nat.card GL4 = 20160 by
      rw [Matrix.card_GL_field]
      decide]
    exact Subgroup.card_dvd_of_injective f hf
  obtain ⟨n, hn⟩ := hpH.exists_card_eq
  have hnpos : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    have hcardone : Nat.card H = 1 := by simpa using hn
    exact not_nontrivial_iff_subsingleton.mpr
      (Nat.card_eq_one_iff_unique.mp hcardone).1 hH
  have hpdvdcard : p ∣ Nat.card H := by
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  have hpdvd : p ∣ 20160 := hpdvdcard.trans hdiv
  have hp : Nat.Prime p := Fact.out
  have hpCases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    have hfactor : 20160 = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num
    rw [hfactor] at hpdvd
    rcases hp.dvd_mul.mp hpdvd with h235 | h7
    · rcases hp.dvd_mul.mp h235 with h23 | h5
      · rcases hp.dvd_mul.mp h23 with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
            (hp.dvd_of_dvd_pow h2))
        · exact Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
              (hp.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h5)))
    · exact Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h7)))
  rcases hpCases with rfl | rfl | rfl | rfl
  · exfalso
    have hcop : Nat.Coprime 2 (2 ^ n) := by simpa [hn] using hodd
    have hcop' : Nat.Coprime 2 2 :=
      hcop.coprime_dvd_right (dvd_pow_self 2 hnpos.ne')
    norm_num at hcop'
  · have hnle : n ≤ 2 := by
      by_contra hnnot
      have h27 : 3 ^ 3 ∣ 3 ^ n := Nat.pow_dvd_pow 3 (by omega)
      have hpown : 3 ^ n ∣ 20160 := by simpa [hn] using hdiv
      have hnot : ¬ 27 ∣ 20160 := by norm_num
      exact hnot (by simpa using h27.trans hpown)
    have hnCases : n = 1 ∨ n = 2 := by omega
    rcases hnCases with rfl | rfl
    · exact Or.inl hn
    · exact Or.inr (Or.inl (by simpa using hn))
  · have hnle : n ≤ 1 := by
      by_contra hnnot
      have h25 : 5 ^ 2 ∣ 5 ^ n := Nat.pow_dvd_pow 5 (by omega)
      have hpown : 5 ^ n ∣ 20160 := by simpa [hn] using hdiv
      have hnot : ¬ 25 ∣ 20160 := by norm_num
      exact hnot (by simpa using h25.trans hpown)
    have hn1 : n = 1 := by omega
    subst n
    exact Or.inr (Or.inr (Or.inl (by simpa using hn)))
  · have hnle : n ≤ 1 := by
      by_contra hnnot
      have h49 : 7 ^ 2 ∣ 7 ^ n := Nat.pow_dvd_pow 7 (by omega)
      have hpown : 7 ^ n ∣ 20160 := by simpa [hn] using hdiv
      have hnot : ¬ 49 ∣ 20160 := by norm_num
      exact hnot (by simpa using h49.trans hpown)
    have hn1 : n = 1 := by omega
    subst n
    exact Or.inr (Or.inr (Or.inr (by simpa using hn)))

private theorem fixedPointSubgroup_eq_bot_of_commutatorAction_eq_top
    {A M : Type*} [Group A] [Finite A] [Group M] [Finite M]
    [MulDistribMulAction A M]
    (hsolv : Group.IsSolvable M)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card M))
    (hcommM : IsMulCommutative M)
    (hcomm : commutatorAction A M = ⊤) :
    FixedPoints.subgroup A M = ⊥ := by
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := M) (A := A) hsolv hcop hcommM
  apply eq_bot_iff.mpr
  intro z hz
  have hzinf : z ∈ FixedPoints.subgroup A M ⊓ commutatorAction A M :=
    ⟨hz, by rw [hcomm]; exact Subgroup.mem_top z⟩
  exact hcompl.disjoint.le_bot hzinf

private theorem prod_mem_subgroup_of_involution
    {I M : Type*} [Fintype I] [DecidableEq I] [CommGroup M]
    (s : Finset I) (e : I ≃ I)
    (he : ∀ i, e (e i) = i)
    (hs : ∀ i, i ∈ s ↔ e i ∈ s)
    (hfix : ∀ i ∈ s, e i ≠ i)
    (K : Subgroup M) (f : I → M)
    (hpair : ∀ i ∈ s, f i * f (e i) ∈ K) :
    ∏ i ∈ s, f i ∈ K := by
  induction s using Finset.strongInduction with
  | H s ih =>
      by_cases hsempty : s = ∅
      · subst s
        simp
      · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hsempty
        have hei : e i ∈ s := (hs i).mp hi
        have hne : e i ≠ i := hfix i hi
        let t := (s.erase i).erase (e i)
        have htlt : t ⊂ s := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
          · intro hts
            have : i ∈ t := hts.symm ▸ hi
            simp [t] at this
        have hts (j : I) : j ∈ t ↔ e j ∈ t := by
          simp only [t, Finset.mem_erase]
          constructor
          · rintro ⟨hjei, hji, hjs⟩
            refine ⟨?_, ?_, (hs j).mp hjs⟩
            · intro hej_i
              exact hji (e.injective hej_i)
            · intro hej_ei
              apply hjei
              have := congrArg e hej_ei
              simpa [he] using this
          · rintro ⟨hej_ei, hej_i, hejs⟩
            refine ⟨?_, ?_, (hs j).mpr hejs⟩
            · intro hjei
              have := congrArg e hjei
              exact hej_i (by simpa [he] using this)
            · intro hji
              exact hej_ei (congrArg e hji)
        have htprod : ∏ j ∈ t, f j ∈ K :=
          ih t htlt hts (fun j hj => hfix j ((Finset.erase_subset _ _).trans
            (Finset.erase_subset _ _) hj))
            (fun j hj => hpair j ((Finset.erase_subset _ _).trans
              (Finset.erase_subset _ _) hj))
        have heiErase : e i ∈ s.erase i := by simpa [hne] using hei
        have hdecomp : ∏ j ∈ s, f j = (f i * f (e i)) * ∏ j ∈ t, f j := by
          calc
            ∏ j ∈ s, f j = (∏ j ∈ s.erase i, f j) * f i :=
              (Finset.prod_erase_mul s f hi).symm
            _ = ((∏ j ∈ (s.erase i).erase (e i), f j) * f (e i)) * f i := by
              rw [Finset.prod_erase_mul (s.erase i) f heiErase]
            _ = (f i * f (e i)) * ∏ j ∈ t, f j := by
              simp [t, mul_comm, mul_left_comm]
        rw [hdecomp]
        exact K.mul_mem (hpair i hi) htprod

private theorem involution_fixed_card_four
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal)
    (hFcomm : IsMulCommutative F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hcardV : Nat.card V = 16) :
    Nat.card V = 4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) := by
  classical
  let : F.Normal := hFnorm
  let : IsMulCommutative F := hFcomm
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let R : Subgroup G := Subgroup.zpowers x
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
  have hcardR : Nat.card R = 2 := by
    simpa [R, Nat.card_zpowers] using hxorder
  have hRnormF : R ≤ Subgroup.normalizer F := Subgroup.le_normalizer_of_normal
  let : Subgroup.Normalizes R F := ⟨hRnormF⟩
  have hcommRFmap :
      (commutatorAction R F).map F.subtype = ⁅F, R⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator F R hRnormF
  have hcommRF : commutatorAction R F = ⊤ := by
    apply Subgroup.map_injective F.subtype_injective
    rw [hcommRFmap, show ⁅F, R⁆ = F by simpa [R] using hcommFx]
    ext g
    simp
  have hcopRF : Nat.Coprime (Nat.card R) (Nat.card F) := by
    simpa [hcardR] using hFodd
  have hfixRF : FixedPoints.subgroup R F = ⊥ :=
    fixedPointSubgroup_eq_bot_of_commutatorAction_eq_top
      (Group.isSolvable_of_comm fun a b => mul_comm a b)
      hcopRF hFcomm hcommRF
  let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
  let sigma : MulAut F := MulDistribMulAction.toMulAut R F rx
  have hsigma_involutive : Function.Involutive sigma := by
    intro f
    change rx • (rx • f) = f
    rw [← mul_smul]
    have hrxSq : rx * rx = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hx.2
    rw [hrxSq, one_smul]
  have hsigma_fixed : MonoidHom.FixedPointFree sigma := by
    intro f hf
    have hfall : f ∈ FixedPoints.subgroup R F := by
      rw [FixedPoints.mem_subgroup]
      intro r
      by_cases hr : r = 1
      · simp [hr]
      · obtain ⟨z, hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : R)).mp hcardR
        have hrxne : rx ≠ 1 := by
          intro h
          exact hx.1 (congrArg Subtype.val h)
        have hre : r = rx := (hzuniq r hr).trans (hzuniq rx hrxne).symm
        simpa [hre, sigma] using hf
    rw [hfixRF] at hfall
    simpa using hfall
  have hsigma_inv : ∀ f : F, sigma f = f⁻¹ := by
    intro f
    exact congrFun (hsigma_fixed.coe_eq_inv_of_involutive hsigma_involutive) f
  let : Fintype F := Fintype.ofFinite F
  let N : V →* V := by
    refine
      { toFun := fun v => ∏ f : F, (f : G) • v
        map_one' := by simp
        map_mul' := ?_ }
    intro v w
    simp only [smul_mul']
    exact Finset.prod_mul_distrib
  have hnorm_gen (a : F) (v : V) : N (v⁻¹ * ((a : G) • v)) = 1 := by
    have hprod_shift : (∏ b : F, ((b * a : F) : G) • v) =
        ∏ b : F, (b : G) • v := by
      have hbij : Function.Bijective (fun b : F => b * a) := by
        refine ⟨fun _ _ h => mul_right_cancel h, fun b => ⟨b * a⁻¹, by simp [mul_assoc]⟩⟩
      simpa using
        (Fintype.prod_bijective
          (e := fun b : F => b * a)
          (he := hbij)
          (f := fun b : F => ((b * a : F) : G) • v)
          (g := fun b : F => (b : G) • v)
          (by intro b; rfl))
    calc
      N (v⁻¹ * ((a : G) • v)) =
          ∏ b : F, (((b : G) • v)⁻¹ * (((b * a : F) : G) • v)) := by
            simp [N, smul_mul', smul_smul]
      _ = (∏ b : F, ((b : G) • v)⁻¹) *
          (∏ b : F, (((b * a : F) : G) • v)) := by
            rw [Finset.prod_mul_distrib]
      _ = (∏ b : F, ((b : G) • v)⁻¹) * (∏ b : F, (b : G) • v) := by
            rw [hprod_shift]
      _ = 1 := by simp
  have hcomm_le_ker : commutatorAction F V ≤ N.ker := by
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := N.ker)).2 ?_
    intro z hz
    rcases hz with ⟨a, v, rfl⟩
    change N (v⁻¹ * ((a : G) • v)) = 1
    exact hnorm_gen a v
  have hNorm (v : V) : N v = 1 := by
    have hv : v ∈ commutatorAction F V := by rw [hcommFV]; exact Subgroup.mem_top v
    exact MonoidHom.mem_ker.mp (hcomm_le_ker hv)
  let Kx : Subgroup V := commutatorAction R V
  have hfix_le : FixedPoints.subgroup R V ≤ Kx := by
    intro v hv
    have hvx : x • v = v :=
      (FixedPoints.mem_subgroup (M := R) (a := v)).1 hv rx
    let s : Finset F := Finset.univ.erase 1
    have hprod : ∏ a ∈ s, ((a : G) • v) ∈ Kx := by
      apply prod_mem_subgroup_of_involution s sigma.toEquiv hsigma_involutive
      · intro a
        simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro ha
          exact fun h => ha (sigma.injective (by simpa using h))
        · intro ha h
          exact ha (by simpa using congrArg sigma.symm h)
      · intro a ha hfix
        have hane : a ≠ 1 := by simpa [s] using ha
        exact hane (hsigma_fixed a hfix)
      · intro a _ha
        change ((a : G) • v) * ((sigma a : F) : G) • v ∈ commutatorAction R V
        rw [commutatorAction_eq_closure]
        apply Subgroup.subset_closure
        refine ⟨rx, (a : G) • v, ?_⟩
        rw [hsigma_inv]
        simp only [inv_eq_self_of_exponent_two
          IsElementaryAbelian.exponent_eq_prime]
        change (a : G) • v * ((a⁻¹ : F) : G) • v =
          ((a : G) • v) * (x • ((a : G) • v))
        congr 1
        calc
          ((a⁻¹ : F) : G) • v = (x * (a : G) * x⁻¹) • v := by
            have hs : ((sigma a : F) : G) = x * (a : G) * x⁻¹ := by
              exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe R F rx a
            have hainv : ((a⁻¹ : F) : G) = x * (a : G) * x⁻¹ := by
              rw [← hsigma_inv a]
              exact hs
            rw [hainv]
          _ = x • ((a : G) • (x⁻¹ • v)) := by simp [smul_smul, mul_assoc]
          _ = x • ((a : G) • v) := by
            have hxinvfix : x⁻¹ • v = v := by rw [hxinv, hvx]
            rw [hxinvfix]
    have hNdecomp : N v = v * ∏ a ∈ s, ((a : G) • v) := by
      calc
        N v = ∏ a : F, (a : G) • v := rfl
        _ = (∏ a ∈ s, (a : G) • v) * ((1 : F) : G) • v := by
          exact (Finset.prod_erase_mul Finset.univ (fun a : F => (a : G) • v)
            (Finset.mem_univ 1)).symm
        _ = v * ∏ a ∈ s, ((a : G) • v) := by simp [mul_comm]
    have hvprod : v = ∏ a ∈ s, ((a : G) • v) := by
      have hn := hNorm v
      rw [hNdecomp] at hn
      exact (eq_inv_of_mul_eq_one_left hn).trans
        (inv_eq_self_of_exponent_two IsElementaryAbelian.exponent_eq_prime _)
    rw [hvprod]
    exact hprod
  let d : V →* V :=
    { toFun := fun v => v⁻¹ * (x • v)
      map_one' := by simp
      map_mul' := by
        intro v w
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hker : d.ker = FixedPoints.subgroup R V := by
    ext v
    constructor
    · intro hv
      rw [FixedPoints.mem_subgroup]
      intro r
      have hvx : x • v = v := by
        exact (eq_of_inv_mul_eq_one (MonoidHom.mem_ker.mp hv)).symm
      by_cases hr : r = 1
      · simp [hr]
      · obtain ⟨z, hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : R)).mp hcardR
        have hrxne : rx ≠ 1 := by
          intro h
          exact hx.1 (congrArg Subtype.val h)
        have hre : r = rx := (hzuniq r hr).trans (hzuniq rx hrxne).symm
        simpa [hre, rx] using hvx
    · intro hv
      rw [MonoidHom.mem_ker]
      have hvx := (FixedPoints.mem_subgroup (M := R) (a := v)).1 hv rx
      exact inv_mul_eq_one.mpr (by simpa [rx] using hvx.symm)
  have hrange : d.range = Kx := by
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨v, rfl⟩
      change v⁻¹ * (x • v) ∈ commutatorAction R V
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨rx, v, rfl⟩
    · change commutatorAction R V ≤ d.range
      rw [commutatorAction_eq_closure]
      refine (Subgroup.closure_le (K := d.range)).2 ?_
      intro z hz
      rcases hz with ⟨r, v, rfl⟩
      by_cases hr : r = 1
      · subst r
        exact ⟨1, by simp [d]⟩
      · obtain ⟨z, hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : R)).mp hcardR
        have hrxne : rx ≠ 1 := by
          intro h
          exact hx.1 (congrArg Subtype.val h)
        have hre : r = rx := (hzuniq r hr).trans (hzuniq rx hrxne).symm
        exact ⟨v, by simp [d, hre, rx]⟩
  have hKx_le_fix : Kx ≤ FixedPoints.subgroup R V := by
    rw [← hker, ← hrange]
    intro z hz
    rcases hz with ⟨v, rfl⟩
    rw [MonoidHom.mem_ker]
    have hxx (w : V) : x • (x • w) = w := by
      rw [← mul_smul, ← pow_two, hx.2, one_smul]
    have hexp : Monoid.exponent V = 2 := IsElementaryAbelian.exponent_eq_prime
    have hpow := Monoid.pow_exponent_eq_one ((x • v)⁻¹ * v)
    rw [hexp] at hpow
    simpa [d, smul_mul', hxx, pow_two] using hpow
  have heq : Kx = FixedPoints.subgroup R V := le_antisymm hKx_le_fix hfix_le
  have hcardSquare : Nat.card V =
      Nat.card (FixedPoints.subgroup R V) * Nat.card (FixedPoints.subgroup R V) := by
    calc
      Nat.card V = Nat.card d.ker * d.ker.index := d.ker.card_mul_index.symm
      _ = Nat.card d.ker * Nat.card d.range := by rw [Subgroup.index_ker]
      _ = Nat.card (FixedPoints.subgroup R V) *
          Nat.card (FixedPoints.subgroup R V) := by rw [hker, hrange, heq]
  have hcardFix : Nat.card (FixedPoints.subgroup R V) = 4 := by
    have : 16 = Nat.card (FixedPoints.subgroup R V) ^ 2 := by
      simpa [hcardV, pow_two] using hcardSquare
    nlinarith
  change Nat.card V = 4 * Nat.card (FixedPoints.subgroup R V)
  rw [hcardV, hcardFix]

private theorem noncyclic_card_nine_mulEquiv
    {F : Type*} [Group F] [Finite F]
    (hcardF : Nat.card F = 9) (hnotcyclic : ¬ IsCyclic F) :
    Nonempty (F ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcardPow : Nat.card F = 3 ^ 2 := by simpa using hcardF
  let hcomm : IsMulCommutative F :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardPow
  let : IsMulCommutative F := hcomm
  have hexp : Monoid.exponent F = 3 :=
    (not_isCyclic_iff_exponent_eq_prime (by decide) hcardPow).mp hnotcyclic
  let : IsElementaryAbelian 3 F :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := by rw [hexp] }
  let n := Module.finrank (ZMod 3) (Additive F)
  have hn : n = 2 := by
    have hc := Module.natCard_eq_pow_finrank
      (K := ZMod 3) (V := Additive F)
    change Nat.card F = Nat.card (ZMod 3) ^
      Module.finrank (ZMod 3) (Additive F) at hc
    rw [hcardF, show Nat.card (ZMod 3) = 3 by norm_num] at hc
    exact Nat.pow_right_injective (by omega : 1 < 3) hc.symm
  let b0 : Module.Basis (Fin n) (ZMod 3) (Additive F) :=
    Module.finBasis (ZMod 3) (Additive F)
  let b : Module.Basis (Fin 2) (ZMod 3) (Additive F) :=
    b0.reindex (Fin.castOrderIso hn).toEquiv
  let eadd : Additive F ≃+ (ZMod 3 × ZMod 3) :=
    b.equivFun.toAddEquiv.trans
      (LinearEquiv.finTwoArrow (ZMod 3) (ZMod 3)).toAddEquiv
  exact ⟨(MulEquiv.multiplicativeAdditive F).symm |>.trans
    (AddEquiv.toMultiplicative eadd) |>.trans
    (MulEquiv.prodMultiplicative (ZMod 3) (ZMod 3))⟩

/-- The `GL₄(2)` classification endpoint used in the first two cases of Stellmacher's
Lemma (1.3). -/
theorem glFourTwo_involutionPGroup_classification
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal) (hFne : F ≠ ⊥)
    (p : ℕ) [Fact p.Prime] (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (_hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hcardV : Nat.card V = 2 ^ 4)
    (_hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    Nat.card V =
        4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) ∧
      (Nonempty (F ≃* Multiplicative (ZMod 3)) ∨
       Nonempty (F ≃* Multiplicative (ZMod 5)) ∨
       Nonempty
         (F ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))) := by
  let _ : F.Normal := hFnorm
  have hfaithF : fixingSubgroup F (Set.univ : Set V) = ⊥ := by
    apply le_antisymm
    · intro f hf
      have hfambient : (f : G) ∈ fixingSubgroup G (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff] at hf ⊢
        intro z hz
        simpa only [Subgroup.smul_def] using hf z hz
      rw [hfaith] at hfambient
      exact Subtype.ext (by simpa using hfambient)
    · exact bot_le
  let rho := Representation.ofElementaryAbelianAction
    (A := F) (G := V) (p := 2)
  have hrhoinj : Function.Injective rho.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro f hf
      have hrhof : rho f = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hf)
      have hfker : f ∈ fixingSubgroup F (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        intro z _hz
        apply Additive.ofMul.injective
        have happ := LinearMap.congr_fun hrhof (Additive.ofMul z)
        simpa [rho] using happ
      rw [hfaithF] at hfker
      simpa using hfker
    · exact bot_le
  let nV := Module.finrank (ZMod 2) (Additive V)
  have hnV : nV = 4 := by
    have hc := Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive V)
    change Nat.card V = Nat.card (ZMod 2) ^
      Module.finrank (ZMod 2) (Additive V) at hc
    rw [hcardV, show Nat.card (ZMod 2) = 2 by norm_num] at hc
    exact Nat.pow_right_injective (by omega : 1 < 2) hc.symm
  let b0 : Module.Basis (Fin nV) (ZMod 2) (Additive V) :=
    Module.finBasis (ZMod 2) (Additive V)
  let b : Module.Basis (Fin 4) (ZMod 2) (Additive V) :=
    b0.reindex (Fin.castOrderIso hnV).toEquiv
  let phi : F →* GL4 :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp rho.asGroupHom
  have hphiinj : Function.Injective phi :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hrhoinj
  have hFnontrivial : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot (H := F)).mpr hFne
  have hcards : Nat.card F = 3 ∨ Nat.card F = 9 ∨
      Nat.card F = 5 ∨ Nat.card F = 7 :=
    gl4_pgroup_card_cases p hFp hFnontrivial hFodd phi hphiinj
  have hcopFV : Nat.Coprime (Nat.card F) (Nat.card V) := by
    simpa [hcardV] using hFodd.symm.pow_right 4
  have hfixF : FixedPoints.subgroup F V = ⊥ :=
    fixedPointSubgroup_eq_bot_of_commutatorAction_eq_top
      (Group.isSolvable_of_comm fun a b =>
        (IsMulCommutative.is_comm (M := V)).comm a b)
      hcopFV (inferInstance : IsMulCommutative V) hcommFV
  have hnotSeven : Nat.card F ≠ 7 := by
    intro hcardF
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hFseven : IsPGroup 7 F :=
      IsPGroup.of_card (p := 7) (n := 1) (by simpa using hcardF)
    have hmod := hFseven.card_modEq_card_fixedPoints V
    change Nat.ModEq 7 (Nat.card V)
      (Nat.card (FixedPoints.subgroup F V)) at hmod
    have : Nat.ModEq 7 16 1 := by
      simpa [hcardV, hfixF] using hmod
    norm_num at this
  have hnotCyclicNine : Nat.card F = 9 → ¬ IsCyclic F := by
    intro hcardF
    exact not_isCyclic_of_card_nine_of_faithful_on_card_sixteen
      hcardF (by norm_num [hcardV]) hfaithF
  have hFcomm : IsMulCommutative F := by
    rcases hcards with hcardF | hcardF | hcardF | hcardF
    · let : Fact (Nat.Prime 3) := ⟨by decide⟩
      exact (isCyclic_of_prime_card hcardF).isMulCommutative
    · let : Fact (Nat.Prime 3) := ⟨by decide⟩
      exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
        (by simpa using hcardF)
    · let : Fact (Nat.Prime 5) := ⟨by decide⟩
      exact (isCyclic_of_prime_card hcardF).isMulCommutative
    · exact False.elim (hnotSeven hcardF)
  have hfixed := involution_fixed_card_four F hFnorm hFcomm hFodd x hx
    hcommFx hcommFV (by norm_num [hcardV])
  refine ⟨hfixed, ?_⟩
  rcases hcards with hcardF | hcardF | hcardF | hcardF
  · left
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact ⟨mulEquivOfPrimeCardEq hcardF (by norm_num)⟩
  · right; right
    exact noncyclic_card_nine_mulEquiv hcardF (hnotCyclicNine hcardF)
  · right; left
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact ⟨mulEquivOfPrimeCardEq hcardF (by norm_num)⟩
  · exact False.elim (hnotSeven hcardF)

end Stellmacher.SectionOne
