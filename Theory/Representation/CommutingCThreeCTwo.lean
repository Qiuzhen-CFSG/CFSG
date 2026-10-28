module

public import Theory.Comparator.Defs
public import Theory.Frattini.CoprimeAction
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.Tactic

/-!
# A commuting `C₃`--`C₂` action with four fixed points

Let an order-three subgroup `F` and an order-two subgroup `A` commute on a
finite elementary abelian two-group `V`.  Put `U = [V,F]`.  If `C_U(A)` has
order four but `U` is not fixed by `A`, this module proves that `U` has order
sixteen.

The involution rank--nullity formula bounds `|U|` by `|C_U(A)|² = 16`.
Noncontainment gives `|U| > 4`.  Coprime idempotence makes the order-three
action fixed-point-free on `U`, so the p-group fixed-point congruence gives
`|U| ≡ 1 (mod 3)`; among the remaining powers of two, this excludes eight.

This is the finite action calculation used in the non-generic branch of
Stellmacher's Lemma (1.6), journal page 18; see
`refs/latex/stellmacher-n-group.tex`, lines 456--462.
-/

open scoped Pointwise IsMulCommutative

namespace Representation

universe u

private theorem elementaryAbelian_subgroup
    {V : Type u} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative :=
    ⟨⟨fun x y => Subtype.ext
      (IsMulCommutative.is_comm.comm (x : V) (y : V))⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V)

private theorem commutatorAction_isInvariant_of_commuting_subgroups
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (P Q : Subgroup G) (hPQ : ⁅P, Q⁆ = ⊥) :
    IsInvariant P V (commutatorAction Q V) := by
  have hcomm : P ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPQ
  have hpq (p : P) (q : Q) :
      (p : G) * (q : G) = (q : G) * (p : G) := by
    exact (Subgroup.mem_centralizer_iff.mp (hcomm p.property)
      (q : G) q.property).symm
  have hforward : ∀ p : P, ∀ v : V,
      v ∈ commutatorAction Q V → p • v ∈ commutatorAction Q V := by
    intro p v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun x _ => p • x ∈ Subgroup.closure
        {z : V | ∃ q : Q, ∃ w : V, z = w⁻¹ * q • w})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨q, w, rfl⟩
      refine Subgroup.subset_closure ⟨q, p • w, ?_⟩
      simp only [smul_mul', smul_inv']
      congr 1
      change p • (q • w) = q • (p • w)
      change (p : G) • ((q : G) • w) = (q : G) • ((p : G) • w)
      rw [← mul_smul, ← mul_smul, hpq]
    · simp
    · intro x y _ _ hx hy
      simpa [smul_mul'] using Subgroup.mul_mem _ hx hy
    · intro x _ hx
      simpa [smul_inv'] using Subgroup.inv_mem _ hx
  refine ⟨?_⟩
  intro p v
  constructor
  · exact hforward p v
  · intro hpv
    have := hforward p⁻¹ (p • v) hpv
    simpa [inv_smul_smul] using this

private theorem cardTwo_fixed_commutator_card_data
    {Q U : Type u} [Group Q] [Group U] [Finite Q] [Finite U]
    [Nontrivial U] [IsElementaryAbelian 2 U] [MulDistribMulAction Q U]
    (x : Q) (hx : IsInvolution x) (hcardQ : Nat.card Q = 2) :
    Nat.card U = Nat.card (FixedPoints.subgroup Q U) *
        Nat.card (commutatorAction Q U) ∧
      commutatorAction Q U ≤ FixedPoints.subgroup Q U := by
  classical
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  let d : U →* U :=
    { toFun := fun w => w⁻¹ * (x • w)
      map_one' := by simp
      map_mul' := by
        intro w z
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hker : d.ker = FixedPoints.subgroup Q U := by
    ext w
    constructor
    · intro hw
      rw [FixedPoints.mem_subgroup]
      intro q
      have hwx : x • w = w :=
        (eq_of_inv_mul_eq_one (MonoidHom.mem_ker.mp hw)).symm
      by_cases hq : q = 1
      · simp [hq]
      · obtain ⟨t, _htne, htuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : Q)).mp hcardQ
        have hqx : q = x := (htuniq q hq).trans (htuniq x hx.1).symm
        simpa [hqx] using hwx
    · intro hw
      rw [MonoidHom.mem_ker]
      have hwx := (FixedPoints.mem_subgroup (M := Q) (a := w)).mp hw x
      exact inv_mul_eq_one.mpr hwx.symm
  have hrange : d.range = commutatorAction Q U := by
    apply le_antisymm
    · rintro z ⟨w, rfl⟩
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨x, w, rfl⟩
    · rw [commutatorAction_eq_closure]
      refine (Subgroup.closure_le (K := d.range)).2 ?_
      rintro z ⟨q, w, rfl⟩
      by_cases hq : q = 1
      · subst q
        exact ⟨1, by simp [d]⟩
      · obtain ⟨t, _htne, htuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : Q)).mp hcardQ
        have hqx : q = x := (htuniq q hq).trans (htuniq x hx.1).symm
        exact ⟨w, by simp [d, hqx]⟩
  have hrange_le_ker : d.range ≤ d.ker := by
    intro z hz
    rcases hz with ⟨w, rfl⟩
    rw [MonoidHom.mem_ker]
    have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
    have hxx : x * x = 1 := by simpa [pow_two] using hx.2
    have hexp : Monoid.exponent U = 2 := IsElementaryAbelian.exponent_eq_prime
    have hpow2 (y : U) : y * y = 1 := by
      have h := Monoid.pow_exponent_eq_one y
      rw [hexp] at h
      simpa [pow_two] using h
    have hinvself (y : U) : y⁻¹ = y :=
      (eq_inv_of_mul_eq_one_left (hpow2 y)).symm
    change
      ((w⁻¹ * (x • w))⁻¹ *
        (x • (w⁻¹ * (x • w)))) = 1
    simp only [mul_inv_rev, smul_mul', smul_inv', ← mul_smul, hxx, one_smul]
    simp_rw [hinvself]
    calc
      (x • w) * w * ((x • w) * w) =
          (w * w) * ((x • w) * (x • w)) := by ac_rfl
      _ = 1 := by rw [hpow2, hpow2, one_mul]
  constructor
  · calc
      Nat.card U = Nat.card d.ker * d.ker.index := d.ker.card_mul_index.symm
      _ = Nat.card d.ker * Nat.card d.range := by rw [Subgroup.index_ker]
      _ = Nat.card (FixedPoints.subgroup Q U) *
          Nat.card (commutatorAction Q U) := by rw [hker, hrange]
  · simpa [hker, hrange] using hrange_le_ker

public theorem commutator_card_sixteen_of_commuting_involution_fixed_card_four
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F A : Subgroup G)
    (hFcard : Nat.card F = 3)
    (hAcard : Nat.card A = 2)
    (hcomm : ⁅F, A⁆ = ⊥)
    (hfixed : Nat.card (↥(commutatorAction F V ⊓
      FixedPoints.subgroup A V)) = 4)
    (hnongeneric : ¬ commutatorAction F V ≤
      FixedPoints.subgroup A V) :
    Nat.card (commutatorAction F V) = 2 ^ 4 := by
  let U : Subgroup V := commutatorAction F V
  let X : Subgroup V := U ⊓ FixedPoints.subgroup A V
  let hUinvF : IsInvariant F V U := commutatorAction_isInvariant
  let _ : IsInvariant F V U := hUinvF
  let hUinvA : IsInvariant A V U := by
    simpa only [U, Subgroup.commutator_comm] using
      commutatorAction_isInvariant_of_commuting_subgroups A F
        (by simpa only [Subgroup.commutator_comm] using hcomm)
  let _ : IsInvariant A V U := hUinvA
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let _ : IsElementaryAbelian 2 U := hUelem
  have hcopFV : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hFcard, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hcomplV : IsCompl (FixedPoints.subgroup F V) U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F) (Group.isSolvable_of_comm fun x y =>
        (IsMulCommutative.is_comm (M := V)).comm x y)
      hcopFV inferInstance
  have hfixFU : FixedPoints.subgroup F U = ⊥ := by
    apply Subgroup.map_injective U.subtype_injective
    rw [fixedPoints_subgroup_map_subtype_eq_inf]
    simpa [inf_comm] using hcomplV.disjoint.eq_bot
  have hXcard : Nat.card X = 4 := hfixed
  have hfixedAUmap : (FixedPoints.subgroup A U).map U.subtype = X := by
    simpa only [X, U] using fixedPoints_subgroup_map_subtype_eq_inf U
  have hfixedAUcard : Nat.card (FixedPoints.subgroup A U) = 4 := by
    rw [← Subgroup.card_map_of_injective
      (K := FixedPoints.subgroup A U) U.subtype_injective,
      hfixedAUmap, hXcard]
  let _ : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    have hXleU : X ≤ U := inf_le_left
    have hle : Nat.card X ≤ Nat.card U := Subgroup.card_le_of_le hXleU
    rw [hXcard] at hle
    omega)
  obtain ⟨a, hane, hauniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
  have ha : IsInvolution a := by
    refine ⟨hane, ?_⟩
    have hainv : a⁻¹ ≠ 1 := by simpa using hane
    have heq : a⁻¹ = a := (hauniq a⁻¹ hainv).trans (hauniq a hane).symm
    calc
      a ^ 2 = a * a := pow_two a
      _ = a⁻¹ * a := by rw [heq]
      _ = 1 := inv_mul_cancel a
  obtain ⟨hcardU, hcommAle⟩ :=
    cardTwo_fixed_commutator_card_data (Q := A) (U := U) a ha hAcard
  have hcommAcardLe : Nat.card (commutatorAction A U) ≤ 4 := by
    rw [← hfixedAUcard]
    exact Subgroup.card_le_of_le hcommAle
  have hUle : Nat.card U ≤ 16 := by
    rw [hcardU, hfixedAUcard]
    nlinarith
  have hXneU : X ≠ U := by
    intro hXU
    apply hnongeneric
    intro u hu
    exact (show u ∈ X from hXU ▸ hu).2
  have hXsubNeTop : X.subgroupOf U ≠ ⊤ := by
    intro htop
    apply hXneU
    apply le_antisymm inf_le_left
    exact Subgroup.subgroupOf_eq_top.mp htop
  have hindexGt : 1 < (X.subgroupOf U).index :=
    Subgroup.one_lt_index_of_ne_top hXsubNeTop
  have hsubCard : Nat.card (X.subgroupOf U) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardMul := (X.subgroupOf U).index_mul_card
  have hUgt : 4 < Nat.card U := by
    rw [hsubCard, hXcard] at hcardMul
    nlinarith
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
  have hnle : n ≤ 4 := by
    apply (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp
    norm_num
    simpa [hn] using hUle
  have hnGt : 2 < n := by
    apply (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp
    norm_num
    simpa [hn] using hUgt
  have hnCases : n = 3 ∨ n = 4 := by omega
  rcases hnCases with rfl | rfl
  · have hFthree : IsPGroup 3 F :=
      IsPGroup.of_card (p := 3) (n := 1) (by simpa using hFcard)
    let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hmod := hFthree.card_modEq_card_fixedPoints U
    have hfixedSetCard : Nat.card (MulAction.fixedPoints F U) = 1 := by
      change Nat.card (FixedPoints.subgroup F U) = 1
      rw [hfixFU]
      simp
    rw [hfixedSetCard] at hmod
    norm_num [hn] at hmod
  · simpa [hn]

/-- Rank-nullity and quadraticity for the displacement map of an involution
generating a two-element actor on an elementary abelian two-group. -/
public theorem involution_fixed_commutator_card_data
    {Q U : Type u} [Group Q] [Group U] [Finite Q] [Finite U]
    [Nontrivial U] [IsElementaryAbelian 2 U] [MulDistribMulAction Q U]
    (x : Q) (hx : IsInvolution x) (hQcard : Nat.card Q = 2) :
    Nat.card U = Nat.card (FixedPoints.subgroup Q U) *
      Nat.card (commutatorAction Q U) ∧
      commutatorAction Q U ≤ FixedPoints.subgroup Q U :=
  cardTwo_fixed_commutator_card_data x hx hQcard

end Representation
