module

public import Theory.GroupAction.SimpleCosets
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The fifteen-point action of A₇

For every actual subgroup H ≅ PSL₃(2) of A₇, the left-coset action on A₇/H
is two-transitive. Its degree is fifteen by the group orders. Simplicity of
A₇ excludes overgroups of indices three and five, making H maximal and
self-normalizing. Thus H fixes only its own coset. Simplicity of PSL₃(2)
and the prime divisor seven of its order force every other H-orbit to
have length at least seven.

The coset action is faithful. An involution therefore swaps some pair of
cosets, and pair reversal acts freely on the resulting orbit of ordered
pairs. Since the degree is odd, the corresponding H-suborbit has even
length, hence at least eight. The remaining six points cannot contain
another nontrivial H-orbit, proving two-transitivity.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.4.12(2), printed p.97/PDF p.108 of `refs/quasithin.pdf`.
The imported ATLAS simplicity proof retains its attribution and license.
-/

open MulAction Subgroup
open scoped MatrixGroups

namespace FifteenPointSubgroups

private abbrev A7 := alternatingGroup (Fin 7)

private theorem card_a7 : Nat.card A7 = 2520 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem a7_index (H : Subgroup A7) (hH : Nat.card H = 168) : H.index = 15 := by
  have h := H.card_mul_index
  rw [hH, card_a7] at h
  omega

private theorem a7_maximal (H : Subgroup A7) (hH : Nat.card H = 168) : IsCoatom H := by
  let : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)
  have hi := a7_index H hH
  refine ⟨?_, ?_⟩
  · intro h
    rw [h, Subgroup.index_top] at hi
    contradiction
  · intro K hK
    have hd := Subgroup.index_dvd_of_le hK.le
    rw [hi] at hd
    have hd' : K.index = 1 ∨ K.index = 3 ∨ K.index = 5 ∨ K.index = 15 := by
      have hdiv : (15 : ℕ).divisors = {1, 3, 5, 15} := by decide
      simpa only [hdiv, Finset.mem_insert, Finset.mem_singleton] using
        (Nat.mem_divisors.mpr ⟨hd, by decide⟩ : K.index ∈ (15 : ℕ).divisors)
    rcases hd' with h1 | h3 | h5 | h15
    · exact Subgroup.index_eq_one.mp h1
    · by_contra hn
      have hf := K.card_dvd_factorial_index_of_simple hn
      rw [card_a7, h3] at hf
      norm_num [Nat.factorial] at hf
    · by_contra hn
      have hf := K.card_dvd_factorial_index_of_simple hn
      rw [card_a7, h5] at hf
      norm_num [Nat.factorial] at hf
    · have hs := Subgroup.index_strictAnti hK
      omega

private theorem a7_self_normalizing (H : Subgroup A7) (hH : Nat.card H = 168) :
    normalizer H = H := by
  let : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)
  have hm := a7_maximal H hH
  by_contra hn
  have hlt : H < normalizer H := lt_of_le_of_ne H.le_normalizer (fun h => hn h.symm)
  have htop := hm.2 _ hlt
  have hnormal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hnormal.eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.card_bot] at hH
    contradiction
  · exact hm.1 ht

private theorem a7_fixed_coset (H : Subgroup A7) (hH : Nat.card H = 168)
    (q : A7 ⧸ H) (hq : ∀ h : H, h • q = q) : q = QuotientGroup.mk 1 := by
  induction q using Quotient.inductionOn with
  | h g =>
    have hn : g ∈ normalizer H := Sylow.mem_fixedPoints_mul_left_cosets_iff_mem_normalizer.mp hq
    rw [a7_self_normalizing H hH] at hn
    apply QuotientGroup.eq.mpr
    simpa using H.inv_mem hn

private theorem psl3_min_index {P : Type*} [Group P] [Finite P] [IsSimpleGroup P]
    (hc : Nat.card P = 168) (K : Subgroup P) (hK : K ≠ ⊤) : 7 ≤ K.index := by
  have hd := K.card_dvd_factorial_index_of_simple hK
  rw [hc] at hd
  exact (Nat.Prime.dvd_factorial (by decide : Nat.Prime 7)).mp
    (dvd_trans (by decide : 7 ∣ 168) hd)

private theorem a7_suborbit_min (H : Subgroup A7) (e : H ≃* PSL(3, ZMod 2))
    (q : A7 ⧸ H) (hq : q ≠ QuotientGroup.mk 1) : 7 ≤ Nat.card (orbit H q) := by
  let : IsSimpleGroup PSL(3, ZMod 2) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup H := e.isSimpleGroup
  have hc : Nat.card H = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hn : stabilizer H q ≠ ⊤ := by
    intro ht
    apply hq
    apply a7_fixed_coset H hc q
    intro h
    exact (show h ∈ stabilizer H q by rw [ht]; trivial)
  have hm := psl3_min_index hc (stabilizer H q) hn
  rwa [index_stabilizer] at hm

private theorem even_card_of_free_involution {X : Type*} [Finite X]
    (f : X → X) (hf : Function.Involutive f) (hn : ∀ x, f x ≠ x) :
    Even (Nat.card X) := by
  classical
  let := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card]
  apply (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)).mp
  have h := Finset.prod_ninvolution (s := Finset.univ) (f := fun _ : X => (-1 : ℤ))
    f (fun _ => by norm_num) (fun x _ => hn x) (fun _ => Finset.mem_univ _) hf
  simpa using h

private theorem card_pair_orbit {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (x y : X) :
    Nat.card (orbit G (x, y)) = Nat.card (orbit (stabilizer G x) y) * Nat.card X := by
  let K := stabilizer G (x, y)
  let H := stabilizer G x
  have hle : K ≤ H := fun g hg => congrArg Prod.fst hg
  have he : K.subgroupOf H = stabilizer H y := by
    ext g
    change (g.val • (x, y) = (x, y)) ↔ g.val • y = y
    change (g.val • x, g.val • y) = (x, y) ↔ g.val • y = y
    simp only [Prod.mk.injEq, show g.val • x = x from g.property, true_and]
  have hi := K.relIndex_mul_index hle
  rw [Subgroup.relIndex, he, index_stabilizer, index_stabilizer_of_transitive] at hi
  rw [show K = stabilizer G (x, y) from rfl, index_stabilizer] at hi
  exact hi.symm

/-- Reversal pairs the ordered pairs in a self-paired orbital without fixed points. -/
private theorem even_suborbit_of_swap {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] [Finite X]
    (hodd : Odd (Nat.card X)) (x y : X) (hne : x ≠ y)
    (hswap : (y, x) ∈ orbit G (x, y)) :
    Even (Nat.card (orbit (stabilizer G x) y)) := by
  let O := orbit G (x, y)
  have hswapO : ∀ p : O, p.val.swap ∈ O := by
    rintro ⟨p, g, rfl⟩
    exact mem_orbit_of_mem_orbit g hswap
  let f : O → O := fun p => ⟨p.val.swap, hswapO p⟩
  have hi : Function.Involutive f := fun _ => Subtype.ext (Prod.swap_swap _)
  have hn : ∀ p : O, f p ≠ p := by
    rintro ⟨p, g, rfl⟩ he
    have he' : g • y = g • x := congrArg (fun p : O => p.val.1) he
    exact hne (MulAction.injective g he'.symm)
  have hev := even_card_of_free_involution f hi hn
  rw [card_pair_orbit, Nat.even_mul] at hev
  exact hev.resolve_right (Nat.not_even_iff_odd.mpr hodd)

/-- An even suborbit has at least eight points, leaving no room for another
nontrivial suborbit of length at least seven. -/
private theorem two_pretransitive_of_large_suborbits {G X : Type*}
    [Group G] [MulAction G X] [MulAction.IsPretransitive G X] [Finite X]
    (hc : Nat.card X = 15) (x : X)
    (hmin : ∀ z : X, z ≠ x → 7 ≤ Nat.card (orbit (stabilizer G x) z))
    (hex : ∃ y : X, y ≠ x ∧ Even (Nat.card (orbit (stabilizer G x) y))) :
    MulAction.IsMultiplyPretransitive G X 2 := by
  classical
  let H := stabilizer G x
  have hnot (z : X) (hz : z ≠ x) : x ∉ orbit H z := by
    rintro ⟨h, hh⟩
    change h • z = x at hh
    apply hz
    calc
      z = h⁻¹ • (h • z) := (inv_smul_smul h z).symm
      _ = h⁻¹ • x := by rw [hh]
      _ = x := h⁻¹.property
  obtain ⟨y, hy, heven⟩ := hex
  have hy7 := hmin y hy
  obtain ⟨k, hk⟩ := heven
  change 7 ≤ Nat.card (orbit H y) at hy7
  change Nat.card (orbit H y) = k + k at hk
  have hy8 : 8 ≤ Nat.card (orbit H y) := by omega
  have hall (z : X) (hz : z ≠ x) : z ∈ orbit H y := by
    by_contra hn
    have hd : Disjoint (orbit H y) (orbit H z) := by
      apply Set.disjoint_left.mpr
      intro w hwy hwz
      have heq : orbit H z = orbit H y :=
        (orbit_eq_iff.mpr hwz).symm.trans (orbit_eq_iff.mpr hwy)
      exact hn (heq ▸ mem_orbit_self z)
    have hxn : x ∉ orbit H y ∪ orbit H z := by
      exact fun h => h.elim (hnot y hy) (hnot z hz)
    have hb := Set.ncard_le_card (s := insert x (orbit H y ∪ orbit H z))
    rw [Set.ncard_insert_of_notMem hxn, Set.ncard_union_eq hd, hc] at hb
    have hz7 := hmin z hz
    change (orbit H y).ncard + (orbit H z).ncard + 1 ≤ 15 at hb
    change 7 ≤ (orbit H z).ncard at hz7
    change 8 ≤ (orbit H y).ncard at hy8
    omega
  have htrans (a b : X) (ha : a ≠ x) (hb : b ≠ x) : ∃ h : H, h • a = b := by
    obtain ⟨s, hs⟩ := hall a ha
    obtain ⟨t, ht⟩ := hall b hb
    change s • y = a at hs
    change t • y = b at ht
    refine ⟨t * s⁻¹, ?_⟩
    rw [mul_smul, ← hs, inv_smul_smul, ht]
  apply is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨s, hs⟩ := exists_smul_eq G a x
  obtain ⟨t, ht⟩ := exists_smul_eq G c x
  have hsb : s • b ≠ x := fun h => hab (MulAction.injective s (hs.trans h.symm))
  have htd : t • d ≠ x := fun h => hcd (MulAction.injective t (ht.trans h.symm))
  obtain ⟨u, hu⟩ := htrans (s • b) (t • d) hsb htd
  refine ⟨t⁻¹ * u.val * s, ?_, ?_⟩
  · simp only [mul_smul, hs, show u.val • x = x from u.property]
    rw [← ht, inv_smul_smul]
  · simp only [mul_smul]
    change t⁻¹ • (u • (s • b)) = d
    rw [hu, inv_smul_smul]

/-- Faithfulness and Cauchy supply a moved pair swapped by an involution. -/
private theorem exists_even_suborbit {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [MulAction.IsPretransitive G X] [Finite X] [FaithfulSMul G X]
    (hodd : Odd (Nat.card X)) (heven : 2 ∣ Nat.card G) (x : X) :
    ∃ y : X, y ≠ x ∧ Even (Nat.card (orbit (stabilizer G x) y)) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 heven
  have htne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    contradiction
  have hmove : ∃ q : X, t • q ≠ q := by
    by_contra hn
    push Not at hn
    apply htne
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    simpa only [one_smul] using hn
  obtain ⟨q, hq⟩ := hmove
  obtain ⟨g, hg⟩ := exists_smul_eq G x q
  let s := g⁻¹ * t * g
  have hs : s * s = 1 := by
    have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
    dsimp [s]
    calc
      g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; simp
  have hsx : s • x ≠ x := by
    intro hh
    apply hq
    have hh' := congrArg (fun z : X => g • z) hh
    simpa only [s, mul_smul, smul_inv_smul, hg] using hh'
  refine ⟨s • x, hsx, even_suborbit_of_swap hodd x (s • x) hsx.symm ?_⟩
  refine ⟨s, ?_⟩
  change (s • x, s • (s • x)) = (s • x, x)
  rw [← mul_smul, hs, one_smul]

/-- Every subgroup actually isomorphic to PSL₃(2) gives the two-transitive
left-coset action of A₇. -/
public theorem alternating7_two_pretransitive
    (H : Subgroup (alternatingGroup (Fin 7)))
    (hH : Nonempty (H ≃* PSL(3, ZMod 2))) :
    MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7))
      (alternatingGroup (Fin 7) ⧸ H) 2 := by
  obtain ⟨e⟩ := hH
  have hc : Nat.card H = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  let : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)
  let : FaithfulSMul A7 (A7 ⧸ H) := H.faithfulSMul_quotient_of_simple (a7_maximal H hc).1
  have hdegree : Nat.card (A7 ⧸ H) = 15 := a7_index H hc
  let x : A7 ⧸ H := QuotientGroup.mk 1
  apply two_pretransitive_of_large_suborbits hdegree x
  · intro z hz
    change 7 ≤ Nat.card (orbit (stabilizer A7 (QuotientGroup.mk 1 : A7 ⧸ H)) z)
    rw [stabilizer_quotient]
    exact a7_suborbit_min H e z hz
  · apply exists_even_suborbit
    · rw [hdegree]
      decide
    · rw [card_a7]
      decide

end FifteenPointSubgroups
