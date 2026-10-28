module
public import Theory.PGroupCore
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Binary actions of two-perfect groups with a simple quotient

For a p-perfect group with simple quotient by its p-core, every nontrivial
image still maps onto that simple quotient. If the quotient order is divisible
by five, any binary group moved by the actor has at least sixteen elements.
A perfect actor cannot move an elementary abelian subgroup only into a central
kernel, so this gives two-rank at least four in every central quotient of the
ambient group.

The normal-subgroup and orbit-counting arguments extend those in
`Theory.SpecificGroups.Alternating.FiveChiefDegree` and
`FiveMovedCentralQuotient` without requiring an alternating-five marking.
Source application: Aschbacher--Smith 10.2.6, printed pp.748--749.
-/

public section
open Subgroup
namespace Theory.GroupAction.SimpleQuotientFiveAction

private theorem normal_le_of_simple_quotient
    {G : Type*} [Group G] {p : ℕ}
    (Q : Subgroup G) [Q.Normal] [IsSimpleGroup (G ⧸ Q)]
    (hQ : IsPGroup p Q) (hp : IsPPerfect p G)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊤) : N ≤ Q := by
  let q := QuotientGroup.mk' Q
  have hnmap : (N.map q).Normal :=
    (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective Q)
  rcases hnmap.eq_bot_or_eq_top with hz | ht
  · simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hz
  · exfalso
    apply hN
    apply hp N inferInstance
    let f := (QuotientGroup.mk' N).comp Q.subtype
    apply hQ.of_surjective f
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨n, hn, he⟩ := mem_map.mp (show q x ∈ N.map q by rw [ht]; trivial)
    have hnx : n⁻¹ * x ∈ Q := QuotientGroup.eq.mp he
    refine ⟨⟨n⁻¹ * x, hnx⟩, ?_⟩
    change QuotientGroup.mk' N (n⁻¹ * x) = QuotientGroup.mk' N x
    have hn' : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, map_inv, hn', inv_one, one_mul]

/-- A nontrivial image retains the entire simple p-core quotient order. -/
theorem quotient_card_dvd_range
    {J H : Type*} [Group J] [Finite J] [Group H] {p : ℕ}
    [IsSimpleGroup (J ⧸ pCore p J)] (hp : IsPPerfect p J)
    (f : J →* H) (hf : f ≠ 1) : Nat.card (J ⧸ pCore p J) ∣ Nat.card f.range := by
  have hker : f.ker ≠ ⊤ := by
    intro h
    apply hf
    ext x
    exact MonoidHom.mem_ker.mp (h ▸ mem_top x)
  have hle : f.ker ≤ pCore p J :=
    normal_le_of_simple_quotient (pCore p J) pCore_isPGroup hp f.ker hker
  let q := QuotientGroup.map f.ker (pCore p J) (MonoidHom.id J) hle
  have hq : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective f.ker (pCore p J) (MonoidHom.id J)
      (QuotientGroup.mk'_surjective (pCore p J)) hle
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact card_dvd_of_surjective q hq

/-- A factor of five in the simple quotient forces a moved binary group to have order at least sixteen. -/
theorem sixteen_le_card_of_nontrivial_action
    {J V : Type*} [Group J] [Finite J] [Group V] [Finite V]
    [IsSimpleGroup (J ⧸ pCore 2 J)]
    (hp : IsPPerfect 2 J) (h5 : 5 ∣ Nat.card (J ⧸ pCore 2 J))
    (ρ : J →* MulAut V) (hρ : ρ ≠ 1) (hV : IsPGroup 2 V) :
    16 ≤ Nat.card V := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ρ.range) 5
    (h5.trans (quotient_card_dvd_range hp ρ hρ))
  let B := zpowers a
  have hB : Nat.card B = 5 := (Nat.card_zpowers a).trans ha
  have hnot : FixedPoints.subgroup B V ≠ ⊤ := by
    intro htop
    have he : a = 1 := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      have hv : v ∈ FixedPoints.subgroup B V := htop ▸ mem_top v
      exact hv ⟨a, mem_zpowers a⟩
    simp [he] at ha
  exact Theory.GroupAction.sixteen_le_card_of_five_action_nontrivial hB hV hnot

/-- The nontrivial perfect action survives every central quotient, retaining two-rank at least four. -/
theorem four_le_twoRank_central_quotient
    {G : Type*} [Group G] [Finite G]
    (A U N : Subgroup G) [Group.IsPerfect A] [IsElementaryAbelian 2 U] [N.Normal]
    [IsSimpleGroup (A ⧸ pCore 2 A)]
    (hp : IsPPerfect 2 A) (h5 : 5 ∣ Nat.card (A ⧸ pCore 2 A))
    (hAU : A ≤ normalizer (U : Set G)) (hne : ⁅U,A⁆ ≠ ⊥)
    (hN : N ≤ center G) : 4 ≤ primeRank 2 (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  let E := U.map q
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hnorm : A.map q ≤ normalizer (E : Set (G ⧸ N)) :=
    (map_mono hAU).trans (U.le_normalizer_map q)
  let a : A →* normalizer (E : Set (G ⧸ N)) :=
    (q.comp A.subtype).codRestrict (normalizer (E : Set (G ⧸ N)))
      (fun x => hnorm (mem_map_of_mem q x.property))
  let f : A →* MulAut E := E.normalizerMonoidHom.comp a
  have hf : f ≠ 1 := by
    intro hf
    have hc : A.map q ≤ centralizer (E : Set (G ⧸ N)) := by
      rintro x ⟨b,hb,rfl⟩ y hy
      have hh := congrArg (fun z : MulAut E => (z ⟨y,hy⟩ : G ⧸ N))
        (DFunLike.congr_fun hf ⟨b,hb⟩)
      change q b * y * (q b)⁻¹ = y at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hz : (⁅U,A⁆ : Subgroup G).map q = ⊥ := by
      rw [map_commutator]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
    have hcentral : ⁅U,A⁆ ≤ center G := by
      have hh := (map_eq_bot_iff (⁅U,A⁆ : Subgroup G)).mp hz
      rw [QuotientGroup.ker_mk'] at hh
      exact hh.trans hN
    have hzero : ⁅⁅U,A⁆,A⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (hcentral.trans (center_le_centralizer (A : Set G)))
    exact hne (commutator_eq_bot_of_iterated_eq_bot U A hzero)
  have hcard : 16 ≤ Nat.card E :=
    sixteen_le_card_of_nontrivial_action hp h5 f hf (IsElementaryAbelian.isPGroup 2 E)
  by_contra! hr
  have hsmall : Nat.card E ≤ 2 ^ 3 :=
    (primeRank_le_iff_elementary_card_le (G ⧸ N)).mp (by omega : primeRank 2 (G ⧸ N) ≤ 3)
      E inferInstance
  norm_num at hsmall
  omega

end Theory.GroupAction.SimpleQuotientFiveAction
