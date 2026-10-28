module

public import BenderSuzuki.Converse.Lift
public import BenderSuzuki.SE.StrongEmbeddingConjugacy
public import BenderSuzuki.PFchapter1section1.proposition_2_a

/-!
# Commuting conjugates from strong embedding

The concrete Bender models have a four-group and a doubly transitive action
whose two-point stabilizers have odd order. We turn that action into strong
embedding, then use involution fusion to transport a commuting pair from the
four-group to any specified involution.

This is the group-theoretic part of the involution geometry used in
Aschbacher--Smith, *The Classification of Quasithin Groups*, I.8.2,
printed pp. 429–430. The fusion input is [IG; 17.8(i)], proved in
`SE.StrongEmbeddingConjugacy`; the action hypotheses are Peterfalvi's (A1).
-/

namespace BenderSuzuki
open PFAppendixIII PFchapter1section1
open scoped IsMulCommutative

/-- A doubly transitive point stabilizer with the even/odd decomposition of
Peterfalvi's Hypothesis (A1) is strongly embedded. Distinct two-point
stabilizers are conjugate and hence have the same odd order as `D`. -/
public theorem PFchapter1section1.HypothesisA1.isStronglyEmbedded
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G} (hA : HypothesisA1 G Ω H D Q t) :
    IsStronglyEmbedded H := by
  obtain ⟨ω, hHω⟩ := hA.point_stabilizer
  have hmem : ∀ g : G, g ∈ H ↔ g • ω = ω := by
    intro g; rw [hHω]; exact MulAction.mem_stabilizer_iff
  have htω : t⁻¹ • ω ≠ ω := by
    intro hcon
    exact hA.t_not_mem_H ((hmem t).2 (inv_smul_eq_iff.mp hcon).symm)
  have hDstab : D = MulAction.stabilizer G ω ⊓ MulAction.stabilizer G (t⁻¹ • ω) := by
    rw [hA.D_eq, hHω, rightConjugate_stabilizer]
  have hΩpos : 0 < Nat.card Ω - 1 := by
    have : Nonempty Ω := ⟨ω⟩
    have hne : Nat.card Ω ≠ 1 := by
      intro h
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 h
      exact htω (hsub.allEq _ _)
    have hpos : 0 < Nat.card Ω := Nat.card_pos
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    exact hA.t_not_mem_H (by rw [hc]; exact Subgroup.mem_top t)
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 hA.Q_even.two_dvd
    have hxi : IsInvolution x := by
      have h := (orderOf_eq_prime_iff (p := 2)).mp hx
      exact ⟨h.2, h.1⟩
    exact ⟨x, hA.Q_le_H x.property,
      IsInvolution.map_of_injective hxi Q.subtype Q.subtype_injective⟩
  · intro g hg x hxH hxconj
    have hgω : g⁻¹ • ω ≠ ω := by
      intro h
      exact hg ((hmem g).2 (inv_smul_eq_iff.mp h).symm)
    have hconj : H ⊓ rightConjugate H g =
        MulAction.stabilizer G ω ⊓ MulAction.stabilizer G (g⁻¹ • ω) := by
      rw [hHω, rightConjugate_stabilizer]
    have h1 := Converse.card_stabilizer_eq_twoPoint_mul hA.two_transitive hgω
    have h2 := Converse.card_stabilizer_eq_twoPoint_mul hA.two_transitive htω
    have hEq : Nat.card (H ⊓ rightConjugate H g : Subgroup G) = Nat.card D := by
      rw [hconj, hDstab]
      exact Nat.eq_of_mul_eq_mul_right hΩpos (h1.symm.trans h2)
    exact not_isInvolution_of_mem_odd_subgroup (H ⊓ rightConjugate H g) (hEq.symm ▸ hA.D_odd) ⟨hxH, hxconj⟩

private theorem commuting_pair_of_rank
    {G : Type*} [Group G] [Finite G] (hrank : TwoRankAtLeastTwo G) :
    ∃ x y : G, IsInvolution x ∧ IsInvolution y ∧ x ≠ y ∧ Commute x y := by
  classical
  obtain ⟨E, hcard, hsq⟩ := hrank
  let : Fintype E := Fintype.ofFinite E
  have hcard' : 2 < Fintype.card E := by rw [← Nat.card_eq_fintype_card, hcard]; omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcard'
  let x := a⁻¹ * b
  let y := a⁻¹ * c
  have hx : IsInvolution x := ⟨fun h => hab (inv_mul_eq_one.mp h), hsq x⟩
  have hy : IsInvolution y := ⟨fun h => hac (inv_mul_eq_one.mp h), hsq y⟩
  let : IsMulCommutative E := isMulCommutative_of_forall_sq_one hsq
  have hxy : x ≠ y := by simpa [x, y] using hbc
  have hc : Commute x y := mul_comm x y
  exact ⟨x, y, IsInvolution.map_of_injective hx E.subtype E.subtype_injective,
    IsInvolution.map_of_injective hy E.subtype E.subtype_injective,
    fun h => hxy (Subtype.ext h), hc.map E.subtype⟩

/-- In a group with a strongly embedded subgroup and a four-group, every
involution has a distinct commuting conjugate. Strong embedding gives one
involution class; conjugate a pair from the four-group to the given involution. -/
public theorem IsStronglyEmbedded.exists_distinct_commuting_conjugate_of_twoRank
    {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hM : IsStronglyEmbedded M) (hrank : TwoRankAtLeastTwo G)
    (i : G) (hi : IsInvolution i) :
    ∃ g : G, MulAut.conj g i ≠ i ∧ Commute i (MulAut.conj g i) := by
  obtain ⟨x, y, hx, hy, hxy, hc⟩ := commuting_pair_of_rank hrank
  obtain ⟨g, hg⟩ := hM.involutions_conjugate hi hx
  obtain ⟨h, hh⟩ := hM.involutions_conjugate hi hy
  have hx' : MulAut.conj g x = i := by
    rw [← hg]
    simp [rightConjugateElem, MulAut.conj_apply, mul_assoc]
  have hy' : MulAut.conj (g * h⁻¹) i = MulAut.conj g y := by
    rw [← hh]
    simp [rightConjugateElem, MulAut.conj_apply, mul_assoc]
  refine ⟨g * h⁻¹, ?_, ?_⟩
  · rw [hy', ← hx']
    exact fun heq => hxy ((MulAut.conj g).injective heq).symm
  · rw [hy', ← hx']
    exact hc.map (MulAut.conj g)
end BenderSuzuki
