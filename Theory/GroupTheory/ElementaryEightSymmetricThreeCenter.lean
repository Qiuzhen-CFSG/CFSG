module

public import Theory.GroupTheory.ElementaryEightThreeNormalizer
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.IndexNormal

/-!
# The central line in an elementary-eight extension of S₃

If a normal abelian subgroup Q has order eight, is self-centralizing, and
has index six, then G has a central subgroup of order two contained in Q.
Conjugation embeds G/Q in Aut(Q). Its normal subgroup of order three fixes
exactly two elements of Q, by counting orbits modulo three. This fixed
subgroup is normal in G, and a normal subgroup of order two is central.

The elementary-eight specialization supplies the central factor in the
order-forty-eight vertex of Aschbacher–Smith, F.6.5(v). It requires no
choice of a complement or involutory lift in the ambient group.
-/

open Subgroup

private theorem fixed_card_two_of_order_eight
    {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 8) (B : Subgroup (MulAut E)) (hB : Nat.card B = 3) :
    Nat.card (FixedPoints.subgroup B E) = 2 := by
  let F := FixedPoints.subgroup B E
  have hp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hmod := hp.card_modEq_card_fixedPoints E
  change Nat.card E % 3 = Nat.card F % 3 at hmod
  rw [hE] at hmod
  have hdiv : Nat.card F ∣ 8 := hE ▸ F.card_subgroup_dvd_card
  have hproper : Nat.card F ≠ 8 := by
    intro hh
    have htop : F = ⊤ := F.eq_top_of_card_eq (hh.trans hE.symm)
    have hbot : B = ⊥ := by
      apply eq_bot_iff.mpr
      intro b hb
      apply mem_bot.mpr
      apply MulEquiv.ext
      intro x
      have hx : x ∈ F := htop ▸ mem_top x
      exact hx ⟨b, hb⟩
    rw [hbot, card_bot] at hB
    omega
  have hmem := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  have hdivs : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  change Nat.card F = 2
  omega

/-- A self-centralizing normal abelian eight of index six has ambient center of order two. -/
public theorem card_center_eq_two_of_abelian_eight_index_six
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] [IsMulCommutative Q]
    (hQ : Nat.card Q = 8) (hcent : centralizer (Q : Set G) ≤ Q)
    (hindex : Q.index = 6) :
    Nat.card (center G) = 2 := by
  classical
  let ρ : G →* MulAut Q := MulAut.conjNormal
  have hker : ρ.ker = Q := by
    apply le_antisymm
    · intro x hx
      apply hcent
      intro d hd
      have hh := congrArg (fun f : MulAut Q => (f ⟨d, hd⟩ : G))
        (MonoidHom.mem_ker.mp hx)
      change x * d * x⁻¹ = d at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro x hx
      apply MonoidHom.mem_ker.mpr
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      change x * (d : G) * x⁻¹ = d
      rw [(Q.le_centralizer hx d d.property).symm, mul_inv_cancel_right]
  let R := ρ.range
  have hR : Nat.card R = 6 := by
    rw [← index_ker, hker, hindex]
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := R) 3 (by rw [hR]; decide)
  let B₀ : Subgroup R := zpowers c
  have hB₀ : Nat.card B₀ = 3 := (Nat.card_zpowers c).trans hc
  have hindexB₀ : B₀.index = 2 := by
    have hh := B₀.card_mul_index
    rw [hB₀, hR] at hh
    omega
  let : B₀.Normal := B₀.normal_of_index_eq_two hindexB₀
  let B : Subgroup (MulAut Q) := B₀.map R.subtype
  have hB : Nat.card B = 3 := by
    rw [card_map_of_injective R.subtype_injective, hB₀]
  have hRB : R ≤ normalizer (B : Set (MulAut Q)) := by
    have hh := B₀.le_normalizer_map R.subtype
    intro a ha
    apply hh
    exact ⟨⟨a, ha⟩, B₀.normalizer_eq_top ▸ mem_top _, rfl⟩
  let F := FixedPoints.subgroup B Q
  let : IsInvariant R Q F := fixedPoints_isInvariant_of_normalizing_actor R B hRB
  let Z : Subgroup G := F.map Q.subtype
  have hZ : Nat.card Z = 2 := by
    rw [card_map_of_injective Q.subtype_injective]
    exact fixed_card_two_of_order_eight hQ B hB
  have hZnormal : Z.Normal := by
    constructor
    rintro x ⟨y, hy, rfl⟩ g
    refine ⟨ρ g y, ?_, rfl⟩
    exact (IsInvariant.invariant (A := R) (G := Q) (H := F)
      ⟨ρ g, ⟨g, rfl⟩⟩ y).mp hy
  let : Z.Normal := hZnormal
  have hCZ : center G ≤ Z := by
    intro x hx
    have hxQ : x ∈ Q := hcent ((center_le_centralizer (Q : Set G)) hx)
    refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
    intro b
    have hbR : (b : MulAut Q) ∈ R := map_subtype_le B₀ b.property
    obtain ⟨g, hg⟩ := hbR
    apply Subtype.ext
    change ((b : MulAut Q) ⟨x, hxQ⟩ : G) = x
    rw [← hg]
    change g * x * g⁻¹ = x
    rw [mem_center_iff.mp hx g, mul_inv_cancel_right]
  rwa [le_antisymm hCZ (central_of_normal_card_two Z hZ)]

/-- A self-centralizing normal abelian eight of index six contains a central involution. -/
public theorem exists_central_card_two_of_abelian_eight_index_six
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] [IsMulCommutative Q]
    (hQ : Nat.card Q = 8) (hcent : centralizer (Q : Set G) ≤ Q)
    (hindex : Q.index = 6) :
    ∃ Z : Subgroup G, Nat.card Z = 2 ∧ Z ≤ Q ∧ Z ≤ center G := by
  exact ⟨center G, card_center_eq_two_of_abelian_eight_index_six Q hQ hcent hindex,
    (center_le_centralizer (Q : Set G)).trans hcent, le_rfl⟩

/-- An elementary-eight kernel of a faithful S₃ conjugation action contains a central line. -/
public theorem exists_central_card_two_of_elementary_eight_symmetric_three
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] [IsElementaryAbelian 2 Q]
    (hQ : Nat.card Q = 8) (hcent : centralizer (Q : Set G) ≤ Q)
    (hquot : Nonempty (G ⧸ Q ≃* Equiv.Perm (Fin 3))) :
    ∃ Z : Subgroup G, Nat.card Z = 2 ∧ Z ≤ Q ∧ Z ≤ center G := by
  obtain ⟨e⟩ := hquot
  have hindex : Q.index = 6 := by
    change Nat.card (G ⧸ Q) = 6
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact exists_central_card_two_of_abelian_eight_index_six Q hQ hcent hindex
