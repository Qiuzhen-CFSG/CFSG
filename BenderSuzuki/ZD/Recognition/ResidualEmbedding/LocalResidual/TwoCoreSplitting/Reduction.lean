module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.Pair
public import Theory.GroupTheory.Involution.OddRotation
public import BenderSuzuki.SE.Theorem4

/-!
# Numerical inputs and the distinguished part of the two-core

GLS, Volume 4, Chapter 2, Lemmas 17.1–17.5 give the square degree and
an odd-order element inverted by an involution of the two-point stabilizer.
`TwoCoreCountingData` states those outstanding obligations, not a theorem
asserting their existence. In particular the centralizer-order ratio in
(17D) is rational; no divisibility assertion about that ratio is made here.

The first paragraph of Proposition 17.6 is proved below: if the degree is
one more than a power of two, a distinguished involution belongs to the
two-core. Otherwise Baer–Suzuki supplies an inverted odd-prime-order
subgroup. The action theorem makes its fixed-coset set a singleton,
contradicting the fixed-point congruence. Two-centrality then puts the
local distinguished closure in the center of the two-core.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The Baer–Suzuki step of Proposition 17.6, conditional only on the
numerical degree supplied by the preceding counting argument. -/
public theorem distinguished_mem_twoCore_of_binary_degree
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    {n : ℕ} (hdegree : Nat.card (G ⧸ M) = 2 ^ n + 1)
    {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M) :
    (⟨z, hzM⟩ : M) ∈ pCore 2 M := by
  classical
  by_contra hzcore
  obtain ⟨p, hp, hp2, x, hxorder, hinv⟩ :=
    involution_outside_twoCore_inverts_odd_prime (⟨z, hzM⟩ : M)
      (BenderSuzuki.IsInvolution.subtype (h.involutions z hzZ) hzM) hzcore
  let W := Subgroup.zpowers (x : G)
  have hxp : orderOf (x : G) = p := by simpa using hxorder
  have hWodd : Odd (Nat.card W) := by
    simpa [W, Nat.card_zpowers, hxp] using hp.odd_of_ne_two hp2
  have hWM : W ≤ M := Subgroup.zpowers_le.mpr x.property
  have hinvG : z * (x : G) * z⁻¹ = (x : G)⁻¹ := by
    have hh := congrArg Subtype.val hinv
    simpa [rightConjugateElem, (h.involutions z hzZ).inv_eq_self] using hh
  have hzNorm : z ∈ Subgroup.normalizer (W : Set G) :=
    theorem4b_mem_normalizer_zpowers_of_inverts (h.involutions z hzZ) hinvG
  have hnot : ¬ W ≤ Subgroup.centralizer ({z} : Set G) := by
    intro hle
    have hc := Subgroup.mem_centralizer_singleton_iff.mp
      (hle (Subgroup.mem_zpowers (x : G)))
    have heq : (x : G) = (x : G)⁻¹ := by
      calc
        (x : G) = z * (x : G) * z⁻¹ := by rw [← hc]; simp
        _ = (x : G)⁻¹ := hinvG
    have hsquare : (x : G) ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [heq]
      exact inv_mul_cancel _
    have hpdvd : p ∣ 2 := hxp ▸ orderOf_dvd_of_pow_eq_one hsquare
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hpdvd |>.resolve_left hp.ne_one)
  have hfix := (ha.odd_normalizer z hzZ hzM W hWodd hWM hzNorm).resolve_left hnot
  have hWpg : IsPGroup p W := IsPGroup.of_card (n := 1) (by simp [W, Nat.card_zpowers, hxp])
  have hone : Nat.card (MulAction.fixedPoints W (G ⧸ M)) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    have hbase : QuotientGroup.mk (s := M) 1 ∈ MulAction.fixedPoints W (G ⧸ M) := by
      intro w
      change (w : G) • QuotientGroup.mk (s := M) (1 : G) = QuotientGroup.mk (s := M) (1 : G)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
      simpa using M.inv_mem (hWM w.property)
    refine ⟨⟨_, hbase⟩, ?_⟩
    intro beta
    apply Subtype.ext
    apply hfix
    intro w hw
    exact beta.property ⟨w, hw⟩
  let : Fact p.Prime := ⟨hp⟩
  have hmod := hWpg.card_modEq_card_fixedPoints (G ⧸ M)
  rw [hone, hdegree] at hmod
  have hdvd : p ∣ 2 ^ n := by
    have hh : Nat.ModEq p (2 ^ n) 0 := Nat.ModEq.add_right_cancel' 1 (by simpa using hmod)
    exact Nat.modEq_zero_iff_dvd.mp hh
  exact hp2 ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd) |>.resolve_left hp.ne_one)


/-- Two-centrality and unique conjugate membership imply centralization
of the internal two-core, without using the counting argument. -/
public theorem distinguished_centralizes_twoCore
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M) :
    ∀ x : pCore 2 M, Commute (⟨z, hzM⟩ : M) (x : M) := by
  obtain ⟨S, _, hS⟩ := r.two_central z hzZ
  have hSM : (S : Subgroup G) ≤ M := by
    intro s hs
    exact mem_of_commute h hzZ hzM (hS ⟨s, hs⟩)
  have hcore : pCore 2 M ≤ (S.subtype hSM : Subgroup M) :=
    IsPGroup.le_sylow_of_normal pCore_isPGroup (S.subtype hSM)
  intro x
  have hxS : ((x : M) : G) ∈ (S : Subgroup G) := hcore x.property
  apply Subtype.ext
  exact (hS ⟨x, hxS⟩).eq

/-- The local circle is a central subgroup of the two-core after the
binary-degree conclusion. It is generation by distinguished involutions. -/
public theorem localClosure_le_twoCore_inf_centralizer_of_binary_degree
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {n : ℕ}
    (hdegree : Nat.card (G ⧸ M) = 2 ^ n + 1) :
    Subgroup.closure (M.subtype ⁻¹' Z) ≤
      pCore 2 M ⊓ Subgroup.centralizer (pCore 2 M : Set M) := by
  rw [Subgroup.closure_le]
  intro z hz
  refine ⟨distinguished_mem_twoCore_of_binary_degree h ha hdegree hz z.property, ?_⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  exact (distinguished_centralizes_twoCore h r hz z.property ⟨x, hx⟩).eq.symm

/-- The numerical and inverter outputs needed from Sections 16–17.
This is an explicit prerequisite interface. Its existence must be proved
using actual local model isomorphisms and all of their source hypotheses. -/
public structure TwoCoreCountingData (Z : Set G) (M : Subgroup G) where
  q : ℕ
  one_lt : 1 < q
  binary : ∃ n : ℕ, q = 2 ^ n
  t : G
  t_mem : t ∈ Z
  t_not_mem : t ∉ M
  degree : Nat.card (G ⧸ M) = q ^ 2 + 1
  pair_index : (residualPairIn M t).index = q ^ 2
  u : residualPairIn M t
  u_order : orderOf u = 2
  commutes_t : Commute ((u : M) : G) t
  z : M
  z_mem : (z : G) ∈ Z
  commutes_z : Commute ((u : M) : G) (z : G)
  linear_centralizer : ∃ n : ℕ, q = 2 ^ n ∧ Nonempty
    ((Subgroup.closure
      ((Subgroup.centralizer ({((u : M) : G)} : Set G)).subtype ⁻¹' Z)) ≃*
        MatrixGroups.PSL2BinaryMatrixGroup n)
  x : M
  x_odd : Odd (orderOf x)
  x_ne : x ≠ 1
  inverts : (u : M) * x * (u : M)⁻¹ = x⁻¹

omit [Finite G] in
/-- The source square degree implies the binary degree required by the
Baer–Suzuki argument; the exponent is doubled. -/
public theorem TwoCoreCountingData.binary_degree (d : TwoCoreCountingData Z M) :
    ∃ n : ℕ, Nat.card (G ⧸ M) = 2 ^ n + 1 := by
  obtain ⟨n, hn⟩ := d.binary
  exact ⟨n * 2, by rw [d.degree, hn, pow_mul]⟩

end BenderSuzuki.ZD
