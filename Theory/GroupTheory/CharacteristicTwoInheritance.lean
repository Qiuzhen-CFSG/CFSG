module

public import Theory.GroupTheory.Commutator.PTimesQ
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Characteristic p in local subgroups

Suppose the p-core Q of a finite group M contains its centralizer. A subgroup
N inherits this property if C_Q(O_p(N)) lies in N. This centralizer is a
normal p-subgroup of N and hence lies in O_p(N). If a prime-order element
of C_N(O_p(N)) has order different from p, the P × Q centralizer theorem
makes it centralize Q. Characteristic p in M then puts it in Q, a
contradiction. Cauchy's theorem and normality finish the core containment.

This criterion gives every subgroup between X C_M(X) and N_M(X), for a
p-subgroup X. Normal inheritance gives C_M(X). Induction through an ordered
finite family gives the corresponding intersection of normalizers; a later
subgroup is only required to normalize the earlier ones.

All embedded cores are images of intrinsic cores. In particular N need not
be normal in M in the centralizer criterion. The intrinsic normalizer form
is also exported for applications that work inside subgroup types.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemmas 1.1.3 and 1.1.4(4), printed pp.500–501.
The argument works for every prime, using the proved coprime P × Q theorem
instead of the full residual Thompson A × B theorem cited in the source.
-/

namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}

private theorem core_normalizes (H : Subgroup G) :
    H ≤ normalizer (H.pCoreIn p : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  exact mem_map.mpr ⟨⟨g, hg⟩ * y * (⟨g, hg⟩ : H)⁻¹,
    (inferInstance : (pCore p H).Normal).conj_mem y hy ⟨g, hg⟩, rfl⟩

private theorem normalizes_centralizer (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (centralizer (X : Set G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance

private theorem intrinsic_iff_ambient (H : Subgroup G) :
    centralizer (pCore p H : Set H) ≤ pCore p H ↔
      H ⊓ centralizer (H.pCoreIn p : Set G) ≤ H.pCoreIn p := by
  constructor
  · intro h x hx
    have hc : (⟨x, hx.1⟩ : H) ∈ centralizer (pCore p H : Set H) := by
      intro y hy
      apply Subtype.ext
      exact mem_centralizer_iff.mp hx.2 y (mem_map.mpr ⟨y, hy, rfl⟩)
    exact mem_map.mpr ⟨⟨x, hx.1⟩, h hc, rfl⟩
  · intro h x hx
    have hc : (x : G) ∈ centralizer (H.pCoreIn p : Set G) := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hy
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx a ha)
    obtain ⟨y, hy, he⟩ := mem_map.mp (h ⟨x.property, hc⟩)
    exact (Subtype.ext he : y = x) ▸ hy

variable [Finite G] [Fact p.Prime]

private theorem prime_order_core_centralizer
    {M N : Subgroup G}
    (hM : M ⊓ centralizer (M.pCoreIn p : Set G) ≤ M.pCoreIn p)
    (hNM : N ≤ M)
    (hR : M.pCoreIn p ⊓ centralizer (N.pCoreIn p : Set G) ≤ N.pCoreIn p)
    (x : N) (hx : x ∈ centralizer (pCore p N : Set N))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (ho : orderOf x = q) : False := by
  let P := N.pCoreIn p
  let Q := M.pCoreIn p
  let A := zpowers (x : G)
  have hAN : A ≤ N := zpowers_le.mpr x.property
  have hxP : (x : G) ∈ centralizer (P : Set G) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_map (f := N.subtype) (K := pCore p N)).mp hy
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx a ha)
  have hAP : A ≤ centralizer (P : Set G) := zpowers_le.mpr hxP
  have hPA : P ≤ centralizer (A : Set G) := le_centralizer_iff.mp hAP
  have hAcard : Nat.card A = q := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ho]
  have hAcop : Nat.Coprime p (Nat.card A) := by
    rw [hAcard]
    exact ((hq.coprime_iff_not_dvd).mpr
      (fun hd => hqp ((Nat.dvd_prime Fact.out).mp hd |>.resolve_left hq.ne_one))).symm
  have hQA : ⁅Q, A⁆ = ⊥ := p_times_q_centralizer P A Q
    (isPGroup_pCoreIn p N) (isPGroup_pCoreIn p M) hAcop
    ((pCoreIn_le p N).trans (hNM.trans (core_normalizes M)))
    (hAN.trans (hNM.trans (core_normalizes M)))
    (commutator_eq_bot_iff_le_centralizer.mpr hPA) (hR.trans hPA)
  have hxQ : (x : G) ∈ Q := hM ⟨hNM x.property,
    (commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm] : ⁅A, Q⁆ = ⊥))
      (mem_zpowers _)⟩
  obtain ⟨n, hn⟩ := (isPGroup_pCoreIn p M).exists_orderOf_dvd_pow ⟨x, hxQ⟩
  have hd : q ∣ p ^ n := by
    simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe x, ho] using hn
  exact hqp ((Nat.dvd_prime Fact.out).mp (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one)

/-- A subgroup N inherits characteristic p from M when C_{O_p(M)}(O_p(N))
lies in N. Normality of N in M is not required. -/
public theorem pCoreIn_selfCentralizing_of_core_centralizer_le {M N : Subgroup G}
    (hM : M ⊓ centralizer (M.pCoreIn p : Set G) ≤ M.pCoreIn p)
    (hNM : N ≤ M)
    (hR : M.pCoreIn p ⊓ centralizer (N.pCoreIn p : Set G) ≤ N) :
    N ⊓ centralizer (N.pCoreIn p : Set G) ≤ N.pCoreIn p := by
  have hRcore : M.pCoreIn p ⊓ centralizer (N.pCoreIn p : Set G) ≤ N.pCoreIn p :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn p M).to_le inf_le_left) hR
      ((le_inf (hNM.trans (core_normalizes M))
        ((core_normalizes N).trans (normalizes_centralizer _))).trans
          inf_normalizer_le_normalizer_inf)
  apply (intrinsic_iff_ambient N).mp
  let C := centralizer (pCore p N : Set N)
  have hCp : IsPGroup p C := by
    apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
    intro q hq
    obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    by_cases he : q = p
    · subst q
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩
    · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) q (hp := ⟨hqprime⟩) hqdvd
      exact (prime_order_core_centralizer hM hNM hRcore x x.property hqprime he
        (by simpa only [Subgroup.orderOf_coe] using hx)).elim
  exact le_sSup ⟨inferInstance, hCp⟩

/-- Characteristic p passes to relatively subnormal subgroups, with both
cores viewed in their common ambient group. -/
public theorem pCoreIn_selfCentralizing_of_subnormal {M N : Subgroup G}
    (hM : M ⊓ centralizer (M.pCoreIn p : Set G) ≤ M.pCoreIn p)
    (hNM : N ≤ M) (hn : (N.subgroupOf M).IsSubnormal) :
    N ⊓ centralizer (N.pCoreIn p : Set G) ≤ N.pCoreIn p := by
  apply (intrinsic_iff_ambient N).mp
  exact (Theory.Quasithin.centralizer_pCore_le_iff p (subgroupOfEquivOfLe hNM)).mp
    (subnormal_core_selfCentralizing ((intrinsic_iff_ambient M).mpr hM)
      (N.subgroupOf M) hn)

/-- Every subgroup between X C_M(X) and N_M(X) inherits characteristic p
from M, for a p-subgroup X. -/
public theorem pCoreIn_selfCentralizing_of_normalizer_sandwich {M X H : Subgroup G}
    (hM : M ⊓ centralizer (M.pCoreIn p : Set G) ≤ M.pCoreIn p)
    (hXp : IsPGroup p X) (hXH : X ≤ H)
    (hCH : M ⊓ centralizer (X : Set G) ≤ H)
    (hHM : H ≤ M) (hHN : H ≤ normalizer (X : Set G)) :
    H ⊓ centralizer (H.pCoreIn p : Set G) ≤ H.pCoreIn p := by
  apply pCoreIn_selfCentralizing_of_core_centralizer_le hM hHM
  exact (inf_le_inf (pCoreIn_le p M)
    (centralizer_le (le_pCoreIn_of_normalizes hXp hXH hHN))).trans hCH

/-- The relative normalizer of a p-subgroup inherits characteristic p. -/
public theorem pCoreIn_selfCentralizing_normalizer {M X : Subgroup G}
    (hM : M ⊓ centralizer (M.pCoreIn p : Set G) ≤ M.pCoreIn p)
    (hXp : IsPGroup p X) (hXM : X ≤ M) :
    let N := M ⊓ normalizer (X : Set G)
    N ⊓ centralizer (N.pCoreIn p : Set G) ≤ N.pCoreIn p := by
  exact pCoreIn_selfCentralizing_of_normalizer_sandwich hM hXp
    (le_inf hXM X.le_normalizer) (inf_le_inf_left M (centralizer_le_normalizer _))
    inf_le_left inf_le_right

/-- The relative centralizer of a p-subgroup inherits characteristic p,
by normality inside its relative normalizer. -/
public theorem pCoreIn_selfCentralizing_centralizer {M X : Subgroup G}
    (hM : M ⊓ centralizer (M.pCoreIn p : Set G) ≤ M.pCoreIn p)
    (hXp : IsPGroup p X) (hXM : X ≤ M) :
    let C := M ⊓ centralizer (X : Set G)
    C ⊓ centralizer (C.pCoreIn p : Set G) ≤ C.pCoreIn p := by
  let N := M ⊓ normalizer (X : Set G)
  let C := M ⊓ centralizer (X : Set G)
  have hCN : C ≤ N := inf_le_inf_left M (centralizer_le_normalizer _)
  have hn : (C.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCN).mpr
      ((le_inf (inf_le_left.trans M.le_normalizer)
        (inf_le_right.trans (normalizes_centralizer X))).trans
          inf_normalizer_le_normalizer_inf)
  exact pCoreIn_selfCentralizing_of_subnormal
      (pCoreIn_selfCentralizing_normalizer hM hXp hXM) hCN hn.isSubnormal

/-- In an ordered finite family, each later p-subgroup need only normalize
its predecessors. Their normalizer intersection inherits characteristic p. -/
public theorem pCoreIn_selfCentralizing_iInf_normalizer {M : Subgroup G}
    (hM : M ⊓ centralizer (M.pCoreIn p : Set G) ≤ M.pCoreIn p)
    {n : ℕ} (B : Fin n → Subgroup G) (hp : ∀ i, IsPGroup p (B i))
    (hBM : ∀ i, B i ≤ M)
    (hnorm : ∀ i j, i ≤ j → B j ≤ normalizer (B i : Set G)) :
    let H := M ⊓ ⨅ i, normalizer (B i : Set G)
    H ⊓ centralizer (H.pCoreIn p : Set G) ≤ H.pCoreIn p := by
  induction n with
  | zero => simpa using hM
  | succ n ih =>
    let K := M ⊓ ⨅ i : Fin n, normalizer (B i.castSucc : Set G)
    have hK : K ⊓ centralizer (K.pCoreIn p : Set G) ≤ K.pCoreIn p :=
      ih (fun i => B i.castSucc) (fun i => hp i.castSucc) (fun i => hBM i.castSucc)
        (fun i j hij => hnorm i.castSucc j.castSucc hij)
    have hBK : B (Fin.last n) ≤ K :=
      le_inf (hBM _) (le_iInf (fun i => hnorm i.castSucc _ (Fin.le_last _)))
    have he : (M ⊓ ⨅ i, normalizer (B i : Set G)) =
        K ⊓ normalizer (B (Fin.last n) : Set G) := by
      ext x
      simp only [mem_inf, mem_iInf]
      constructor
      · rintro ⟨hxM, hx⟩
        exact ⟨⟨hxM, mem_iInf.mpr (fun i => hx i.castSucc)⟩, hx (Fin.last n)⟩
      · rintro ⟨⟨hxM, hx⟩, hlast⟩
        exact ⟨hxM, fun i => Fin.lastCases hlast (fun j => mem_iInf.mp hx j) i⟩
    change (M ⊓ ⨅ i, normalizer (B i : Set G)) ⊓ _ ≤ _
    rw [he]
    exact pCoreIn_selfCentralizing_normalizer hK (hp _) hBK

/-- The normalizer of any p-subgroup of a group of characteristic p has
self-centralizing intrinsic p-core. -/
public theorem normalizer_core_selfCentralizing
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (X : Subgroup G) (hXp : IsPGroup p X) :
    centralizer (pCore p (normalizer (X : Set G)) : Set (normalizer (X : Set G))) ≤
      pCore p (normalizer (X : Set G)) := by
  have ht : (⊤ : Subgroup G).pCoreIn p = pCore p G :=
    pCore_map_iso p Subgroup.topEquiv
  have htop : (⊤ : Subgroup G) ⊓ centralizer ((⊤ : Subgroup G).pCoreIn p : Set G) ≤
      (⊤ : Subgroup G).pCoreIn p := by simpa only [ht, top_inf_eq] using hc
  apply (intrinsic_iff_ambient _).mpr
  simpa only [top_inf_eq] using pCoreIn_selfCentralizing_normalizer htop hXp le_top

end Subgroup
