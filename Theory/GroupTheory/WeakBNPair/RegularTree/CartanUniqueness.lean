module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentSeparation
public import Theory.GroupTheory.Hall.Basic
public import Mathlib.Tactic.Group

/-!
# Uniqueness of the apartment from Hall path stabilizers

The normalizer of a line acts transitively on its vertices in each ambient
orbit and on the two neighbors of each vertex. Consequently it aligns two
paths of the same length. A common path in two translated apartments then
reduces their comparison to its pointwise stabilizer.

If that stabilizer is a pi-group and contains the Hall pi-Cartan of an edge
stabilizer, it equals the Cartan. This proves apartment uniqueness without
assuming uniqueness, exchange, or a quotient BN-pair. Finite vertex
stabilizers suffice; the acting group may be infinite.

Source: DGS, *Groups and Graphs* (1985), Part II, (14.1)(a), (14.10),
printed pp.210,216–217; the line symmetries are those of (3.5), p.75.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {X V : Type*} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {T : Set V}

/-- The pointwise stabilizer of a path, including both endpoints. -/
def pathFixer {a b : V} (p : Γ.Walk a b) : Subgroup X where
  carrier := {g | ∀ k ≤ p.length, g • p.getVert k = p.getVert k}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy k hk
    rw [mul_smul, hy k hk, hx k hk]
  inv_mem' := by
    intro x hx k hk
    rw [inv_smul_eq_iff, hx k hk]

/-- The two elementary transitivity properties of the dihedral apartment
normalizer: vertices of the same ambient orbit and the two neighbors at a
vertex. Neither property concerns distinct apartments. -/
structure ApartmentSymmetries (Γ : SimpleGraph V) (T : Set V) (N : Subgroup X) : Prop where
  preserves : ∀ g ∈ N, ∀ a ∈ T, g • a ∈ T
  vertices : ∀ a ∈ T, ∀ b ∈ T, (∃ g : X, g • a = b) → ∃ n ∈ N, n • a = b
  neighbors : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, Γ.Adj a b → Γ.Adj a c →
    ∃ n ∈ N, n • a = a ∧ n • b = c

namespace ApartmentSymmetries
variable {N : Subgroup X} (d : ApartmentSymmetries Γ T N)
include d

/-- In an apartment of valence two the initial edge determines the path.
The normalizer can align that edge, hence every vertex of two equal-length
paths whose initial vertices lie in the same ambient orbit. -/
theorem align_paths
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T)
    {a b c e : V} (p : Γ.Walk a b) (q : Γ.Walk c e)
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length = q.length)
    (hpT : ∀ z ∈ p.support, z ∈ T) (hqT : ∀ z ∈ q.support, z ∈ T)
    (horbit : ∃ g : X, g • a = c) :
    ∃ n ∈ N, ∀ k ≤ p.length, n • p.getVert k = q.getVert k := by
  obtain ⟨m, hm, hma⟩ := d.vertices a (hpT _ p.start_mem_support)
    c (hqT _ q.start_mem_support) horbit
  by_cases hzero : p.length = 0
  · refine ⟨m, hm, ?_⟩
    intro k hk
    have : k = 0 := by omega
    subst k
    simpa only [getVert_zero] using hma
  have hp1 : Γ.Adj a (p.getVert 1) := by
    simpa only [getVert_zero] using p.adj_getVert_succ (by omega : 0 < p.length)
  have hq1 : Γ.Adj c (q.getVert 1) := by
    simpa only [getVert_zero] using q.adj_getVert_succ (by omega : 0 < q.length)
  obtain ⟨t, ht, htc, ht1⟩ := d.neighbors c (hqT _ q.start_mem_support)
    (m • p.getVert 1) (d.preserves m hm _ (hpT _ (p.getVert_mem_support 1)))
    (q.getVert 1) (hqT _ (q.getVert_mem_support 1))
    (by simpa only [hma] using hact m hp1) hq1
  refine ⟨t * m, N.mul_mem ht hm, ?_⟩
  have hpres : ∀ z ∈ T, (t * m) • z ∈ T := d.preserves _ (N.mul_mem ht hm)
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro _; simpa only [getVert_zero, mul_smul, hma] using htc
  | one => intro _; simpa only [mul_smul] using ht1
  | more k ih₀ ih₁ =>
    intro hk
    have hk₀ : k ≤ p.length := by omega
    have hk₁ : k+1 ≤ p.length := by omega
    have he₀ := ih₀ hk₀
    have he₁ := ih₁ hk₁
    have hback : Γ.Adj (q.getVert (k+1)) ((t*m) • p.getVert k) := by
      rw [← he₁]
      exact hact _ (p.adj_getVert_succ (by omega : k < p.length)).symm
    have hnext : Γ.Adj (q.getVert (k+1)) ((t*m) • p.getVert (k+2)) := by
      rw [← he₁]
      exact hact _ (p.adj_getVert_succ (by omega : k+1 < p.length))
    have hother := q.adj_getVert_succ (by omega : k+1 < q.length)
    have hne : (t*m) • p.getVert k ≠ (t*m) • p.getVert (k+2) := by
      intro he
      have := hp.getVert_injOn hk₀ hk ((MulAction.toPerm (t*m)).injective he)
      omega
    rcases hline _ (hqT _ (q.getVert_mem_support (k+1)))
      _ (hpres _ (hpT _ (p.getVert_mem_support k)))
      _ (hpres _ (hpT _ (p.getVert_mem_support (k+2))))
      _ (hqT _ (q.getVert_mem_support (k+2))) hback hnext hother hne with he | he
    · rw [he₀] at he
      have := hq.getVert_injOn (by omega : k+2 ≤ q.length) (by omega : k ≤ q.length) he
      omega
    · exact he.symm

/-- Once every length-s stabilizer inside the chosen apartment lies in its
normalizer, aligning a common s-path forces equality of two apartments. -/
theorem unique_of_pathFixer_le
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T) (s : ℕ)
    (hfix : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length = s →
      (∀ z ∈ p.support, z ∈ T) → pathFixer (X := X) p ≤ N) :
    ApartmentsUnique (X := X) Γ T s := by
  intro a b p hp hlen g h hg hh
  let f : Γ →g Γ := ⟨fun z => g⁻¹ • z, fun hadj => hact _ hadj⟩
  let f' : Γ →g Γ := ⟨fun z => h⁻¹ • z, fun hadj => hact _ hadj⟩
  have hqT : ∀ z ∈ (p.map f).support, z ∈ T := by
    intro z hz
    rw [Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨v, hv, he⟩ := hg w hw
    change g⁻¹ • w ∈ T
    rw [← he, inv_smul_smul]
    exact hv
  have hrT : ∀ z ∈ (p.map f').support, z ∈ T := by
    intro z hz
    rw [Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨v, hv, he⟩ := hh w hw
    change h⁻¹ • w ∈ T
    rw [← he, inv_smul_smul]
    exact hv
  have hq : (p.map f).IsPath := hp.map (MulAction.toPerm g⁻¹).injective
  have hr : (p.map f').IsPath := hp.map (MulAction.toPerm h⁻¹).injective
  obtain ⟨n, hn, he⟩ := d.align_paths hact hline (p.map f) (p.map f') hq hr
    (by simp only [length_map]) hqT hrT ⟨h⁻¹*g, by simp [f, f', mul_smul]⟩
  have hz : n⁻¹*h⁻¹*g ∈ pathFixer (X := X) (p.map f) := by
    intro k hk
    have he' := he k hk
    simp only [getVert_map] at he'
    change n • (g⁻¹ • p.getVert k) = h⁻¹ • p.getVert k at he'
    rw [getVert_map]
    change (n⁻¹*h⁻¹*g) • (g⁻¹ • p.getVert k) = g⁻¹ • p.getVert k
    rw [mul_smul, mul_smul, smul_inv_smul, ← he', inv_smul_smul]
  have hzN := hfix (p.map f) hq (by simpa only [length_map] using hlen) hqT hz
  have hng : h⁻¹*g ∈ N := by
    have hmem := N.mul_mem hn hzN
    convert hmem using 1; group
  apply Set.ext
  intro v
  constructor
  · rintro ⟨z, hzT, rfl⟩
    exact ⟨(h⁻¹*g) • z, d.preserves _ hng z hzT, by simp [mul_smul]⟩
  · rintro ⟨z, hzT, rfl⟩
    have hinv : g⁻¹*h ∈ N := by simpa only [mul_inv_rev, inv_inv] using N.inv_mem hng
    exact ⟨(g⁻¹*h) • z, d.preserves _ hinv z hzT, by simp [mul_smul]⟩
end ApartmentSymmetries

/-- A pi-subgroup containing a Hall pi-subgroup equals it. -/
theorem eq_hall_of_le_pi {Y : Type*} [Group Y] [Finite Y] {π : Set Nat.Primes}
    {K H : Subgroup Y} (hK : IsHallSubgroup π K) (hH : IsPiSubgroup π H) (hKH : K ≤ H) :
    H = K := by
  have hHall : IsHallSubgroup π H := ⟨hH, fun p hp =>
    hK.p_in_pi_of_p_dvd_index p (hp.trans (Subgroup.index_dvd_of_le hKH))⟩
  exact (hK.eq_of_le hHall hKH).symm

/-- Odd s-path stabilizers equal the Hall Cartan, rather than merely
containing it. This is the counting step used in DGS (14.10). -/
theorem pathFixer_eq_cartan {π : Set Nat.Primes} (K : Subgroup X)
    (hK : ∀ k ∈ K, ∀ a ∈ T, k • a = a)
    (hHall : ∀ a ∈ T, ∀ b ∈ T, Γ.Adj a b →
      IsHallSubgroup π (K.subgroupOf (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b)))
    (hfinite : ∀ a : V, Finite (MulAction.stabilizer X a))
    {a b : V} (p : Γ.Walk a b) (hpos : 0 < p.length)
    (hpT : ∀ z ∈ p.support, z ∈ T) (hpi : IsPiSubgroup π (pathFixer (X := X) p)) :
    pathFixer (X := X) p = K := by
  let E := MulAction.stabilizer X a ⊓ MulAction.stabilizer X (p.getVert 1)
  have hFE : pathFixer (X := X) p ≤ E := by
    intro x hx
    refine ⟨?_, hx 1 (by omega)⟩
    change x • a = a
    simpa only [getVert_zero] using hx 0 (by omega)
  have hKF : K ≤ pathFixer (X := X) p := fun x hx k _ =>
    hK x hx _ (hpT _ (p.getVert_mem_support k))
  let := hfinite a
  let : Finite E := Finite.of_injective (Subgroup.inclusion (show E ≤ MulAction.stabilizer X a from inf_le_left))
    (Subgroup.inclusion_injective _)
  have hKE := hHall a (hpT _ p.start_mem_support) (p.getVert 1)
    (hpT _ (p.getVert_mem_support 1)) (by simpa only [getVert_zero] using p.adj_getVert_succ hpos)
  have hpi' : IsPiSubgroup π ((pathFixer (X := X) p).subgroupOf E) := by
    intro q hq
    apply hpi q
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv] at hq
  have he := eq_hall_of_le_pi hKE hpi' (Subgroup.subgroupOf_mono E hKF)
  apply le_antisymm _ hKF
  intro x hx
  have hm : (⟨x, hFE hx⟩ : E) ∈ (pathFixer (X := X) p).subgroupOf E := hx
  rw [he] at hm
  exact hm

/-- The uniqueness argument of DGS (14.10), with the earlier local path
stabilizers and Cartan construction kept as genuine input. -/
theorem apartmentsUnique_of_hall_pathFixers
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T) (s : ℕ) (hs : 0 < s)
    (K N : Subgroup X) (hKN : K ≤ N) (d : ApartmentSymmetries Γ T N)
    {π : Set Nat.Primes} (hK : ∀ k ∈ K, ∀ a ∈ T, k • a = a)
    (hHall : ∀ a ∈ T, ∀ b ∈ T, Γ.Adj a b →
      IsHallSubgroup π (K.subgroupOf (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b)))
    (hfinite : ∀ a : V, Finite (MulAction.stabilizer X a))
    (hpi : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length = s →
      IsPiSubgroup π (pathFixer (X := X) p)) :
    ApartmentsUnique (X := X) Γ T s := by
  apply d.unique_of_pathFixer_le hact hline s
  intro a b p hp hlen hpT
  rw [pathFixer_eq_cartan K hK hHall hfinite p (by omega) hpT (hpi p hp hlen)]
  exact hKN
/-- An automorphism of a line fixing an edge fixes every path in the line
starting with that edge. This does not require a faithful ambient action. -/
theorem fixes_path_of_fixes_first_edge
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hline : NoBranchingIn Γ T) {a b : V} (p : Γ.Walk a b) (hp : p.IsPath)
    (hpT : ∀ z ∈ p.support, z ∈ T) {x : X} (hpres : ∀ z ∈ T, x • z ∈ T)
    (ha : x • a = a) (hb : x • p.getVert 1 = p.getVert 1) :
    x ∈ pathFixer (X := X) p := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro _; simpa only [getVert_zero] using ha
  | one => intro _; exact hb
  | more k ih₀ ih₁ =>
    intro hk
    have hk₀ : k ≤ p.length := by omega
    have hk₁ : k+1 ≤ p.length := by omega
    have he₀ := ih₀ hk₀
    have he₁ := ih₁ hk₁
    have hback := (p.adj_getVert_succ (by omega : k < p.length)).symm
    have hnext := p.adj_getVert_succ (by omega : k+1 < p.length)
    have hother : Γ.Adj (p.getVert (k+1)) (x • p.getVert (k+2)) := by
      simpa only [he₁] using hact x hnext
    have hne : p.getVert k ≠ p.getVert (k+2) := by
      intro he
      have := hp.getVert_injOn hk₀ hk he
      omega
    rcases hline _ (hpT _ (p.getVert_mem_support (k+1)))
      _ (hpT _ (p.getVert_mem_support k)) _ (hpT _ (p.getVert_mem_support (k+2)))
      _ (hpres _ (hpT _ (p.getVert_mem_support (k+2)))) hback hnext hother hne with he | he
    · rw [← he₀] at he
      exact (hne ((MulAction.toPerm x).injective he).symm).elim
    · exact he
end Theory.GroupTheory.WeakBNPair.RegularTree
