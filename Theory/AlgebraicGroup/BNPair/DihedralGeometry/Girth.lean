module

public import Theory.AlgebraicGroup.BNPair.DihedralGeometry

/-!
# Girth of the octagonal BN-pair coset graph

Every simple cycle in the actual typed left-coset incidence graph has length
at least sixteen. An edge has a common group representative. At two consecutive
edges, their representatives differ by an element of the intervening parabolic;
nonbacktracking excludes the Borel and hence gives a simple Bruhat-cell factor.

The marking in `DihedralGroup 8` proves that alternating words of length at most
eight are reduced: an explicit function on the sixteen elements changes by at
most one under a simple reflection and takes the value `n` on such a word.
These finite identities are proved by kernel reduction, and shortest-word
induction transports the lower bound to the actual Weyl quotient.

Bruhat multiplication therefore puts eight alternating transitions in a cell
of length eight. The complementary transitions in a closed gallery must have
at least that length, by inversion and Bruhat-index uniqueness. Shorter galleries
of length at most eight are excluded directly. No apartment, metric, conjugacy,
or finiteness assumption is used.

Source: the BN-pair and standard-parabolic construction of GLS3 §§2.3 and 2.6,
`refs/KGroup/GLS3/chapter2.tex`.
-/

namespace Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open Subgroup
open scoped Pointwise

private def dihedralLength : DihedralGroup 8 → ℕ
  | .r k => 2 * min k.val (8 - k.val)
  | .sr k => if k.val = 0 then 1 else min (2 * k.val - 1) (17 - 2 * k.val)

private def dihedralSimple (b : Bool) : DihedralGroup 8 := .sr (if b then 1 else 0)

private def dihedralWord : Bool → ℕ → DihedralGroup 8
  | _, 0 => 1
  | b, n + 1 => dihedralSimple b * dihedralWord (!b) n

private lemma dihedralLength_simple_mul_le : ∀ (b : Bool) (w : DihedralGroup 8),
    dihedralLength (dihedralSimple b * w) ≤ dihedralLength w + 1 := by decide

private lemma dihedralLength_word : ∀ (b : Bool) (n : Fin 9),
    dihedralLength (dihedralWord b n) = n := by decide

private lemma dihedralLength_inv : ∀ w : DihedralGroup 8,
    dihedralLength w⁻¹ = dihedralLength w := by decide

variable {X I : Type*} [Group X] {T : TitsSystem (X := X)} {F : I → Subgroup X}
namespace OctagonalDatum
variable (D : OctagonalDatum T F)

private def alternatingWord : Bool → ℕ → T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N
  | _, 0 => 1
  | b, n + 1 => D.simple (D.typeEquiv.symm b) * alternatingWord (!b) n

private lemma map_alternatingWord (b : Bool) (n : ℕ) :
    D.weylEquiv (D.alternatingWord b n) = dihedralWord b n := by
  induction n generalizing b with
  | zero => simp [alternatingWord, dihedralWord]
  | succ n ih => simp [alternatingWord, dihedralWord, ih, D.map_simple, dihedralSimple]

private lemma dihedralLength_le_wordLength (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    dihedralLength (D.weylEquiv w) ≤ T.wordLength w := by
  obtain ⟨l, hlen, hl, rfl⟩ := T.wordLength_spec w
  rw [← hlen]
  clear hlen
  induction l with
  | nil => simp only [List.prod_nil, map_one, List.length_nil]; exact Nat.le_refl 0
  | cons s l ih =>
    obtain ⟨i, rfl⟩ := D.simple_range.symm ▸ hl s (by simp)
    have h := dihedralLength_simple_mul_le (D.typeEquiv i) (D.weylEquiv l.prod)
    simpa [List.prod_cons, D.map_simple, dihedralSimple] using
      h.trans (Nat.add_le_add_right (ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))) 1)

private lemma wordLength_alternatingWord_le (b : Bool) (n : ℕ) :
    T.wordLength (D.alternatingWord b n) ≤ n := by
  induction n generalizing b with
  | zero => simp [alternatingWord, T.wordLength_one]
  | succ n ih =>
    exact (T.wordLength_mul_left_le (D.simple_mem _) _).trans
      (Nat.add_le_add_right (ih (!b)) 1)

/-- Alternating marked simple words through length eight are reduced in the
actual Weyl quotient; no Coxeter-length certificate is assumed. -/
private lemma wordLength_alternatingWord (b : Bool) {n : ℕ} (hn : n ≤ 8) :
    T.wordLength (D.alternatingWord b n) = n := by
  apply le_antisymm (D.wordLength_alternatingWord_le b n)
  have h := D.dihedralLength_le_wordLength (D.alternatingWord b n)
  rwa [D.map_alternatingWord, dihedralLength_word b ⟨n, by omega⟩] at h

private lemma short_gallery_cell (g : ℕ → X) (t : ℕ → I) {n : ℕ} (hn : n ≤ 8)
    (hstep : ∀ k < n, (g k)⁻¹ * g (k + 1) ∈ T.bruhatCell (D.simple (t k)))
    (hflip : ∀ k, k + 1 < n → D.typeEquiv (t (k + 1)) = !(D.typeEquiv (t k))) :
    (g 0)⁻¹ * g n ∈ T.bruhatCell (D.alternatingWord (D.typeEquiv (t 0)) n) := by
  induction n generalizing g t with
  | zero => simp [alternatingWord, T.bruhatCell_one]
  | succ n ih =>
    have htail := ih (fun k => g (k + 1)) (fun k => t (k + 1)) (by omega)
      (fun k hk => hstep (k + 1) (by omega)) (fun k hk => hflip (k + 1) (by omega))
    have hindex : D.simple (t 0) * D.alternatingWord (D.typeEquiv (t 1)) n =
        D.alternatingWord (D.typeEquiv (t 0)) (n + 1) := by
      by_cases hz : n = 0
      · simp [hz, alternatingWord]
      · rw [hflip 0 (by omega)]
        simp [alternatingWord]
    have hlen : T.wordLength (D.alternatingWord (D.typeEquiv (t 1)) n) ≤
        T.wordLength (D.simple (t 0) * D.alternatingWord (D.typeEquiv (t 1)) n) := by
      rw [hindex, D.wordLength_alternatingWord _ hn,
        D.wordLength_alternatingWord _ (by omega : n ≤ 8)]
      omega
    rw [← hindex]
    apply T.bruhatCell_mul_bruhatCell_subset_of_wordLength_le (D.simple_mem _) _ hlen
    refine ⟨(g 0)⁻¹ * g 1, hstep 0 (by omega), (g 1)⁻¹ * g (n + 1), htail, ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left]

private lemma gallery_wordLength_le (g : ℕ → X) (t : ℕ → I) (n : ℕ)
    (hstep : ∀ k < n, (g k)⁻¹ * g (k + 1) ∈ T.bruhatCell (D.simple (t k))) :
    ∃ w, (g 0)⁻¹ * g n ∈ T.bruhatCell w ∧ T.wordLength w ≤ n := by
  induction n generalizing g t with
  | zero => exact ⟨1, by simp [T.bruhatCell_one], by rw [T.wordLength_one]⟩
  | succ n ih =>
    obtain ⟨w, hw, hlen⟩ := ih (fun k => g (k + 1)) (fun k => t (k + 1))
      (fun k hk => hstep (k + 1) (by omega))
    have hprod : (g 0)⁻¹ * g (n + 1) ∈ T.bruhatCell (D.simple (t 0)) * T.bruhatCell w := by
      refine ⟨(g 0)⁻¹ * g 1, hstep 0 (by omega), (g 1)⁻¹ * g (n + 1), hw, ?_⟩
      simp only [mul_assoc, mul_inv_cancel_left]
    rcases T.doubleCoset_mul_doubleCoset_subset_of_mem_S (D.simple_mem _) w hprod with h | h
    · exact ⟨D.simple (t 0) * w, h,
        (T.wordLength_mul_left_le (D.simple_mem _) w).trans (Nat.add_le_add_right hlen 1)⟩
    · exact ⟨w, h, by omega⟩

private lemma inv_mem_cell (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) {x : X}
    (hx : x ∈ T.bruhatCell w) : x⁻¹ ∈ T.bruhatCell w⁻¹ := by
  obtain ⟨y, hy, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨b₁, hb₁, n, ⟨nN, hnw, rfl⟩, rfl⟩ := Set.mem_mul.mp hy
  refine ⟨(b₂⁻¹ * (nN⁻¹ : T.N) : X), ?_, b₁⁻¹, T.B.inv_mem hb₁, ?_⟩
  · exact ⟨b₂⁻¹, T.B.inv_mem hb₂, (nN⁻¹ : T.N),
      ⟨nN⁻¹, by rw [map_inv, hnw], rfl⟩, rfl⟩
  · simp only [mul_inv_rev, Subgroup.coe_inv, mul_assoc]

/-- Compare the first eight transitions with the inverted complementary
gallery; fewer than eight complementary transitions cannot return. -/
private lemma closed_gallery_bound (g : ℕ → X) (t : ℕ → I) {n : ℕ} (hn : 0 < n)
    (hclosed : g n = g 0)
    (hstep : ∀ k < n, (g k)⁻¹ * g (k + 1) ∈ T.bruhatCell (D.simple (t k)))
    (hflip : ∀ k, k + 1 < n → D.typeEquiv (t (k + 1)) = !(D.typeEquiv (t k))) :
    16 ≤ n := by
  by_cases hshort : n ≤ 8
  · have hc := D.short_gallery_cell g t hshort hstep hflip
    have hb : (g 0)⁻¹ * g n ∈ T.bruhatCell 1 := by simp [hclosed, T.bruhatCell_one]
    have heq := T.doubleCoset_index_unique hc hb
    have hlen := D.wordLength_alternatingWord (D.typeEquiv (t 0)) hshort
    rw [heq, T.wordLength_one] at hlen
    omega
  · have hc := D.short_gallery_cell g t (n := 8) (by omega)
      (fun k hk => hstep k (by omega)) (fun k hk => hflip k (by omega))
    obtain ⟨w, hw, hlen⟩ := D.gallery_wordLength_le (fun k => g (k + 8))
      (fun k => t (k + 8)) (n - 8) (fun k hk => by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hstep (k + 8) (by omega))
    have hw' := inv_mem_cell w hw
    have hidx : D.alternatingWord (D.typeEquiv (t 0)) 8 = w⁻¹ := by
      apply T.doubleCoset_index_unique hc
      change (g 0)⁻¹ * g 8 ∈ T.bruhatCell w⁻¹
      simpa only [Nat.zero_add, Nat.sub_add_cancel (by omega : 8 ≤ n), hclosed,
        mul_inv_rev, inv_inv] using hw'
    have hmetric := D.dihedralLength_le_wordLength w
    have hval : dihedralLength (D.weylEquiv w) = 8 := by
      rw [← dihedralLength_inv, ← map_inv, ← hidx, D.map_alternatingWord]
      exact dihedralLength_word _ ⟨8, by decide⟩
    omega

private lemma typeEquiv_eq_not_of_ne {i j : I} (h : i ≠ j) :
    D.typeEquiv j = !(D.typeEquiv i) := by
  have h' := D.typeEquiv.injective.ne h
  cases hi : D.typeEquiv i <;> cases hj : D.typeEquiv j <;> simp_all

include D in
private lemma type_eq_of_ne {i j k : I} (hi : i ≠ j) (hk : k ≠ j) : i = k := by
  apply D.typeEquiv.injective
  have h₁ := D.typeEquiv_eq_not_of_ne hi
  have h₂ := D.typeEquiv_eq_not_of_ne hk
  simpa only [Bool.not_not] using congrArg Bool.not (h₁.symm.trans h₂)

/-- A nonbacktracking pair of edges gives a non-Borel parabolic factor. -/
private lemma transition_cell {u v w : CosetGeometry.Vertex F}
    (huv : (graph F).Adj u v) (hvw : (graph F).Adj v w) (hne : u ≠ w)
    (g h : X)
    (hgu : g • CosetGeometry.base F u.type = u)
    (hgv : g • CosetGeometry.base F v.type = v)
    (hhv : h • CosetGeometry.base F v.type = v)
    (hhw : h • CosetGeometry.base F w.type = w) :
    g⁻¹ * h ∈ T.bruhatCell (D.simple v.type) := by
  have hm : g⁻¹ * h ∈ F v.type :=
    (smul_base_eq_iff F g h v.type).mp (hgv.trans hhv.symm)
  apply (D.mem_parabolic_iff v.type _).mp hm |>.resolve_left
  intro hb
  apply hne
  have ht : u.type = w.type := D.type_eq_of_ne huv.1 hvw.1.symm
  have he : g • CosetGeometry.base F u.type = h • CosetGeometry.base F u.type :=
    (smul_base_eq_iff F g h u.type).mpr (D.borel_le u.type hb)
  exact hgu.symm.trans (he.trans (ht ▸ hhw))

include D in
/-- Every simple cycle of the marked octagonal BN-pair incidence graph has
length at least sixteen. The vertices and adjacency are the original typed
left cosets, with no geometric hypotheses added to `OctagonalDatum`. -/
public theorem cycle_bound (v : CosetGeometry.Vertex F) (p : (graph F).Walk v v)
    (hp : p.IsCycle) : 16 ≤ p.length := by
  classical
  have hn := hp.three_le_length
  have hrep : ∀ k : Fin p.length, ∃ g : X,
      g • CosetGeometry.base F (p.getVert k).type = p.getVert k ∧
      g • CosetGeometry.base F (p.getVert (k + 1)).type = p.getVert (k + 1) := by
    intro k
    exact (incident_iff_common_translate F _ _).mp (p.adj_getVert_succ k.isLt).2
  choose r hr using hrep
  let g : ℕ → X := fun k => if hk : k < p.length then r ⟨k, hk⟩ else r ⟨0, by omega⟩
  have hg (k : ℕ) (hk : k < p.length) :
      g k • CosetGeometry.base F (p.getVert k).type = p.getVert k ∧
      g k • CosetGeometry.base F (p.getVert (k + 1)).type = p.getVert (k + 1) := by
    simpa only [g, dif_pos hk] using hr ⟨k, hk⟩
  have hclosed : g p.length = g 0 := by simp [g, show 0 < p.length by omega]
  apply D.closed_gallery_bound g (fun k => (p.getVert (k + 1)).type) (by omega) hclosed
  · intro k hk
    by_cases hk' : k + 1 < p.length
    · apply D.transition_cell (p.adj_getVert_succ hk) (p.adj_getVert_succ hk')
        (by simpa using hp.getVert_sub_one_ne_getVert_add_one (i := k + 1) (by omega))
        (g k) (g (k + 1)) (hg k hk).1 (hg k hk).2 (hg (k + 1) hk').1 (hg (k + 1) hk').2
    · have hklen : k + 1 = p.length := by omega
      have hne : p.getVert k ≠ p.getVert 1 := by
        intro he
        have := hp.getVert_injOn' (by change k ≤ p.length - 1; omega)
          (by change 1 ≤ p.length - 1; omega) he
        omega
      have hvw : (graph F).Adj (p.getVert (k + 1)) (p.getVert 1) := by
        simpa only [hklen, SimpleGraph.Walk.getVert_length,
          SimpleGraph.Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
      apply D.transition_cell (p.adj_getVert_succ hk) hvw hne (g k) (g (k + 1))
        (hg k hk).1 (hg k hk).2
      · simpa only [hklen, hclosed, SimpleGraph.Walk.getVert_length,
          SimpleGraph.Walk.getVert_zero] using (hg 0 (by omega)).1
      · simpa only [hklen, hclosed] using (hg 0 (by omega)).2
  · intro k hk
    exact D.typeEquiv_eq_not_of_ne (p.adj_getVert_succ hk).1

end OctagonalDatum
end Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
