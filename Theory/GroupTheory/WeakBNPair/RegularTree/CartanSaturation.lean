module
public import Theory.GroupTheory.WeakBNPair.RegularTree.CartanUniqueness

/-!
# Saturation from the separated apartment quotient

An element of the Borel fixing every quotient vertex of an apartment fixes
its original path vertices: short-distance separation propagates fixation
from the initial vertex along the path. The Hall-Cartan computation of the
path stabilizer then puts the element in the Cartan. Normalization gives the
reverse containment in the intersection of all conjugate Borels.

The theorem applies to one literal quotient map and requires neither ambient
finiteness nor an assumed saturated BN-pair. Source: the apartment quotient
in DGS (3.6)–(3.7), pp.77–80, and the path stabilizer in (14.10), pp.216–217.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {X Y V : Type*} [Group X] [Group Y] [MulAction X V]
variable {Γ : SimpleGraph V} {r : Setoid V}

/-- Separation recovers actual fixation of a path from fixation of its
quotient vertices and of its initial vertex. -/
theorem fixes_path_of_related
    (hconn : Γ.Connected)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {m : ℕ} (hsep : Separated r Γ m) (hm : 2 < m)
    {a b : V} (p : Γ.Walk a b) {x : X} (hstart : x • a = a)
    (hrel : ∀ k ≤ p.length, r (x • p.getVert k) (p.getVert k)) :
    x ∈ pathFixer (X := X) p := by
  intro k hk
  induction k with
  | zero => simpa only [getVert_zero] using hstart
  | succ k ih =>
    have hprev := ih (by omega)
    apply hsep (hrel _ hk)
    have hadj := p.adj_getVert_succ (by omega : k < p.length)
    have hother : Γ.Adj (p.getVert k) (x • p.getVert (k+1)) := by
      simpa only [hprev] using hact x hadj
    have htri := hconn.dist_triangle (u := x • p.getVert (k+1))
      (v := p.getVert k) (w := p.getVert (k+1))
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hother.symm,
      SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at htri
    omega

/-- The intersection of all normalizer conjugates of the image Borel is
exactly the image Cartan. The proof uses the same quotient equivalence
and its short-distance separation, rather than a saturation assumption. -/
theorem image_saturation_of_pathFixer
    (q : X →* Y) (hr : Invariant (X := X) r)
    (hrelated : ∀ {g h : X}, q g = q h → ∀ a : V, r (g • a) (h • a))
    (hconn : Γ.Connected)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {m : ℕ} (hsep : Separated r Γ m) (hm : 2 < m)
    (B K N : Subgroup X) (a c : V)
    (hBa : B ≤ MulAction.stabilizer X a) (hBc : B ≤ MulAction.stabilizer X c)
    (hKB : K ≤ B) (hnorm : N ≤ Subgroup.normalizer (K : Set X))
    {b : V} (p : Γ.Walk a b) (hfix : pathFixer (X := X) p ≤ K)
    (horbit : ∀ k ≤ p.length, ∃ n ∈ N,
      n • a = p.getVert k ∨ n • c = p.getVert k) :
    (⨅ n : N.map q, (B.map q).comap (MulAut.conj (n : Y)).toMonoidHom) = K.map q := by
  apply le_antisymm
  · intro y hy
    have hyB := (Subgroup.mem_iInf.mp hy) (1 : N.map q)
    change (1 : Y) * y * 1⁻¹ ∈ B.map q at hyB
    simp only [inv_one, one_mul, mul_one] at hyB
    obtain ⟨x, hx, rfl⟩ := hyB
    apply Subgroup.mem_map.mpr
    refine ⟨x, hfix ?_, rfl⟩
    apply fixes_path_of_related hconn hact hsep hm p (hBa hx)
    intro k hk
    obtain ⟨n, hn, hnz⟩ := horbit k hk
    have hinv : q n⁻¹ ∈ N.map q := ⟨n⁻¹, N.inv_mem hn, rfl⟩
    have hconj := (Subgroup.mem_iInf.mp hy) ⟨q n⁻¹, hinv⟩
    change q n⁻¹ * q x * (q n⁻¹)⁻¹ ∈ B.map q at hconj
    obtain ⟨d, hd, he⟩ := hconj
    have he' : q (n⁻¹*x*n) = q d := by
      simpa only [map_mul, map_inv, inv_inv] using he.symm
    have hrel (z : V) (hdz : d • z = z) : r (x • (n • z)) (n • z) := by
      have hz := hr n (hrelated he' z)
      simpa only [mul_smul, smul_inv_smul, hdz] using hz
    rcases hnz with hez | hez
    · rw [← hez]
      exact hrel a (hBa hd)
    · rw [← hez]
      exact hrel c (hBc hd)
  · rintro y ⟨k, hk, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro n
    obtain ⟨x, hx, he⟩ := n.property
    change (n : Y) * q k * (n : Y)⁻¹ ∈ B.map q
    rw [← he]
    exact ⟨x*k*x⁻¹, hKB ((Subgroup.mem_normalizer_iff.mp (hnorm hx) k).mp hk),
      by simp only [map_mul, map_inv]⟩
end Theory.GroupTheory.WeakBNPair.RegularTree
