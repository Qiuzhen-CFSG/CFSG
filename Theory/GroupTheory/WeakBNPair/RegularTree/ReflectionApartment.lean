module
public import Theory.GroupAction.CubicTree.Tracks
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentSeparation

/-!
# Reflections determine an apartment in an acyclic graph

Two involutions fixing opposite endpoints of an edge and moving the other
endpoint construct an embedded integer line in the tree. A subgroup fixing
the edge and normalized by the two reflections fixes that line pointwise.
Adjoining it therefore does not enlarge the line, and the resulting orbit
apartment has no branching. The reused integer-line construction does not
require cubic valence; acyclicity rules out chords between its vertices.

This supplies the geometric step after DGS (14.2), printed pp.210--211,
from the actual chosen characteristic-two involutions. It does not choose
them from the earlier local group profiles.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open scoped Pointwise
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
variable {V X : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

/-- Distance along an embedded integer line agrees with its coordinate length. -/
theorem line_dist_add_nat (hΓ : Γ.IsAcyclic) (l : Line Γ) (i : ℤ) (n : ℕ) :
    Γ.dist (l.vertex i) (l.vertex (i+n)) = n := by
  let p := sequenceWalk l.vertex l.adjacent i n
  have hp : p.toWalk.IsPath := isPath_of_nonbacktracking_of_cycle_bound
    (N := n) (fun v c hc => (hΓ c hc).elim) p
    (sequenceWalk_nonbacktracking _ _ (fun j h => by have := l.injective h; omega) i n)
    le_rfl
  obtain ⟨q, hq, hlen⟩ := p.toWalk.reachable.exists_path_of_dist
  have he : p.toWalk = q := Subtype.mk.inj
    ((hΓ.subsingleton_path _ _).elim ⟨p.toWalk, hp⟩ ⟨q, hq⟩)
  have hl : n = Γ.dist (l.vertex i) p.endpoint := by
    rw [← hlen, ← he, BasedWalk.length_toWalk]
  rw [sequenceWalk_endpoint] at hl
  exact hl.symm

/-- An integer line embedded in an acyclic graph has no extra internal edges. -/
theorem line_adjacent_iff (hΓ : Γ.IsAcyclic) (l : Line Γ) (i j : ℤ) :
    Γ.Adj (l.vertex i) (l.vertex j) ↔ j = i+1 ∨ j = i-1 := by
  constructor
  · intro hadj
    rcases le_total i j with hij | hji
    · have hi : i + ((j-i).toNat : ℤ) = j := by omega
      have hd := line_dist_add_nat hΓ l i (j-i).toNat
      rw [hi, SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hd
      left
      omega
    · have hi : j + ((i-j).toNat : ℤ) = i := by omega
      have hd := line_dist_add_nat hΓ l j (i-j).toNat
      rw [hi, SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm] at hd
      right
      omega
  · rintro (rfl | rfl)
    · exact l.adjacent i
    · simpa only [sub_add_cancel] using (l.adjacent (i-1)).symm

/-- The vertex set of an embedded integer line is an apartment with internal
valence at most two. Acyclicity is essential: it excludes chords. -/
theorem line_noBranching (hΓ : Γ.IsAcyclic) (l : Line Γ) :
    NoBranchingIn Γ (Set.range l.vertex) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ ⟨m, rfl⟩ hij hik him hne
  have hj := (line_adjacent_iff hΓ l i j).mp hij
  have hk := (line_adjacent_iff hΓ l i k).mp hik
  have hm := (line_adjacent_iff hΓ l i m).mp him
  have hjk : j ≠ k := fun he => hne (congrArg l.vertex he)
  have : m=j ∨ m=k := by omega
  exact this.imp (congrArg l.vertex) (congrArg l.vertex)

variable (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ X)
variable {a b : V} (hab : Γ.Adj a b) {x y : X}
variable (hx : x • a = a) (hy : y • b = b)
variable (hxb : x • b ≠ b) (hya : y • a ≠ a)
variable (hx2 : x*x=1) (hy2 : y*y=1)
variable (K N : Subgroup X) (hxN : x∈N) (hyN : y∈N)
variable (hnorm : N ≤ Subgroup.normalizer (K : Set X))
variable (hfix : ∀ k∈K, k • a = a ∧ k • b = b)
variable (hgen : N ≤ Subgroup.closure ((K : Set X) ∪ {x,y}))

include hxN hyN hnorm hfix in
/-- Normalization transports the Cartan's fixation of the marked edge to
all integer translates of that edge. -/
theorem cartan_fixes_alternatingVertex (k : X) (hk : k∈K) (i : ℤ) :
    k • alternatingVertex (y*x) a b i = alternatingVertex (y*x) a b i := by
  have hg : (y*x)^(i/2) ∈ N := N.zpow_mem (N.mul_mem hyN hxN) _
  have hc : ((y*x)^(i/2))⁻¹*k*((y*x)^(i/2)) ∈ K := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (hnorm (N.inv_mem hg)) k).mp hk
  have hf := hfix _ hc
  unfold alternatingVertex
  split_ifs with hi
  · have he := congrArg (((y*x)^(i/2)) • ·) hf.1
    simpa only [mul_smul, smul_inv_smul] using he
  · have he := congrArg (((y*x)^(i/2)) • ·) hf.2
    simpa only [mul_smul, smul_inv_smul] using he

include hx hy hx2 hy2 hxN hyN hnorm hfix hgen in
/-- The orbit of the marked edge under the Cartan and its two reflection
lifts is exactly the explicit alternating integer line. -/
theorem reflectionOrbit_eq_range :
    {v | ∃ g∈N, g • a = v ∨ g • b = v} =
      Set.range (alternatingVertex (y*x) a b) := by
  let T := Set.range (alternatingVertex (y*x) a b)
  have hK : K ≤ MulAction.stabilizer X T := by
    apply (MulAction.le_stabilizer_iff_smul_le T K).mpr
    intro k hk v hv
    obtain ⟨w, ⟨i, rfl⟩, rfl⟩ := hv
    exact ⟨i, (cartan_fixes_alternatingVertex K N hxN hyN hnorm hfix k hk i).symm⟩
  have hxs : x ∈ MulAction.stabilizer X T := by
    change x • T = T
    ext v
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨-i, (alternatingVertex_left_reflection hx hy hx2 hy2 i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨-i, rfl⟩, by
        simpa only [neg_neg] using alternatingVertex_left_reflection hx hy hx2 hy2 (-i)⟩
  have hys : y ∈ MulAction.stabilizer X T := by
    change y • T = T
    ext v
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨2-i, (alternatingVertex_right_reflection hx hy hx2 hy2 i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨2-i, rfl⟩, by
        simpa only [sub_sub_cancel] using alternatingVertex_right_reflection hx hy hx2 hy2 (2-i)⟩
  have hN : N ≤ MulAction.stabilizer X T := hgen.trans ((Subgroup.closure_le _).mpr (by
    rintro g (hg | hg)
    · exact hK hg
    · rcases hg with rfl | rfl
      · exact hxs
      · exact hys))
  have haT : a∈T := ⟨0, by simp [alternatingVertex]⟩
  have hbT : b∈T := ⟨1, by simp [alternatingVertex]⟩
  apply Set.Subset.antisymm
  · rintro v ⟨g, hg, rfl | rfl⟩
    · exact (MulAction.le_stabilizer_iff_smul_le T N).mp hN g hg ⟨a, haT, rfl⟩
    · exact (MulAction.le_stabilizer_iff_smul_le T N).mp hN g hg ⟨b, hbT, rfl⟩
  · rintro v ⟨i, rfl⟩
    refine ⟨(y*x)^(i/2), N.zpow_mem (N.mul_mem hyN hxN) _, ?_⟩
    unfold alternatingVertex
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

include hΓ hact hab hx hy hxb hya hx2 hy2 hxN hyN hnorm hfix hgen in
/-- Two adjacent involutory reflections and their normal Cartan generate an
actual nonbranching orbit apartment in a tree. -/
theorem reflectionOrbit_noBranching :
    NoBranchingIn Γ {v | ∃ g∈N, g • a = v ∨ g • b = v} := by
  rw [reflectionOrbit_eq_range hx hy hx2 hy2 K N hxN hyN hnorm hfix hgen]
  exact line_noBranching hΓ (localMoversTrack hΓ hact hab hx hy hxb hya).toLine

end Theory.GroupTheory.WeakBNPair.RegularTree
