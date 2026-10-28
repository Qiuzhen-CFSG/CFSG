module
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicApartment

/-!
# Root fixation on the two halves of a periodic apartment

An actual simple path in an embedded line has the coordinates determined by
its first edge. A root fixing that path therefore fixes a closed half of the
periodic line. Every edge of the quotient cycle lies in this half or its
reflection, giving a uniform choice for every element of the root group.

The conclusion concerns the two marked vertex classes of the same invariant
relation. It does not identify their stabilizer with the image of an original
edge stabilizer: that additional identification cannot be inferred from
injectivity on the original endpoints.

Source: DGS, *Groups and Graphs* (1985), proof of (3.7), printed p.80.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
open Theory.GroupAction.CubicTree
variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

/-- A simple path supported on a line and starting with its forward edge
has the successive nonnegative integer coordinates. -/
theorem path_on_line_getVert (hΓ : Γ.IsAcyclic) (l : Line Γ)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath)
    (hT : ∀ z∈p.support, z∈Set.range l.vertex)
    (hzero : a=l.vertex 0) (hfirst : p.getVert 1=l.vertex 1) :
    ∀ k≤p.length, p.getVert k=l.vertex k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro _; exact p.getVert_zero.trans hzero
  | one => intro _; exact hfirst
  | more k ih₀ ih₁ =>
    intro hk
    obtain ⟨j,hj⟩ := hT _ (p.getVert_mem_support (k+2))
    have hadj := p.adj_getVert_succ (by omega : k+1<p.length)
    rw [ih₁ (by omega), ←hj] at hadj
    rcases (line_adjacent_iff hΓ l ((k+1:ℕ):ℤ) j).mp hadj with he | he
    · rw [←hj,he]
      congr 1
    · have hjk : j=(k:ℤ) := by omega
      have hsame : p.getVert (k+2)=p.getVert k := by
        rw [←hj,hjk,ih₀ (by omega)]
      have := hp.getVert_injOn hk (by omega : k≤p.length) hsame
      omega

/-- Every edge of a period-2n line is contained in a closed half-cycle or
in its reflection. The choice is uniform for the whole root group. -/
theorem periodic_edge_half (n : ℕ) (hn : 0<n) (j k : ℤ)
    (hjk : k=j+1 ∨ k=j-1) :
    (∃ a b : ℤ, 0≤a ∧ a≤n ∧ 0≤b ∧ b≤n ∧
      j % (2*n:ℕ)=a % (2*n:ℕ) ∧ k % (2*n:ℕ)=b % (2*n:ℕ)) ∨
    (∃ a b : ℤ, 0≤a ∧ a≤n ∧ 0≤b ∧ b≤n ∧
      (-j) % (2*n:ℕ)=a % (2*n:ℕ) ∧ (-k) % (2*n:ℕ)=b % (2*n:ℕ)) := by
  have hforward (j : ℤ) :
      (∃ a b : ℤ, 0≤a ∧ a≤n ∧ 0≤b ∧ b≤n ∧
        j % (2*n:ℕ)=a % (2*n:ℕ) ∧ (j+1) % (2*n:ℕ)=b % (2*n:ℕ)) ∨
      (∃ a b : ℤ, 0≤a ∧ a≤n ∧ 0≤b ∧ b≤n ∧
        (-j) % (2*n:ℕ)=a % (2*n:ℕ) ∧ (-(j+1)) % (2*n:ℕ)=b % (2*n:ℕ)) := by
    let m : ℤ := (2*n:ℕ)
    let v := j % m
    have hm : 0<m := by dsimp [m]; omega
    have hv₀ : 0≤v := Int.emod_nonneg _ (by omega)
    have hvm : v<m := Int.emod_lt_of_pos _ hm
    have hjv : j % m=v % m := (Int.emod_emod j m).symm
    by_cases hv : v<(n:ℤ)
    · left
      refine ⟨v,v+1,hv₀,by omega,by omega,by omega,hjv,?_⟩
      change (j+1)%m=(v+1)%m
      simp only [Int.add_emod,Int.emod_emod]
      simp only [v,Int.emod_emod]
    · right
      have hneg : (-j)%m=(m-v)%m := by
        rw [show -j=0-j by omega]
        simp only [Int.sub_emod,Int.zero_emod,Int.emod_self,Int.emod_emod]
        simp only [v,Int.emod_emod]
      refine ⟨m-v,m-v-1,by dsimp [m] at *; omega,by dsimp [m] at *; omega,
        by dsimp [m] at *; omega,by dsimp [m] at *; omega,hneg,?_⟩
      change (-(j+1))%m=(m-v-1)%m
      have he : -(j+1)= -j-1 := by omega
      rw [he]
      simp only [Int.sub_emod,Int.emod_emod] at hneg ⊢
      rw [hneg]

  rcases hjk with rfl | rfl
  · exact hforward j
  · rcases hforward (j-1) with ⟨a,b,ha₀,ha,hb₀,hb,hja,hjb⟩ |
        ⟨a,b,ha₀,ha,hb₀,hb,hja,hjb⟩
    · exact Or.inl ⟨b,a,hb₀,hb,ha₀,ha,by simpa only [sub_add_cancel] using hjb,hja⟩
    · exact Or.inr ⟨b,a,hb₀,hb,ha₀,ha,by simpa only [sub_add_cancel] using hjb,hja⟩

/-- A root fixing an actual half-path fixes either a transported marked
edge or its reflection in the same separated periodic quotient. This is a
statement about vertex classes, before identifying their stabilizer with
the image of an original Borel. -/
theorem line_root_class_sign (hΓ : Γ.IsAcyclic) (l : Line Γ)
    (r : Setoid V) (hr : Invariant (X := X) r) (n : ℕ) (hn : 0<n)
    (hsep : Separated r Γ (2*n))
    (hperiod : ∀ i : ℤ, r (l.vertex (i+(2*n:ℕ))) (l.vertex i))
    (R : Subgroup X)
    (hfix : ∀ u∈R, ∀ k : ℕ, k≤n → u • l.vertex k=l.vertex k)
    (t : X) (ht : ∀ j : ℤ, t • l.vertex j=l.vertex (-j))
    (x : X) (j k : ℤ) (hx₀ : x • l.vertex 0=l.vertex j)
    (hx₁ : x • l.vertex 1=l.vertex k) (hadj : Γ.Adj (l.vertex j) (l.vertex k)) :
    (∀ u∈R, r ((x⁻¹*u*x) • l.vertex 0) (l.vertex 0) ∧
      r ((x⁻¹*u*x) • l.vertex 1) (l.vertex 1)) ∨
    (∀ u∈R, r (((t*x)⁻¹*u*(t*x)) • l.vertex 0) (l.vertex 0) ∧
      r (((t*x)⁻¹*u*(t*x)) • l.vertex 1) (l.vertex 1)) := by
  have hfixed (u : X) (hu : u∈R) (j a : ℤ) (ha₀ : 0≤a) (ha : a≤n)
      (he : j % (2*n:ℕ)=a % (2*n:ℕ)) : r (u • l.vertex j) (l.vertex j) := by
    have hja := (line_related_iff_mod hΓ l r (2*n) (by omega) hsep hperiod j a).mpr he
    have hf : u • l.vertex a=l.vertex a := by
      have hh := hfix u hu a.toNat (by omega)
      simpa only [Int.toNat_of_nonneg ha₀] using hh
    exact r.trans (by simpa only [hf] using hr u hja) (r.symm hja)
  have hconj (g : X) (u : X) (v : V) (he : r (u • (g • v)) (g • v)) :
      r ((g⁻¹*u*g) • v) v := by
    simpa only [mul_smul,inv_smul_smul] using hr g⁻¹ he
  rcases periodic_edge_half n hn j k ((line_adjacent_iff hΓ l j k).mp hadj) with
      ⟨a,b,ha₀,ha,hb₀,hb,hja,hkb⟩ | ⟨a,b,ha₀,ha,hb₀,hb,hja,hkb⟩
  · left
    intro u hu
    constructor
    · apply hconj
      rw [hx₀]
      exact hfixed u hu j a ha₀ ha hja
    · apply hconj
      rw [hx₁]
      exact hfixed u hu k b hb₀ hb hkb
  · right
    intro u hu
    constructor
    · apply hconj
      rw [mul_smul,hx₀,ht]
      exact hfixed u hu (-j) a ha₀ ha hja
    · apply hconj
      rw [mul_smul,hx₁,ht]
      exact hfixed u hu (-k) b hb₀ hb hkb
end Theory.GroupTheory.WeakBNPair.RegularTree
