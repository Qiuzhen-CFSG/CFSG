module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusNodes
public import Theory.GroupTheory.SubgroupEnumerationBinary
public import Theory.GroupTheory.SubgroupClosureWords

/-!
# Maximal parity-census steps at nodes 61–96

Every maximal subgroup of these prescribed nodes is recovered from its actual
binary membership signature using Schreier generators and the first outside
pivot. The finite branches are certified by parity containment, explicit
conjugacy words, or an outside centralizer element. For the latter, either a
word forces the outside pivot into the closure, or a finite right-transition
cover proves nonmembership. No order or Frattini assumptions are imposed.

Source: the Shinoda (1975), (2.3), pp. 81–82 root model and the fixed words of
`SmallParityCensusNodes`. GAP selected the words and transition tables; all
identities, coverage steps and exclusions below are checked by Lean's kernel.
-/

open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
namespace ReeTwo.SylowModel
namespace SmallParityOrder128
set_option maxRecDepth 10000
private theorem finite_cover {G : Type*} [Group G] [Finite G] {n r : ℕ}
    (s : Fin n → G) (rep : Fin r → G) (base : Fin r)
    (next : Fin r → Fin n → Fin r)
    (hb : rep base = 1) (ht : ∀ a j, rep a * s j = rep (next a j)) :
    ∀ x ∈ Subgroup.closure (Set.range s), ∃ a, x = rep a := by
  intro x hx
  have hx' : x ∈ Submonoid.closure (Set.range s) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hx
  clear hx
  induction hx' using Submonoid.closure_induction_right with
  | one => exact ⟨base, hb.symm⟩
  | mul_right y hy z hz ih =>
    obtain ⟨a, rfl⟩ := ih
    obtain ⟨j, rfl⟩ := hz
    exact ⟨next a j, ht a j⟩

private theorem noncentric {n r : ℕ} (s : Fin n → SylowModel)
    (c : SylowModel) (rep : Fin r → SylowModel) (base : Fin r)
    (next : Fin r → Fin n → Fin r)
    (hb : rep base = 1) (ht : ∀ a j, rep a * s j = rep (next a j))
    (hn : ∀ a, c ≠ rep a) (hc : ∀ j, s j * c = c * s j) :
    ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range s) : Set SylowModel) ∧
      c ∉ Subgroup.closure (Set.range s) := by
  refine ⟨c, ?_, ?_⟩
  · rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, rfl⟩
    exact hc j
  · intro hm
    obtain ⟨a, ha⟩ := finite_cover s rep base next hb ht c hm
    exact hn a ha


private theorem noncentric_short {n : ℕ} (s : Fin n → SylowModel)
    (c t : SylowModel) (w : List (Fin n))
    (ht : t ∉ Subgroup.closure (Set.range s))
    (hc : ∀ j, s j * c = c * s j) (hw : evalWord s w * c = t) :
    ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range s) : Set SylowModel) ∧
      c ∉ Subgroup.closure (Set.range s) := by
  refine ⟨c, ?_, ?_⟩
  · rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j,rfl⟩
    exact hc j
  · intro hm
    apply ht
    rw [← hw]
    exact Subgroup.mul_mem _ (evalWord_mem s _
      (fun j => Subgroup.subset_closure (Set.mem_range_self j)) w) hm

private def signature {n : ℕ} (m : ℕ) (j : Fin n) : Bool := m.testBit j.val
private def pivot {n : ℕ} [NeZero n] (m : ℕ) : Fin n :=
  ((List.finRange n).find? (signature m)).getD 0
private def edgeGen {n : ℕ} [NeZero n] (s : Fin n → SylowModel) (m : ℕ) : Fin (n+n) → SylowModel :=
  Fin.addCases (fun j => binarySchreierGenerator s (s (pivot m)) (signature m) (false,j))
    (fun j => binarySchreierGenerator s (s (pivot m)) (signature m) (true,j))
private theorem edge_range {n : ℕ} [NeZero n] (s : Fin n → SylowModel) (m : ℕ) :
    Set.range (edgeGen s m) = Set.range (binarySchreierGenerator s (s (pivot m)) (signature m)) := by
  ext x
  constructor
  · rintro ⟨j,rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · exact ⟨(false,j),by simp only [edgeGen, Fin.addCases_left]⟩
    · exact ⟨(true,j),by simp only [edgeGen, Fin.addCases_right]⟩
  · rintro ⟨⟨b,j⟩,rfl⟩
    cases b
    · exact ⟨Fin.castAdd n j,by simp only [edgeGen, Fin.addCases_left]⟩
    · exact ⟨Fin.natAdd n j,by simp only [edgeGen, Fin.addCases_right]⟩

private theorem step {n : ℕ} [NeZero n] (i : Fin 131) (s : Fin n → SylowModel)
    (hs : Subgroup.closure (Set.range s) = smallParityCensusNode i)
    (hsig : ∀ σ : Fin n → Bool, (∃ j, σ j = true) →
      ∃ m : Fin (2^n-1), signature (m.val+1) = σ ∧ σ (pivot (m.val+1)) = true)
    (hc : ∀ m : Fin (2^n-1),
      let L := Subgroup.closure (Set.range (edgeGen s (m.val+1)))
      s (pivot (m.val+1)) ∉ L → L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨
      Represented smallParityCensusNode L)
    (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode i)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  classical
  let σ : Fin n → Bool := fun j => decide (s j ∉ H)
  have hex : ∃ j, σ j = true := by
    by_contra h
    have hle : smallParityCensusNode i ≤ H := by
      rw [← hs, Subgroup.closure_le]
      rintro _ ⟨j,rfl⟩
      by_contra hj
      exact h ⟨j, by exact decide_eq_true hj⟩
    exact hmax.lt.not_ge hle
  obtain ⟨m, hm, hp⟩ := hsig σ hex
  have he := binarySchreier_eq_relative hmax.le
    (relIndex_two_of_covBy (IsPGroup.of_card (p:=2) (n:=12) card) hmax)
    s hs (s (pivot (m.val+1))) (hs ▸ Subgroup.subset_closure ⟨_,rfl⟩)
    (of_decide_eq_true hp) (signature (m.val+1)) (by intro j; rw [hm]; simp [σ])
  have hL : Subgroup.closure (Set.range (edgeGen s (m.val+1))) = H := by
    rw [edge_range]; exact he
  have hn : s (pivot (m.val+1)) ∉ Subgroup.closure (Set.range (edgeGen s (m.val+1))) := by
    rw [hL]
    exact of_decide_eq_true hp
  have hh := hc m hn
  rw [hL] at hh
  rcases hh with hh | ⟨c,hc,hn⟩ | hh
  · exact (hpar hh).elim
  · exact (hn (hcent hc)).elim
  · exact hh

private theorem signatures2 : ∀ σ : Fin 2 → Bool, (∃ j, σ j = true) →
    ∃ m : Fin (2^2-1), signature (m.val+1) = σ ∧ σ (pivot (m.val+1)) = true := by decide +kernel

private theorem signatures3 : ∀ σ : Fin 3 → Bool, (∃ j, σ j = true) →
    ∃ m : Fin (2^3-1), signature (m.val+1) = σ ∧ σ (pivot (m.val+1)) = true := by decide +kernel

private theorem signatures4 : ∀ σ : Fin 4 → Bool, (∃ j, σ j = true) →
    ∃ m : Fin (2^4-1), signature (m.val+1) = σ ∧ σ (pivot (m.val+1)) = true := by decide +kernel

private def orig61 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig61_closure : Subgroup.closure (Set.range orig61) = smallParityCensusNode 61 := by
  have he : orig61 = ![rootOne ^ 3, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({rootOne ^ 3, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig62 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig62_closure : Subgroup.closure (Set.range orig62) = smallParityCensusNode 62 := by
  have he : orig62 = ![rootOne ^ 3, root 4 * root 5 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3, root 4 * root 5 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({rootOne ^ 3, root 4 * root 5 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig63 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig63_closure : Subgroup.closure (Set.range orig63) = smallParityCensusNode 63 := by
  have he : orig63 = ![rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig64 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig64_closure : Subgroup.closure (Set.range orig64) = smallParityCensusNode 64 := by
  have he : orig64 = ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 7 * root 9, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 7 * root 9, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 7 * root 9, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig65 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig65_closure : Subgroup.closure (Set.range orig65) = smallParityCensusNode 65 := by
  have he : orig65 = ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig66 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig66_closure : Subgroup.closure (Set.range orig66) = smallParityCensusNode 66 := by
  have he : orig66 = ![rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 8, root 7 * root 9, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 8, root 7 * root 9, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 8, root 7 * root 9, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig67 : Fin 7 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem orig67_closure : Subgroup.closure (Set.range orig67) = smallParityCensusNode 67 := by
  have he : orig67 = ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig68 : Fin 7 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem orig68_closure : Subgroup.closure (Set.range orig68) = smallParityCensusNode 68 := by
  have he : orig68 = ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 6, root 4 * root 5, root 7 * root 8 * root 9, root 8 * root 9, root 9] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 6, root 4 * root 5, root 7 * root 8 * root 9, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 6, root 4 * root 5, root 7 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig69 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig69_closure : Subgroup.closure (Set.range orig69) = smallParityCensusNode 69 := by
  have he : orig69 = ![rootOne ^ 3 * root 3 * root 4, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig70 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig70_closure : Subgroup.closure (Set.range orig70) = smallParityCensusNode 70 := by
  have he : orig70 = ![rootOne ^ 3 * root 3 * root 4, root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig71 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig71_closure : Subgroup.closure (Set.range orig71) = smallParityCensusNode 71 := by
  have he : orig71 = ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig72 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig72_closure : Subgroup.closure (Set.range orig72) = smallParityCensusNode 72 := by
  have he : orig72 = ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig73 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig73_closure : Subgroup.closure (Set.range orig73) = smallParityCensusNode 73 := by
  have he : orig73 = ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6, rootOne ^ 2 * root 4 * root 8, root 4 * root 6 * root 8 * root 9, root 9, root 7, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6, rootOne ^ 2 * root 4 * root 8, root 4 * root 6 * root 8 * root 9, root 9, root 7, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6, rootOne ^ 2 * root 4 * root 8, root 4 * root 6 * root 8 * root 9, root 9, root 7, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig74 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig74_closure : Subgroup.closure (Set.range orig74) = smallParityCensusNode 74 := by
  have he : orig74 = ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 6 * root 7, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 6 * root 7, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 6 * root 7, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig75 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig75_closure : Subgroup.closure (Set.range orig75) = smallParityCensusNode 75 := by
  have he : orig75 = ![root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig76 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig76_closure : Subgroup.closure (Set.range orig76) = smallParityCensusNode 76 := by
  have he : orig76 = ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig77 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig77_closure : Subgroup.closure (Set.range orig77) = smallParityCensusNode 77 := by
  have he : orig77 = ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig78 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig78_closure : Subgroup.closure (Set.range orig78) = smallParityCensusNode 78 := by
  have he : orig78 = ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig79 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig79_closure : Subgroup.closure (Set.range orig79) = smallParityCensusNode 79 := by
  have he : orig79 = ![root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4 * root 6 * root 7 * root 8 * root 9, root 9, root 7 * root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4 * root 6 * root 7 * root 8 * root 9, root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4 * root 6 * root 7 * root 8 * root 9, root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig80 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig80_closure : Subgroup.closure (Set.range orig80) = smallParityCensusNode 80 := by
  have he : orig80 = ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8]) = Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig81 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig81_closure : Subgroup.closure (Set.range orig81) = smallParityCensusNode 81 := by
  have he : orig81 = ![root 2 * root 4 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig82 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig82_closure : Subgroup.closure (Set.range orig82) = smallParityCensusNode 82 := by
  have he : orig82 = ![root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig83 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig83_closure : Subgroup.closure (Set.range orig83) = smallParityCensusNode 83 := by
  have he : orig83 = ![root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig84 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig84_closure : Subgroup.closure (Set.range orig84) = smallParityCensusNode 84 := by
  have he : orig84 = ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig85 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig85_closure : Subgroup.closure (Set.range orig85) = smallParityCensusNode 85 := by
  have he : orig85 = ![root 2 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig86 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig86_closure : Subgroup.closure (Set.range orig86) = smallParityCensusNode 86 := by
  have he : orig86 = ![root 2 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig87 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig87_closure : Subgroup.closure (Set.range orig87) = smallParityCensusNode 87 := by
  have he : orig87 = ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig88 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig88_closure : Subgroup.closure (Set.range orig88) = smallParityCensusNode 88 := by
  have he : orig88 = ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 6 * root 8 * root 9, root 6 * root 8 * root 9, root 8 * root 9, root 7, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 6 * root 8 * root 9, root 6 * root 8 * root 9, root 8 * root 9, root 7, root 8]) = Subgroup.closure ({root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 6 * root 8 * root 9, root 6 * root 8 * root 9, root 8 * root 9, root 7, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig89 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig89_closure : Subgroup.closure (Set.range orig89) = smallParityCensusNode 89 := by
  have he : orig89 = ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig90 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig90_closure : Subgroup.closure (Set.range orig90) = smallParityCensusNode 90 := by
  have he : orig90 = ![root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig91 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig91_closure : Subgroup.closure (Set.range orig91) = smallParityCensusNode 91 := by
  have he : orig91 = ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig92 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig92_closure : Subgroup.closure (Set.range orig92) = smallParityCensusNode 92 := by
  have he : orig92 = ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig93 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig93_closure : Subgroup.closure (Set.range orig93) = smallParityCensusNode 93 := by
  have he : orig93 = ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig94 : Fin 7 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig94_closure : Subgroup.closure (Set.range orig94) = smallParityCensusNode 94 := by
  have he : orig94 = ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig95 : Fin 7 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem orig95_closure : Subgroup.closure (Set.range orig95) = smallParityCensusNode 95 := by
  have he : orig95 = ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig96 : Fin 7 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem orig96_closure : Subgroup.closure (Set.range orig96) = smallParityCensusNode 96 := by
  have he : orig96 = ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig97 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig97_closure : Subgroup.closure (Set.range orig97) = smallParityCensusNode 97 := by
  have he : orig97 = ![rootOne ^ 3, root 4 * root 8, root 9, rootOne ^ 2, root 7 * root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3, root 4 * root 8, root 9, rootOne ^ 2, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({rootOne ^ 3, root 4 * root 8, root 9, rootOne ^ 2, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig98 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig98_closure : Subgroup.closure (Set.range orig98) = smallParityCensusNode 98 := by
  have he : orig98 = ![rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig99 : Fin 6 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem orig99_closure : Subgroup.closure (Set.range orig99) = smallParityCensusNode 99 := by
  have he : orig99 = ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig100 : Fin 6 → SylowModel :=
  ![⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem orig100_closure : Subgroup.closure (Set.range orig100) = smallParityCensusNode 100 := by
  have he : orig100 = ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 7 * root 8 * root 9, root 4 * root 5, root 8 * root 9, root 9] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 7 * root 8 * root 9, root 4 * root 5, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 7 * root 8 * root 9, root 4 * root 5, root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig101 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig101_closure : Subgroup.closure (Set.range orig101) = smallParityCensusNode 101 := by
  have he : orig101 = ![rootOne ^ 3 * root 3 * root 4, root 4 * root 7, root 9, rootOne ^ 2 * root 4 * root 8, root 7 * root 8, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, root 4 * root 7, root 9, rootOne ^ 2 * root 4 * root 8, root 7 * root 8, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 4 * root 7, root 9, rootOne ^ 2 * root 4 * root 8, root 7 * root 8, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig102 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig102_closure : Subgroup.closure (Set.range orig102) = smallParityCensusNode 102 := by
  have he : orig102 = ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 6 * root 7, root 8 * root 9, root 7 * root 8, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 6 * root 7, root 8 * root 9, root 7 * root 8, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 6 * root 7, root 8 * root 9, root 7 * root 8, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig103 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig103_closure : Subgroup.closure (Set.range orig103) = smallParityCensusNode 103 := by
  have he : orig103 = ![root 3, rootOne ^ 3, root 9, rootOne ^ 2, root 4, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3, root 9, rootOne ^ 2, root 4, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3, root 9, rootOne ^ 2, root 4, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig104 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig104_closure : Subgroup.closure (Set.range orig104) = smallParityCensusNode 104 := by
  have he : orig104 = ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig105 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig105_closure : Subgroup.closure (Set.range orig105) = smallParityCensusNode 105 := by
  have he : orig105 = ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 8 * root 9, root 8]) = Subgroup.closure ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig106 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig106_closure : Subgroup.closure (Set.range orig106) = smallParityCensusNode 106 := by
  have he : orig106 = ![root 2 * root 4 * root 8, rootOne ^ 3, root 4, rootOne ^ 2, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 4, rootOne ^ 2, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 4, rootOne ^ 2, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig107 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig107_closure : Subgroup.closure (Set.range orig107) = smallParityCensusNode 107 := by
  have he : orig107 = ![root 2 * root 4 * root 8, rootOne ^ 3, root 7, rootOne ^ 2, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 7, rootOne ^ 2, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 7, rootOne ^ 2, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig108 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig108_closure : Subgroup.closure (Set.range orig108) = smallParityCensusNode 108 := by
  have he : orig108 = ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 7, rootOne ^ 2, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 7, rootOne ^ 2, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 7, rootOne ^ 2, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig109 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig109_closure : Subgroup.closure (Set.range orig109) = smallParityCensusNode 109 := by
  have he : orig109 = ![root 2 * root 8, rootOne ^ 3, root 7, rootOne ^ 2, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 8, rootOne ^ 3, root 7, rootOne ^ 2, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 8, rootOne ^ 3, root 7, rootOne ^ 2, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig110 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig110_closure : Subgroup.closure (Set.range orig110) = smallParityCensusNode 110 := by
  have he : orig110 = ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig111 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig111_closure : Subgroup.closure (Set.range orig111) = smallParityCensusNode 111 := by
  have he : orig111 = ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig112 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig112_closure : Subgroup.closure (Set.range orig112) = smallParityCensusNode 112 := by
  have he : orig112 = ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 7 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 7 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 7 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig113 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem orig113_closure : Subgroup.closure (Set.range orig113) = smallParityCensusNode 113 := by
  have he : orig113 = ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig114 : Fin 6 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem orig114_closure : Subgroup.closure (Set.range orig114) = smallParityCensusNode 114 := by
  have he : orig114 = ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 4 * root 5 * root 7 * root 9, root 9] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 4 * root 5 * root 7 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 4 * root 5 * root 7 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def orig115 : Fin 6 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem orig115_closure : Subgroup.closure (Set.range orig115) = smallParityCensusNode 115 := by
  have he : orig115 = ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 4 * root 5 * root 7 * root 9, root 9] := by decide +kernel
  rw [he]
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 4 * root 5 * root 7 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 4 * root 5 * root 7 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def gen61 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def generation61 : ClosureWords 4 7 :=
  ⟨![[0], [1, 4, 5, 6], [3, 4, 5], [4]],
   ![[0], [0, 0, 0, 2, 0, 1, 2, 3], [0, 0], [0, 2, 0, 0, 0, 3], [3], [0, 0, 2, 0, 2, 0], [0, 0, 0, 1, 0, 1]]⟩
private theorem gen61_closure : Subgroup.closure (Set.range gen61) = smallParityCensusNode 61 := by
  have h := generation61.sound gen61 orig61 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig61_closure] at h
  exact h

private def edge61_1 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_1_eq : edgeGen gen61 1 = edge61_1 := by decide +kernel
private theorem check61_1 (_ht : gen61 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen61 1))) : let L := Subgroup.closure (Set.range (edgeGen gen61 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge61_1 j ∈ character.ker from by decide +kernel) j

private def edge61_2 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_2_eq : edgeGen gen61 2 = edge61_2 := by decide +kernel
private theorem check61_2 (_ht : gen61 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen61 2))) : let L := Subgroup.closure (Set.range (edgeGen gen61 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_2_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_2 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 2)) [0, 0, 0, 2, 3, 4, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_3 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_3_eq : edgeGen gen61 3 = edge61_3 := by decide +kernel
private theorem check61_3 (_ht : gen61 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen61 3))) : let L := Subgroup.closure (Set.range (edgeGen gen61 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_3_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_3 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 3)) [3, 5, 2, 6] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_4 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_4_eq : edgeGen gen61 4 = edge61_4 := by decide +kernel
private def words61_4 : ClosureWords 8 6 :=
  ⟨![[0], [1, 2, 4, 5], [], [2], [4, 0], [1, 2, 4, 5], [], [2]],
   ![[0], [0, 0, 0, 3, 4, 1], [3], [0, 0], [0, 0, 4, 0], [0, 0, 4, 4]]⟩
private theorem check61_4 (_ht : gen61 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen61 4))) : let L := Subgroup.closure (Set.range (edgeGen gen61 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_4_eq]
  right; right
  refine ⟨97, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig97_closure]
  exact words61_4.sound _ _ _ (by decide +kernel)

private def edge61_5 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_5_eq : edgeGen gen61 5 = edge61_5 := by decide +kernel
private def words61_5 : ClosureWords 8 6 :=
  ⟨![[], [1, 4], [0, 1, 2, 3], [2], [0, 4, 0], [1, 4, 5], [0, 1, 2], [2]],
   ![[1, 2, 3, 4], [1, 2, 4, 2], [3], [2, 2], [2, 4, 2], [1, 5]]⟩
private theorem check61_5 (_ht : gen61 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen61 5))) : let L := Subgroup.closure (Set.range (edgeGen gen61 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_5_eq]
  right; right
  refine ⟨97, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig97_closure]
  exact words61_5.sound _ _ _ (by decide +kernel)

private def edge61_6 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_6_eq : edgeGen gen61 6 = edge61_6 := by decide +kernel
private theorem check61_6 (_ht : gen61 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen61 6))) : let L := Subgroup.closure (Set.range (edgeGen gen61 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_6 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 6)) [0, 0, 0, 2, 0, 2, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_7 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_7_eq : edgeGen gen61 7 = edge61_7 := by decide +kernel
private theorem check61_7 (_ht : gen61 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen61 7))) : let L := Subgroup.closure (Set.range (edgeGen gen61 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_7 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 7)) [1, 2, 2, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_8 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_8_eq : edgeGen gen61 8 = edge61_8 := by decide +kernel
private theorem check61_8 (_ht : gen61 (pivot 8) ∉ Subgroup.closure (Set.range (edgeGen gen61 8))) : let L := Subgroup.closure (Set.range (edgeGen gen61 8));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_8_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_8 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 8)) [0, 0, 0, 1, 0, 1] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_9 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge61_9_eq : edgeGen gen61 9 = edge61_9 := by decide +kernel
private theorem check61_9 (_ht : gen61 (pivot 9) ∉ Subgroup.closure (Set.range (edgeGen gen61 9))) : let L := Subgroup.closure (Set.range (edgeGen gen61 9));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_9_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_9 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 9)) [1, 5, 7] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_10 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_10_eq : edgeGen gen61 10 = edge61_10 := by decide +kernel
private theorem check61_10 (_ht : gen61 (pivot 10) ∉ Subgroup.closure (Set.range (edgeGen gen61 10))) : let L := Subgroup.closure (Set.range (edgeGen gen61 10));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_10_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_10 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 10)) [0, 0, 0, 3, 0] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_11 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge61_11_eq : edgeGen gen61 11 = edge61_11 := by decide +kernel
private theorem check61_11 (_ht : gen61 (pivot 11) ∉ Subgroup.closure (Set.range (edgeGen gen61 11))) : let L := Subgroup.closure (Set.range (edgeGen gen61 11));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_11_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_11 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 11)) [1, 1, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_12 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_12_eq : edgeGen gen61 12 = edge61_12 := by decide +kernel
private theorem check61_12 (_ht : gen61 (pivot 12) ∉ Subgroup.closure (Set.range (edgeGen gen61 12))) : let L := Subgroup.closure (Set.range (edgeGen gen61 12));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_12_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_12 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 12)) [0, 0, 3, 0, 0] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_13 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge61_13_eq : edgeGen gen61 13 = edge61_13 := by decide +kernel
private theorem check61_13 (_ht : gen61 (pivot 13) ∉ Subgroup.closure (Set.range (edgeGen gen61 13))) : let L := Subgroup.closure (Set.range (edgeGen gen61 13));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_13_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_13 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 13)) [1, 5, 7] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_14 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge61_14_eq : edgeGen gen61 14 = edge61_14 := by decide +kernel
private theorem check61_14 (_ht : gen61 (pivot 14) ∉ Subgroup.closure (Set.range (edgeGen gen61 14))) : let L := Subgroup.closure (Set.range (edgeGen gen61 14));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_14_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_14 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 14)) [0, 0, 0, 3, 0] _ht
    (by decide +kernel) (by decide +kernel)

private def edge61_15 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge61_15_eq : edgeGen gen61 15 = edge61_15 := by decide +kernel
private theorem check61_15 (_ht : gen61 (pivot 15) ∉ Subgroup.closure (Set.range (edgeGen gen61 15))) : let L := Subgroup.closure (Set.range (edgeGen gen61 15));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge61_15_eq] at _ht ⊢
  right; left
  exact noncentric_short edge61_15 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen61 (pivot 15)) [1, 1, 3] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node61 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 61)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 61 gen61 gen61_closure signatures4 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check61_1
  · exact check61_2
  · exact check61_3
  · exact check61_4
  · exact check61_5
  · exact check61_6
  · exact check61_7
  · exact check61_8
  · exact check61_9
  · exact check61_10
  · exact check61_11
  · exact check61_12
  · exact check61_13
  · exact check61_14
  · exact check61_15

private def gen62 : Fin 2 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def generation62 : ClosureWords 2 7 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1], [1, 1], [0, 0, 1, 0, 0, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1]]⟩
private theorem gen62_closure : Subgroup.closure (Set.range gen62) = smallParityCensusNode 62 := by
  have h := generation62.sound gen62 orig62 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig62_closure] at h
  exact h

private def edge62_1 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge62_1_eq : edgeGen gen62 1 = edge62_1 := by decide +kernel
private theorem check62_1 (_ht : gen62 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen62 1))) : let L := Subgroup.closure (Set.range (edgeGen gen62 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge62_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge62_1 j ∈ character.ker from by decide +kernel) j

private def edge62_2 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge62_2_eq : edgeGen gen62 2 = edge62_2 := by decide +kernel
private def reps62_2 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private def next62_2 : Fin 64 → Fin 4 → Fin 64 :=
  ![![1, 0, 2, 3], ![4, 1, 5, 6], ![7, 2, 8, 9], ![6, 3, 9, 0], ![10, 4, 11, 12], ![13, 5, 14, 15], ![12, 6, 15, 1], ![16, 7, 17, 18], ![19, 8, 20, 21], ![18, 9, 21, 2], ![0, 10, 22, 23], ![24, 11, 25, 26], ![23, 12, 26, 4], ![27, 13, 28, 29], ![30, 14, 31, 32], ![29, 15, 32, 5], ![31, 16, 30, 33], ![28, 17, 27, 34], ![33, 18, 34, 7], ![25, 19, 24, 35], ![22, 20, 0, 36], ![35, 21, 36, 8], ![37, 22, 38, 39], ![3, 23, 39, 10], ![40, 24, 41, 42], ![43, 25, 44, 45], ![42, 26, 45, 11], ![44, 27, 43, 46], ![41, 28, 40, 47], ![46, 29, 47, 13], ![38, 30, 37, 48], ![2, 31, 1, 49], ![48, 32, 49, 14], ![49, 33, 48, 16], ![47, 34, 46, 17], ![45, 35, 42, 19], ![39, 36, 3, 20], ![50, 37, 51, 52], ![53, 38, 54, 55], ![52, 39, 55, 22], ![54, 40, 53, 56], ![51, 41, 50, 57], ![56, 42, 57, 24], ![8, 43, 7, 58], ![5, 44, 4, 59], ![58, 45, 59, 25], ![59, 46, 58, 27], ![57, 47, 56, 28], ![55, 48, 52, 30], ![9, 49, 6, 31], ![20, 50, 19, 60], ![17, 51, 16, 61], ![60, 52, 61, 37], ![14, 53, 13, 62], ![11, 54, 10, 63], ![62, 55, 63, 38], ![63, 56, 62, 40], ![61, 57, 60, 41], ![21, 58, 18, 43], ![15, 59, 12, 44], ![36, 60, 35, 50], ![34, 61, 33, 51], ![32, 62, 29, 53], ![26, 63, 23, 54]]
private theorem transitions62_2 : ∀ a j, reps62_2 a * edge62_2 j = reps62_2 (next62_2 a j) := by decide +kernel
private theorem check62_2 (_ht : gen62 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen62 2))) : let L := Subgroup.closure (Set.range (edgeGen gen62 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge62_2_eq]
  right; left
  exact noncentric edge62_2 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps62_2 0 next62_2
    (by decide +kernel) transitions62_2 (by decide +kernel) (by decide +kernel)

private def edge62_3 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge62_3_eq : edgeGen gen62 3 = edge62_3 := by decide +kernel
private def reps62_3 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def next62_3 : Fin 64 → Fin 4 → Fin 64 :=
  ![![0, 1, 2, 3], ![1, 4, 5, 6], ![2, 7, 0, 8], ![3, 6, 9, 10], ![4, 11, 12, 13], ![5, 14, 1, 15], ![6, 13, 16, 17], ![7, 18, 19, 16], ![8, 16, 20, 12], ![9, 21, 3, 14], ![10, 17, 18, 22], ![11, 23, 24, 25], ![12, 26, 4, 27], ![13, 25, 28, 0], ![14, 29, 30, 28], ![15, 28, 31, 24], ![16, 32, 6, 26], ![17, 0, 29, 33], ![18, 34, 10, 32], ![19, 35, 7, 31], ![20, 36, 8, 35], ![21, 37, 36, 29], ![22, 33, 37, 23], ![23, 38, 39, 40], ![24, 41, 11, 42], ![25, 40, 43, 1], ![26, 2, 44, 43], ![27, 43, 45, 39], ![28, 46, 13, 41], ![29, 47, 17, 46], ![30, 48, 14, 45], ![31, 49, 15, 48], ![32, 50, 49, 2], ![33, 3, 50, 38], ![34, 39, 48, 50], ![35, 44, 51, 49], ![36, 45, 21, 44], ![37, 42, 22, 47], ![38, 10, 52, 53], ![39, 54, 23, 55], ![40, 53, 56, 4], ![41, 5, 57, 56], ![42, 56, 58, 52], ![43, 8, 25, 54], ![44, 59, 26, 58], ![45, 60, 27, 59], ![46, 9, 60, 5], ![47, 52, 59, 9], ![48, 57, 34, 60], ![49, 58, 32, 57], ![50, 55, 33, 7], ![51, 24, 35, 37], ![52, 51, 38, 21], ![53, 22, 61, 11], ![54, 12, 62, 61], ![55, 61, 63, 18], ![56, 15, 40, 51], ![57, 19, 41, 63], ![58, 20, 42, 19], ![59, 62, 47, 20], ![60, 63, 46, 62], ![61, 27, 53, 34], ![62, 30, 54, 36], ![63, 31, 55, 30]]
private theorem transitions62_3 : ∀ a j, reps62_3 a * edge62_3 j = reps62_3 (next62_3 a j) := by decide +kernel
private theorem check62_3 (_ht : gen62 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen62 3))) : let L := Subgroup.closure (Set.range (edgeGen gen62 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge62_3_eq]
  right; left
  exact noncentric edge62_3 (⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps62_3 0 next62_3
    (by decide +kernel) transitions62_3 (by decide +kernel) (by decide +kernel)

private theorem node62 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 62)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 62 gen62 gen62_closure signatures2 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check62_1
  · exact check62_2
  · exact check62_3

private def gen63 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def generation63 : ClosureWords 3 7 :=
  ⟨![[1, 4, 5, 6], [3, 4, 5], [0]],
   ![[2], [1, 2, 0, 2, 2, 1, 2], [0, 2, 0, 1, 2], [0, 2, 0, 1, 2, 2, 2], [0, 2, 0, 2, 2, 2], [1, 2, 2, 2, 1, 2], [2, 2, 2, 2]]⟩
private theorem gen63_closure : Subgroup.closure (Set.range gen63) = smallParityCensusNode 63 := by
  have h := generation63.sound gen63 orig63 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig63_closure] at h
  exact h

private def edge63_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge63_1_eq : edgeGen gen63 1 = edge63_1 := by decide +kernel
private def reps63_1 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private def next63_1 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 0, 4, 1, 0, 5], ![2, 6, 7, 2, 6, 8], ![3, 9, 8, 3, 9, 7], ![4, 10, 11, 4, 10, 12], ![5, 13, 12, 5, 13, 11], ![6, 2, 14, 6, 2, 15], ![7, 16, 17, 7, 16, 18], ![8, 19, 18, 8, 19, 17], ![9, 3, 15, 9, 3, 14], ![10, 4, 20, 10, 4, 21], ![11, 22, 23, 11, 22, 24], ![12, 25, 24, 12, 25, 23], ![13, 5, 21, 13, 5, 20], ![14, 26, 27, 14, 26, 28], ![15, 29, 28, 15, 29, 27], ![16, 7, 30, 16, 7, 31], ![17, 32, 33, 17, 32, 34], ![18, 35, 34, 18, 35, 33], ![19, 8, 31, 19, 8, 30], ![20, 36, 37, 20, 36, 38], ![21, 39, 38, 21, 39, 37], ![22, 11, 40, 22, 11, 41], ![23, 42, 43, 23, 42, 44], ![24, 45, 44, 24, 45, 43], ![25, 12, 41, 25, 12, 40], ![26, 14, 42, 26, 14, 45], ![27, 40, 46, 27, 40, 47], ![28, 41, 47, 28, 41, 46], ![29, 15, 45, 29, 15, 42], ![30, 37, 1, 30, 37, 48], ![31, 38, 48, 31, 38, 1], ![32, 17, 49, 32, 17, 50], ![33, 43, 51, 33, 43, 52], ![34, 44, 52, 34, 44, 51], ![35, 18, 50, 35, 18, 49], ![36, 20, 32, 36, 20, 35], ![37, 30, 53, 37, 30, 54], ![38, 31, 54, 38, 31, 53], ![39, 21, 35, 39, 21, 32], ![40, 27, 0, 40, 27, 55], ![41, 28, 55, 41, 28, 0], ![42, 23, 56, 42, 23, 57], ![43, 33, 58, 43, 33, 59], ![44, 34, 59, 44, 34, 58], ![45, 24, 57, 45, 24, 56], ![46, 53, 60, 46, 53, 61], ![47, 54, 61, 47, 54, 60], ![48, 55, 5, 48, 55, 4], ![49, 56, 6, 49, 56, 9], ![50, 57, 9, 50, 57, 6], ![51, 60, 22, 51, 60, 25], ![52, 61, 25, 52, 61, 22], ![53, 46, 62, 53, 46, 63], ![54, 47, 63, 54, 47, 62], ![55, 48, 3, 55, 48, 2], ![56, 49, 10, 56, 49, 13], ![57, 50, 13, 57, 50, 10], ![58, 62, 16, 58, 62, 19], ![59, 63, 19, 59, 63, 16], ![60, 51, 36, 60, 51, 39], ![61, 52, 39, 61, 52, 36], ![62, 58, 26, 62, 58, 29], ![63, 59, 29, 63, 59, 26]]
private theorem transitions63_1 : ∀ a j, reps63_1 a * edge63_1 j = reps63_1 (next63_1 a j) := by decide +kernel
private theorem check63_1 (_ht : gen63 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen63 1))) : let L := Subgroup.closure (Set.range (edgeGen gen63 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge63_1_eq]
  right; left
  exact noncentric edge63_1 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps63_1 0 next63_1
    (by decide +kernel) transitions63_1 (by decide +kernel) (by decide +kernel)

private def edge63_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge63_2_eq : edgeGen gen63 2 = edge63_2 := by decide +kernel
private def words63_2 : ClosureWords 6 6 :=
  ⟨![[1, 3, 4, 5], [], [0], [1, 3, 4, 5], [], [4, 0]],
   ![[2], [2, 0, 2, 2, 5], [2, 2], [0, 2, 0, 2, 2, 2], [2, 2, 2, 5], [2, 2, 2, 2]]⟩
private theorem check63_2 (_ht : gen63 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen63 2))) : let L := Subgroup.closure (Set.range (edgeGen gen63 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge63_2_eq]
  right; right
  refine ⟨98, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig98_closure]
  exact words63_2.sound _ _ _ (by decide +kernel)

private def edge63_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge63_3_eq : edgeGen gen63 3 = edge63_3 := by decide +kernel
private def reps63_3 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private def next63_3 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 0, 4, 1, 0, 5], ![2, 6, 7, 2, 6, 8], ![3, 9, 8, 3, 9, 7], ![4, 10, 11, 4, 10, 12], ![5, 13, 12, 5, 13, 11], ![6, 2, 14, 6, 2, 15], ![7, 16, 17, 7, 16, 18], ![8, 19, 18, 8, 19, 17], ![9, 3, 15, 9, 3, 14], ![10, 4, 20, 10, 4, 21], ![11, 22, 23, 11, 22, 24], ![12, 25, 24, 12, 25, 23], ![13, 5, 21, 13, 5, 20], ![14, 26, 27, 14, 26, 28], ![15, 29, 28, 15, 29, 27], ![16, 7, 30, 16, 7, 31], ![17, 32, 33, 17, 32, 34], ![18, 35, 34, 18, 35, 33], ![19, 8, 31, 19, 8, 30], ![20, 36, 37, 20, 36, 38], ![21, 39, 38, 21, 39, 37], ![22, 11, 40, 22, 11, 41], ![23, 42, 43, 23, 42, 44], ![24, 45, 44, 24, 45, 43], ![25, 12, 41, 25, 12, 40], ![26, 14, 42, 26, 14, 45], ![27, 40, 46, 27, 40, 47], ![28, 41, 47, 28, 41, 46], ![29, 15, 45, 29, 15, 42], ![30, 37, 1, 30, 37, 48], ![31, 38, 48, 31, 38, 1], ![32, 17, 49, 32, 17, 50], ![33, 43, 51, 33, 43, 52], ![34, 44, 52, 34, 44, 51], ![35, 18, 50, 35, 18, 49], ![36, 20, 32, 36, 20, 35], ![37, 30, 53, 37, 30, 54], ![38, 31, 54, 38, 31, 53], ![39, 21, 35, 39, 21, 32], ![40, 27, 0, 40, 27, 55], ![41, 28, 55, 41, 28, 0], ![42, 23, 56, 42, 23, 57], ![43, 33, 58, 43, 33, 59], ![44, 34, 59, 44, 34, 58], ![45, 24, 57, 45, 24, 56], ![46, 53, 60, 46, 53, 61], ![47, 54, 61, 47, 54, 60], ![48, 55, 5, 48, 55, 4], ![49, 56, 6, 49, 56, 9], ![50, 57, 9, 50, 57, 6], ![51, 60, 22, 51, 60, 25], ![52, 61, 25, 52, 61, 22], ![53, 46, 62, 53, 46, 63], ![54, 47, 63, 54, 47, 62], ![55, 48, 3, 55, 48, 2], ![56, 49, 10, 56, 49, 13], ![57, 50, 13, 57, 50, 10], ![58, 62, 16, 58, 62, 19], ![59, 63, 19, 59, 63, 16], ![60, 51, 36, 60, 51, 39], ![61, 52, 39, 61, 52, 36], ![62, 58, 26, 62, 58, 29], ![63, 59, 29, 63, 59, 26]]
private theorem transitions63_3 : ∀ a j, reps63_3 a * edge63_3 j = reps63_3 (next63_3 a j) := by decide +kernel
private theorem check63_3 (_ht : gen63 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen63 3))) : let L := Subgroup.closure (Set.range (edgeGen gen63 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge63_3_eq]
  right; left
  exact noncentric edge63_3 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps63_3 0 next63_3
    (by decide +kernel) transitions63_3 (by decide +kernel) (by decide +kernel)

private def edge63_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge63_4_eq : edgeGen gen63 4 = edge63_4 := by decide +kernel
private theorem check63_4 (_ht : gen63 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen63 4))) : let L := Subgroup.closure (Set.range (edgeGen gen63 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge63_4_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge63_4 j ∈ character.ker from by decide +kernel) j

private def edge63_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge63_5_eq : edgeGen gen63 5 = edge63_5 := by decide +kernel
private def reps63_5 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private def next63_5 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 0, 4, 1, 0, 5], ![2, 6, 7, 2, 6, 8], ![3, 9, 8, 3, 9, 7], ![4, 10, 11, 4, 10, 12], ![5, 13, 12, 5, 13, 11], ![6, 2, 14, 6, 2, 15], ![7, 16, 17, 7, 16, 18], ![8, 19, 18, 8, 19, 17], ![9, 3, 15, 9, 3, 14], ![10, 4, 20, 10, 4, 21], ![11, 22, 23, 11, 22, 24], ![12, 25, 24, 12, 25, 23], ![13, 5, 21, 13, 5, 20], ![14, 26, 27, 14, 26, 28], ![15, 29, 28, 15, 29, 27], ![16, 7, 30, 16, 7, 31], ![17, 32, 33, 17, 32, 34], ![18, 35, 34, 18, 35, 33], ![19, 8, 31, 19, 8, 30], ![20, 36, 37, 20, 36, 38], ![21, 39, 38, 21, 39, 37], ![22, 11, 40, 22, 11, 41], ![23, 42, 43, 23, 42, 44], ![24, 45, 44, 24, 45, 43], ![25, 12, 41, 25, 12, 40], ![26, 14, 42, 26, 14, 45], ![27, 40, 46, 27, 40, 47], ![28, 41, 47, 28, 41, 46], ![29, 15, 45, 29, 15, 42], ![30, 37, 1, 30, 37, 48], ![31, 38, 48, 31, 38, 1], ![32, 17, 49, 32, 17, 50], ![33, 43, 51, 33, 43, 52], ![34, 44, 52, 34, 44, 51], ![35, 18, 50, 35, 18, 49], ![36, 20, 32, 36, 20, 35], ![37, 30, 53, 37, 30, 54], ![38, 31, 54, 38, 31, 53], ![39, 21, 35, 39, 21, 32], ![40, 27, 0, 40, 27, 55], ![41, 28, 55, 41, 28, 0], ![42, 23, 56, 42, 23, 57], ![43, 33, 58, 43, 33, 59], ![44, 34, 59, 44, 34, 58], ![45, 24, 57, 45, 24, 56], ![46, 53, 60, 46, 53, 61], ![47, 54, 61, 47, 54, 60], ![48, 55, 5, 48, 55, 4], ![49, 56, 6, 49, 56, 9], ![50, 57, 9, 50, 57, 6], ![51, 60, 22, 51, 60, 25], ![52, 61, 25, 52, 61, 22], ![53, 46, 62, 53, 46, 63], ![54, 47, 63, 54, 47, 62], ![55, 48, 3, 55, 48, 2], ![56, 49, 10, 56, 49, 13], ![57, 50, 13, 57, 50, 10], ![58, 62, 16, 58, 62, 19], ![59, 63, 19, 59, 63, 16], ![60, 51, 36, 60, 51, 39], ![61, 52, 39, 61, 52, 36], ![62, 58, 26, 62, 58, 29], ![63, 59, 29, 63, 59, 26]]
private theorem transitions63_5 : ∀ a j, reps63_5 a * edge63_5 j = reps63_5 (next63_5 a j) := by decide +kernel
private theorem check63_5 (_ht : gen63 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen63 5))) : let L := Subgroup.closure (Set.range (edgeGen gen63 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge63_5_eq]
  right; left
  exact noncentric edge63_5 (⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps63_5 0 next63_5
    (by decide +kernel) transitions63_5 (by decide +kernel) (by decide +kernel)

private def edge63_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge63_6_eq : edgeGen gen63 6 = edge63_6 := by decide +kernel
private def words63_6 : ClosureWords 6 6 :=
  ⟨![[1, 4], [], [1, 0], [1, 4], [], [1, 4, 0]],
   ![[0, 5], [0, 2, 2, 2, 5], [0, 5, 0, 5], [0, 2, 0, 2, 2, 2], [2, 2, 2, 5], [2, 2, 2, 2]]⟩
private theorem check63_6 (_ht : gen63 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen63 6))) : let L := Subgroup.closure (Set.range (edgeGen gen63 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge63_6_eq]
  right; right
  refine ⟨98, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig98_closure]
  exact words63_6.sound _ _ _ (by decide +kernel)

private def edge63_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge63_7_eq : edgeGen gen63 7 = edge63_7 := by decide +kernel
private def reps63_7 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def next63_7 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 0, 4, 1, 0, 5], ![2, 6, 7, 2, 6, 8], ![3, 9, 8, 3, 9, 7], ![4, 10, 11, 4, 10, 12], ![5, 13, 12, 5, 13, 11], ![6, 2, 14, 6, 2, 15], ![7, 16, 17, 7, 16, 18], ![8, 19, 18, 8, 19, 17], ![9, 3, 15, 9, 3, 14], ![10, 4, 20, 10, 4, 21], ![11, 22, 23, 11, 22, 24], ![12, 25, 24, 12, 25, 23], ![13, 5, 21, 13, 5, 20], ![14, 26, 27, 14, 26, 28], ![15, 29, 28, 15, 29, 27], ![16, 7, 30, 16, 7, 31], ![17, 32, 33, 17, 32, 34], ![18, 35, 34, 18, 35, 33], ![19, 8, 31, 19, 8, 30], ![20, 36, 37, 20, 36, 38], ![21, 39, 38, 21, 39, 37], ![22, 11, 40, 22, 11, 41], ![23, 42, 43, 23, 42, 44], ![24, 45, 44, 24, 45, 43], ![25, 12, 41, 25, 12, 40], ![26, 14, 42, 26, 14, 45], ![27, 40, 46, 27, 40, 47], ![28, 41, 47, 28, 41, 46], ![29, 15, 45, 29, 15, 42], ![30, 37, 1, 30, 37, 48], ![31, 38, 48, 31, 38, 1], ![32, 17, 49, 32, 17, 50], ![33, 43, 51, 33, 43, 52], ![34, 44, 52, 34, 44, 51], ![35, 18, 50, 35, 18, 49], ![36, 20, 32, 36, 20, 35], ![37, 30, 53, 37, 30, 54], ![38, 31, 54, 38, 31, 53], ![39, 21, 35, 39, 21, 32], ![40, 27, 0, 40, 27, 55], ![41, 28, 55, 41, 28, 0], ![42, 23, 56, 42, 23, 57], ![43, 33, 58, 43, 33, 59], ![44, 34, 59, 44, 34, 58], ![45, 24, 57, 45, 24, 56], ![46, 53, 60, 46, 53, 61], ![47, 54, 61, 47, 54, 60], ![48, 55, 5, 48, 55, 4], ![49, 56, 6, 49, 56, 9], ![50, 57, 9, 50, 57, 6], ![51, 60, 22, 51, 60, 25], ![52, 61, 25, 52, 61, 22], ![53, 46, 62, 53, 46, 63], ![54, 47, 63, 54, 47, 62], ![55, 48, 3, 55, 48, 2], ![56, 49, 10, 56, 49, 13], ![57, 50, 13, 57, 50, 10], ![58, 62, 16, 58, 62, 19], ![59, 63, 19, 59, 63, 16], ![60, 51, 36, 60, 51, 39], ![61, 52, 39, 61, 52, 36], ![62, 58, 26, 62, 58, 29], ![63, 59, 29, 63, 59, 26]]
private theorem transitions63_7 : ∀ a j, reps63_7 a * edge63_7 j = reps63_7 (next63_7 a j) := by decide +kernel
private theorem check63_7 (_ht : gen63 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen63 7))) : let L := Subgroup.closure (Set.range (edgeGen gen63 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge63_7_eq]
  right; left
  exact noncentric edge63_7 (⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps63_7 0 next63_7
    (by decide +kernel) transitions63_7 (by decide +kernel) (by decide +kernel)

private theorem node63 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 63)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 63 gen63 gen63_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check63_1
  · exact check63_2
  · exact check63_3
  · exact check63_4
  · exact check63_5
  · exact check63_6
  · exact check63_7

private def gen64 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def generation64 : ClosureWords 3 7 :=
  ⟨![[0], [1], [5]],
   ![[0], [1], [0, 0], [0, 0, 0, 1, 1, 1, 0, 1], [1, 1], [2], [0, 0, 0, 1, 1, 0, 1, 1]]⟩
private theorem gen64_closure : Subgroup.closure (Set.range gen64) = smallParityCensusNode 64 := by
  have h := generation64.sound gen64 orig64 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig64_closure] at h
  exact h

private def edge64_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge64_1_eq : edgeGen gen64 1 = edge64_1 := by decide +kernel
private theorem check64_1 (_ht : gen64 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen64 1))) : let L := Subgroup.closure (Set.range (edgeGen gen64 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge64_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge64_1 j ∈ character.ker from by decide +kernel) j

private def edge64_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge64_2_eq : edgeGen gen64 2 = edge64_2 := by decide +kernel
private def words64_2 : ClosureWords 6 6 :=
  ⟨![[0], [], [2], [0, 1, 5], [4, 5], [2]],
   ![[0], [0, 0, 0, 4, 3, 4], [2], [0, 0], [0, 0, 0, 4, 0], [0, 0, 0, 4, 0, 4]]⟩
private theorem check64_2 (_ht : gen64 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen64 2))) : let L := Subgroup.closure (Set.range (edgeGen gen64 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge64_2_eq]
  right; right
  refine ⟨97, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig97_closure]
  exact words64_2.sound _ _ _ (by decide +kernel)

private def edge64_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge64_3_eq : edgeGen gen64 3 = edge64_3 := by decide +kernel
private def words64_3 : ClosureWords 6 6 :=
  ⟨![[], [0, 3], [2], [1, 2, 3, 5], [2, 4, 0], [2]],
   ![[1, 1, 1], [2, 3, 4, 4], [2], [1, 1], [2, 4, 1], [1, 1, 4, 4]]⟩
private theorem check64_3 (_ht : gen64 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen64 3))) : let L := Subgroup.closure (Set.range (edgeGen gen64 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge64_3_eq]
  right; right
  refine ⟨97, (⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig97_closure]
  exact words64_3.sound _ _ _ (by decide +kernel)

private def edge64_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge64_4_eq : edgeGen gen64 4 = edge64_4 := by decide +kernel
private theorem check64_4 (_ht : gen64 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen64 4))) : let L := Subgroup.closure (Set.range (edgeGen gen64 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge64_4_eq] at _ht ⊢
  right; left
  exact noncentric_short edge64_4 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen64 (pivot 4)) [0, 0, 0, 1, 1, 0, 1, 1] _ht
    (by decide +kernel) (by decide +kernel)

private def edge64_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge64_5_eq : edgeGen gen64 5 = edge64_5 := by decide +kernel
private theorem check64_5 (_ht : gen64 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen64 5))) : let L := Subgroup.closure (Set.range (edgeGen gen64 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge64_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge64_5 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen64 (pivot 5)) [1, 1, 4, 4, 5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge64_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge64_6_eq : edgeGen gen64 6 = edge64_6 := by decide +kernel
private theorem check64_6 (_ht : gen64 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen64 6))) : let L := Subgroup.closure (Set.range (edgeGen gen64 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge64_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge64_6 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen64 (pivot 6)) [0, 0, 0, 5, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge64_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge64_7_eq : edgeGen gen64 7 = edge64_7 := by decide +kernel
private theorem check64_7 (_ht : gen64 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen64 7))) : let L := Subgroup.closure (Set.range (edgeGen gen64 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge64_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge64_7 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen64 (pivot 7)) [1, 1, 4, 2, 1] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node64 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 64)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 64 gen64 gen64_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check64_1
  · exact check64_2
  · exact check64_3
  · exact check64_4
  · exact check64_5
  · exact check64_6
  · exact check64_7

private def gen65 : Fin 2 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private def generation65 : ClosureWords 2 7 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 0, 0, 1, 1, 1, 0, 1], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1]]⟩
private theorem gen65_closure : Subgroup.closure (Set.range gen65) = smallParityCensusNode 65 := by
  have h := generation65.sound gen65 orig65 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig65_closure] at h
  exact h

private def edge65_1 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge65_1_eq : edgeGen gen65 1 = edge65_1 := by decide +kernel
private theorem check65_1 (_ht : gen65 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen65 1))) : let L := Subgroup.closure (Set.range (edgeGen gen65 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge65_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge65_1 j ∈ character.ker from by decide +kernel) j

private def edge65_2 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge65_2_eq : edgeGen gen65 2 = edge65_2 := by decide +kernel
private def reps65_2 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def next65_2 : Fin 64 → Fin 4 → Fin 64 :=
  ![![1, 0, 2, 3], ![4, 1, 5, 6], ![7, 2, 8, 9], ![10, 3, 11, 0], ![12, 4, 13, 14], ![15, 5, 16, 17], ![18, 6, 19, 1], ![20, 7, 21, 22], ![23, 8, 24, 25], ![26, 9, 27, 2], ![14, 10, 17, 28], ![22, 11, 25, 29], ![0, 12, 30, 31], ![32, 13, 33, 34], ![35, 14, 36, 4], ![37, 15, 38, 39], ![40, 16, 41, 42], ![43, 17, 44, 5], ![31, 18, 34, 45], ![39, 19, 42, 46], ![41, 20, 40, 36], ![38, 21, 37, 35], ![34, 22, 31, 7], ![33, 23, 32, 44], ![30, 24, 0, 43], ![42, 25, 39, 8], ![36, 26, 35, 47], ![44, 27, 43, 48], ![45, 28, 46, 10], ![47, 29, 48, 11], ![49, 30, 50, 51], ![52, 31, 53, 12], ![29, 32, 28, 54], ![55, 33, 56, 57], ![58, 34, 59, 13], ![3, 35, 51, 21], ![54, 36, 57, 20], ![56, 37, 55, 53], ![28, 38, 29, 52], ![51, 39, 3, 15], ![50, 40, 49, 59], ![2, 41, 1, 58], ![57, 42, 54, 16], ![53, 43, 52, 24], ![59, 44, 58, 23], ![21, 45, 20, 18], ![24, 46, 23, 19], ![13, 47, 12, 26], ![16, 48, 15, 27], ![46, 49, 45, 60], ![48, 50, 47, 61], ![62, 51, 63, 30], ![6, 52, 9, 38], ![60, 53, 61, 37], ![9, 54, 6, 32], ![8, 55, 7, 63], ![5, 56, 4, 62], ![61, 57, 60, 33], ![11, 58, 10, 41], ![63, 59, 62, 40], ![17, 60, 14, 49], ![25, 61, 22, 50], ![19, 62, 18, 56], ![27, 63, 26, 55]]
private theorem transitions65_2 : ∀ a j, reps65_2 a * edge65_2 j = reps65_2 (next65_2 a j) := by decide +kernel
private theorem check65_2 (_ht : gen65 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen65 2))) : let L := Subgroup.closure (Set.range (edgeGen gen65 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge65_2_eq]
  right; left
  exact noncentric edge65_2 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps65_2 0 next65_2
    (by decide +kernel) transitions65_2 (by decide +kernel) (by decide +kernel)

private def edge65_3 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge65_3_eq : edgeGen gen65 3 = edge65_3 := by decide +kernel
private def reps65_3 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def next65_3 : Fin 64 → Fin 4 → Fin 64 :=
  ![![0, 1, 2, 3], ![1, 4, 5, 6], ![2, 7, 0, 8], ![3, 9, 10, 4], ![4, 11, 12, 13], ![5, 14, 1, 15], ![6, 16, 17, 11], ![7, 18, 19, 17], ![8, 20, 21, 18], ![9, 13, 20, 22], ![10, 15, 3, 23], ![11, 24, 25, 26], ![12, 27, 4, 28], ![13, 29, 30, 24], ![14, 31, 32, 30], ![15, 33, 34, 31], ![16, 26, 33, 0], ![17, 28, 6, 35], ![18, 35, 36, 37], ![19, 38, 7, 34], ![20, 37, 9, 27], ![21, 34, 8, 32], ![22, 0, 31, 29], ![23, 25, 38, 33], ![24, 39, 40, 41], ![25, 42, 11, 43], ![26, 3, 44, 39], ![27, 2, 45, 44], ![28, 46, 47, 2], ![29, 41, 46, 1], ![30, 43, 13, 48], ![31, 48, 22, 49], ![32, 50, 14, 47], ![33, 49, 16, 42], ![34, 47, 15, 45], ![35, 40, 50, 46], ![36, 22, 18, 16], ![37, 44, 51, 40], ![38, 45, 23, 51], ![39, 36, 52, 9], ![40, 53, 24, 54], ![41, 6, 55, 36], ![42, 5, 56, 55], ![43, 10, 57, 5], ![44, 54, 26, 7], ![45, 58, 27, 57], ![46, 8, 29, 53], ![47, 57, 28, 56], ![48, 52, 58, 10], ![49, 55, 59, 52], ![50, 56, 35, 59], ![51, 59, 37, 58], ![52, 23, 39, 60], ![53, 12, 61, 20], ![54, 17, 62, 12], ![55, 60, 41, 14], ![56, 19, 42, 62], ![57, 62, 43, 61], ![58, 61, 48, 21], ![59, 21, 49, 19], ![60, 30, 63, 25], ![61, 32, 53, 63], ![62, 63, 54, 38], ![63, 51, 60, 50]]
private theorem transitions65_3 : ∀ a j, reps65_3 a * edge65_3 j = reps65_3 (next65_3 a j) := by decide +kernel
private theorem check65_3 (_ht : gen65 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen65 3))) : let L := Subgroup.closure (Set.range (edgeGen gen65 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge65_3_eq]
  right; left
  exact noncentric edge65_3 (⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps65_3 0 next65_3
    (by decide +kernel) transitions65_3 (by decide +kernel) (by decide +kernel)

private theorem node65 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 65)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 65 gen65 gen65_closure signatures2 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check65_1
  · exact check65_2
  · exact check65_3

private def gen66 : Fin 2 → SylowModel :=
  ![⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def generation66 : ClosureWords 2 7 :=
  ⟨![[1], [0]],
   ![[1], [0], [1, 1], [0, 0, 1, 0, 1, 0, 1, 1], [0, 0], [0, 0, 1, 0, 1, 1, 0, 1], [1, 1, 1, 1]]⟩
private theorem gen66_closure : Subgroup.closure (Set.range gen66) = smallParityCensusNode 66 := by
  have h := generation66.sound gen66 orig66 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig66_closure] at h
  exact h

private def edge66_1 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge66_1_eq : edgeGen gen66 1 = edge66_1 := by decide +kernel
private def words66_1 : ClosureWords 4 6 :=
  ⟨![[], [0], [4, 5], [0, 1, 5]],
   ![[1], [1, 1, 1, 3], [1, 1], [1, 1, 2, 3, 2, 3], [1, 1, 1, 1, 2], [1, 1, 1, 1]]⟩
private theorem check66_1 (_ht : gen66 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen66 1))) : let L := Subgroup.closure (Set.range (edgeGen gen66 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge66_1_eq]
  right; right
  refine ⟨98, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig98_closure]
  exact words66_1.sound _ _ _ (by decide +kernel)

private def edge66_2 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge66_2_eq : edgeGen gen66 2 = edge66_2 := by decide +kernel
private theorem check66_2 (_ht : gen66 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen66 2))) : let L := Subgroup.closure (Set.range (edgeGen gen66 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge66_2_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge66_2 j ∈ character.ker from by decide +kernel) j

private def edge66_3 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge66_3_eq : edgeGen gen66 3 = edge66_3 := by decide +kernel
private def words66_3 : ClosureWords 4 6 :=
  ⟨![[], [0, 3], [3, 4, 5], [0, 1, 5]],
   ![[1, 1, 1, 2, 3, 2, 3], [1, 1, 3, 1], [1, 1], [1, 1, 2, 3, 2, 3], [1, 1, 2, 3, 3], [1, 1, 1, 1]]⟩
private theorem check66_3 (_ht : gen66 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen66 3))) : let L := Subgroup.closure (Set.range (edgeGen gen66 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge66_3_eq]
  right; right
  refine ⟨98, (⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig98_closure]
  exact words66_3.sound _ _ _ (by decide +kernel)

private theorem node66 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 66)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 66 gen66 gen66_closure signatures2 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check66_1
  · exact check66_2
  · exact check66_3

private def gen67 : Fin 2 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩]
private def generation67 : ClosureWords 2 7 :=
  ⟨![[2, 5], [0]],
   ![[1], [1, 1], [0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1], [1, 1, 1, 1], [0, 1, 1, 1, 0, 1, 1, 1, 1, 1], [1, 0, 1, 1, 0, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1]]⟩
private theorem gen67_closure : Subgroup.closure (Set.range gen67) = smallParityCensusNode 67 := by
  have h := generation67.sound gen67 orig67 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig67_closure] at h
  exact h

private def edge67_1 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩]
private theorem edge67_1_eq : edgeGen gen67 1 = edge67_1 := by decide +kernel
private def words67_1 : ClosureWords 4 6 :=
  ⟨![[], [0], [], [0, 2, 5]],
   ![[1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 3], [1, 1, 1, 1], [1, 1, 1, 1, 1, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]]⟩
private theorem check67_1 (_ht : gen67 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen67 1))) : let L := Subgroup.closure (Set.range (edgeGen gen67 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge67_1_eq]
  right; right
  refine ⟨99, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig99_closure]
  exact words67_1.sound _ _ _ (by decide +kernel)

private def edge67_2 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge67_2_eq : edgeGen gen67 2 = edge67_2 := by decide +kernel
private theorem check67_2 (_ht : gen67 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen67 2))) : let L := Subgroup.closure (Set.range (edgeGen gen67 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge67_2_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge67_2 j ∈ character.ker from by decide +kernel) j

private def edge67_3 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩]
private theorem edge67_3_eq : edgeGen gen67 3 = edge67_3 := by decide +kernel
private def words67_3 : ClosureWords 4 6 :=
  ⟨![[], [4, 0], [], [2, 0]],
   ![[1, 1, 1, 1, 1, 1, 1, 3, 3], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 3], [1, 1, 1, 1], [1, 1, 1, 1, 1, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]]⟩
private theorem check67_3 (_ht : gen67 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen67 3))) : let L := Subgroup.closure (Set.range (edgeGen gen67 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge67_3_eq]
  right; right
  refine ⟨99, (⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig99_closure]
  exact words67_3.sound _ _ _ (by decide +kernel)

private theorem node67 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 67)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 67 gen67 gen67_closure signatures2 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check67_1
  · exact check67_2
  · exact check67_3

private def gen68 : Fin 2 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩]
private def generation68 : ClosureWords 2 7 :=
  ⟨![[2], [0]],
   ![[1], [1, 1], [0], [1, 1, 1, 1], [1, 0, 1, 0, 1, 1, 1, 1, 1, 1], [1, 0, 1, 1, 0, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1]]⟩
private theorem gen68_closure : Subgroup.closure (Set.range gen68) = smallParityCensusNode 68 := by
  have h := generation68.sound gen68 orig68 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig68_closure] at h
  exact h

private def edge68_1 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩]
private theorem edge68_1_eq : edgeGen gen68 1 = edge68_1 := by decide +kernel
private def words68_1 : ClosureWords 4 6 :=
  ⟨![[], [0], [], [0, 2]],
   ![[1], [1, 1], [1, 1, 1, 1, 1, 3, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]]⟩
private theorem check68_1 (_ht : gen68 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen68 1))) : let L := Subgroup.closure (Set.range (edgeGen gen68 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge68_1_eq]
  right; right
  refine ⟨100, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig100_closure]
  exact words68_1.sound _ _ _ (by decide +kernel)

private def edge68_2 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge68_2_eq : edgeGen gen68 2 = edge68_2 := by decide +kernel
private theorem check68_2 (_ht : gen68 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen68 2))) : let L := Subgroup.closure (Set.range (edgeGen gen68 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge68_2_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge68_2 j ∈ character.ker from by decide +kernel) j

private def edge68_3 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩]
private theorem edge68_3_eq : edgeGen gen68 3 = edge68_3 := by decide +kernel
private def words68_3 : ClosureWords 4 6 :=
  ⟨![[], [0, 5], [], [0, 2, 5]],
   ![[1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 3, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]]⟩
private theorem check68_3 (_ht : gen68 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen68 3))) : let L := Subgroup.closure (Set.range (edgeGen gen68 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge68_3_eq]
  right; right
  refine ⟨100, (⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig100_closure]
  exact words68_3.sound _ _ _ (by decide +kernel)

private theorem node68 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 68)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 68 gen68 gen68_closure signatures2 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check68_1
  · exact check68_2
  · exact check68_3

private def gen69 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private def generation69 : ClosureWords 4 7 :=
  ⟨![[1, 6], [3, 5], [4], [0]],
   ![[3], [3, 0, 3, 3, 3], [3, 3], [3, 1, 3, 3, 3], [2], [1, 3, 1, 3, 3, 3], [0, 3, 0, 3, 3, 3]]⟩
private theorem gen69_closure : Subgroup.closure (Set.range gen69) = smallParityCensusNode 69 := by
  have h := generation69.sound gen69 orig69 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig69_closure] at h
  exact h

private def edge69_1 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_1_eq : edgeGen gen69 1 = edge69_1 := by decide +kernel
private theorem check69_1 (_ht : gen69 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen69 1))) : let L := Subgroup.closure (Set.range (edgeGen gen69 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_1_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_1 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 1)) [1, 3, 1, 3, 3, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_2 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_2_eq : edgeGen gen69 2 = edge69_2 := by decide +kernel
private def words69_2 : ClosureWords 8 6 :=
  ⟨![[1, 5], [], [2], [0], [1, 5], [], [2], [4, 0]],
   ![[3], [0, 3, 3, 7, 7], [2], [3, 3], [3, 3, 7, 3], [3, 3, 7, 7]]⟩
private theorem check69_2 (_ht : gen69 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen69 2))) : let L := Subgroup.closure (Set.range (edgeGen gen69 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_2_eq]
  right; right
  refine ⟨101, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig101_closure]
  exact words69_2.sound _ _ _ (by decide +kernel)

private def edge69_3 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_3_eq : edgeGen gen69 3 = edge69_3 := by decide +kernel
private theorem check69_3 (_ht : gen69 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen69 3))) : let L := Subgroup.closure (Set.range (edgeGen gen69 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_3_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_3 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 3)) [1, 3, 1, 3, 3, 7] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_4 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_4_eq : edgeGen gen69 4 = edge69_4 := by decide +kernel
private theorem check69_4 (_ht : gen69 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen69 4))) : let L := Subgroup.closure (Set.range (edgeGen gen69 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_4_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_4 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 4)) [0, 3, 0, 3, 3, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_5 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_5_eq : edgeGen gen69 5 = edge69_5 := by decide +kernel
private theorem check69_5 (_ht : gen69 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen69 5))) : let L := Subgroup.closure (Set.range (edgeGen gen69 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_5 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 5)) [2, 3, 3, 3, 7] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_6 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_6_eq : edgeGen gen69 6 = edge69_6 := by decide +kernel
private theorem check69_6 (_ht : gen69 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen69 6))) : let L := Subgroup.closure (Set.range (edgeGen gen69 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_6 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 6)) [2, 3, 3, 7, 7] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_7 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_7_eq : edgeGen gen69 7 = edge69_7 := by decide +kernel
private theorem check69_7 (_ht : gen69 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen69 7))) : let L := Subgroup.closure (Set.range (edgeGen gen69 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_7 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 7)) [2, 3, 3, 3, 7] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_8 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge69_8_eq : edgeGen gen69 8 = edge69_8 := by decide +kernel
private theorem check69_8 (_ht : gen69 (pivot 8) ∉ Subgroup.closure (Set.range (edgeGen gen69 8))) : let L := Subgroup.closure (Set.range (edgeGen gen69 8));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_8_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge69_8 j ∈ character.ker from by decide +kernel) j

private def edge69_9 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_9_eq : edgeGen gen69 9 = edge69_9 := by decide +kernel
private theorem check69_9 (_ht : gen69 (pivot 9) ∉ Subgroup.closure (Set.range (edgeGen gen69 9))) : let L := Subgroup.closure (Set.range (edgeGen gen69 9));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_9_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_9 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 9)) [1, 3, 1, 3, 3, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_10 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_10_eq : edgeGen gen69 10 = edge69_10 := by decide +kernel
private def words69_10 : ClosureWords 8 6 :=
  ⟨![[1, 2], [], [2], [0, 1], [1, 2], [], [2], [1, 0, 4]],
   ![[2, 3, 0], [0, 2], [2], [7, 7], [3, 3, 7, 3], [3, 3, 7, 7]]⟩
private theorem check69_10 (_ht : gen69 (pivot 10) ∉ Subgroup.closure (Set.range (edgeGen gen69 10))) : let L := Subgroup.closure (Set.range (edgeGen gen69 10));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_10_eq]
  right; right
  refine ⟨101, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig101_closure]
  exact words69_10.sound _ _ _ (by decide +kernel)

private def edge69_11 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_11_eq : edgeGen gen69 11 = edge69_11 := by decide +kernel
private theorem check69_11 (_ht : gen69 (pivot 11) ∉ Subgroup.closure (Set.range (edgeGen gen69 11))) : let L := Subgroup.closure (Set.range (edgeGen gen69 11));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_11_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_11 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 11)) [1, 3, 1, 3, 3, 7] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_12 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_12_eq : edgeGen gen69 12 = edge69_12 := by decide +kernel
private theorem check69_12 (_ht : gen69 (pivot 12) ∉ Subgroup.closure (Set.range (edgeGen gen69 12))) : let L := Subgroup.closure (Set.range (edgeGen gen69 12));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_12_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_12 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 12)) [0, 3, 0, 3, 3, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_13 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_13_eq : edgeGen gen69 13 = edge69_13 := by decide +kernel
private theorem check69_13 (_ht : gen69 (pivot 13) ∉ Subgroup.closure (Set.range (edgeGen gen69 13))) : let L := Subgroup.closure (Set.range (edgeGen gen69 13));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_13_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_13 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 13)) [2, 3, 3, 3, 7] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_14 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_14_eq : edgeGen gen69 14 = edge69_14 := by decide +kernel
private theorem check69_14 (_ht : gen69 (pivot 14) ∉ Subgroup.closure (Set.range (edgeGen gen69 14))) : let L := Subgroup.closure (Set.range (edgeGen gen69 14));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_14_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_14 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 14)) [2, 3, 3, 7, 7] _ht
    (by decide +kernel) (by decide +kernel)

private def edge69_15 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge69_15_eq : edgeGen gen69 15 = edge69_15 := by decide +kernel
private theorem check69_15 (_ht : gen69 (pivot 15) ∉ Subgroup.closure (Set.range (edgeGen gen69 15))) : let L := Subgroup.closure (Set.range (edgeGen gen69 15));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge69_15_eq] at _ht ⊢
  right; left
  exact noncentric_short edge69_15 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen69 (pivot 15)) [2, 3, 3, 3, 7] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node69 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 69)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 69 gen69 gen69_closure signatures4 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check69_1
  · exact check69_2
  · exact check69_3
  · exact check69_4
  · exact check69_5
  · exact check69_6
  · exact check69_7
  · exact check69_8
  · exact check69_9
  · exact check69_10
  · exact check69_11
  · exact check69_12
  · exact check69_13
  · exact check69_14
  · exact check69_15

private def gen70 : Fin 2 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private def generation70 : ClosureWords 2 7 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 1, 0, 1, 0, 0, 1, 1], [1, 1], [0, 0, 1, 0, 0, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1]]⟩
private theorem gen70_closure : Subgroup.closure (Set.range gen70) = smallParityCensusNode 70 := by
  have h := generation70.sound gen70 orig70 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig70_closure] at h
  exact h

private def edge70_1 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge70_1_eq : edgeGen gen70 1 = edge70_1 := by decide +kernel
private theorem check70_1 (_ht : gen70 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen70 1))) : let L := Subgroup.closure (Set.range (edgeGen gen70 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge70_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge70_1 j ∈ character.ker from by decide +kernel) j

private def edge70_2 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge70_2_eq : edgeGen gen70 2 = edge70_2 := by decide +kernel
private def reps70_2 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩]
private def next70_2 : Fin 64 → Fin 4 → Fin 64 :=
  ![![1, 0, 2, 3], ![4, 1, 5, 6], ![7, 2, 8, 9], ![6, 3, 9, 0], ![10, 4, 11, 12], ![13, 5, 14, 15], ![12, 6, 15, 1], ![16, 7, 17, 18], ![19, 8, 20, 21], ![18, 9, 21, 2], ![0, 10, 22, 23], ![24, 11, 25, 26], ![23, 12, 26, 4], ![27, 13, 28, 29], ![30, 14, 31, 32], ![29, 15, 32, 5], ![31, 16, 30, 33], ![28, 17, 27, 34], ![33, 18, 34, 7], ![25, 19, 24, 35], ![22, 20, 0, 36], ![35, 21, 36, 8], ![37, 22, 38, 39], ![3, 23, 39, 10], ![40, 24, 41, 42], ![43, 25, 44, 45], ![42, 26, 45, 11], ![44, 27, 43, 46], ![41, 28, 40, 47], ![46, 29, 47, 13], ![38, 30, 37, 48], ![2, 31, 1, 49], ![48, 32, 49, 14], ![49, 33, 48, 16], ![47, 34, 46, 17], ![45, 35, 42, 19], ![39, 36, 3, 20], ![50, 37, 51, 52], ![53, 38, 54, 55], ![52, 39, 55, 22], ![54, 40, 53, 56], ![51, 41, 50, 57], ![56, 42, 57, 24], ![8, 43, 7, 58], ![5, 44, 4, 59], ![58, 45, 59, 25], ![59, 46, 58, 27], ![57, 47, 56, 28], ![55, 48, 52, 30], ![9, 49, 6, 31], ![20, 50, 19, 60], ![17, 51, 16, 61], ![60, 52, 61, 37], ![14, 53, 13, 62], ![11, 54, 10, 63], ![62, 55, 63, 38], ![63, 56, 62, 40], ![61, 57, 60, 41], ![21, 58, 18, 43], ![15, 59, 12, 44], ![36, 60, 35, 50], ![34, 61, 33, 51], ![32, 62, 29, 53], ![26, 63, 23, 54]]
private theorem transitions70_2 : ∀ a j, reps70_2 a * edge70_2 j = reps70_2 (next70_2 a j) := by decide +kernel
private theorem check70_2 (_ht : gen70 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen70 2))) : let L := Subgroup.closure (Set.range (edgeGen gen70 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge70_2_eq]
  right; left
  exact noncentric edge70_2 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps70_2 0 next70_2
    (by decide +kernel) transitions70_2 (by decide +kernel) (by decide +kernel)

private def edge70_3 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge70_3_eq : edgeGen gen70 3 = edge70_3 := by decide +kernel
private def reps70_3 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private def next70_3 : Fin 64 → Fin 4 → Fin 64 :=
  ![![0, 1, 2, 3], ![1, 4, 5, 6], ![2, 7, 0, 8], ![3, 6, 9, 10], ![4, 11, 12, 13], ![5, 14, 1, 15], ![6, 13, 16, 17], ![7, 18, 19, 16], ![8, 16, 20, 12], ![9, 21, 3, 14], ![10, 17, 18, 22], ![11, 23, 24, 25], ![12, 26, 4, 27], ![13, 25, 28, 0], ![14, 29, 30, 28], ![15, 28, 31, 24], ![16, 32, 6, 26], ![17, 0, 29, 33], ![18, 34, 10, 32], ![19, 35, 7, 31], ![20, 36, 8, 35], ![21, 37, 36, 29], ![22, 33, 37, 23], ![23, 38, 39, 40], ![24, 41, 11, 42], ![25, 40, 43, 1], ![26, 2, 44, 43], ![27, 43, 45, 39], ![28, 46, 13, 41], ![29, 47, 17, 46], ![30, 48, 14, 45], ![31, 49, 15, 48], ![32, 50, 49, 2], ![33, 3, 50, 38], ![34, 39, 48, 50], ![35, 44, 51, 49], ![36, 45, 21, 44], ![37, 42, 22, 47], ![38, 10, 52, 53], ![39, 54, 23, 55], ![40, 53, 56, 4], ![41, 5, 57, 56], ![42, 56, 58, 52], ![43, 8, 25, 54], ![44, 59, 26, 58], ![45, 60, 27, 59], ![46, 9, 60, 5], ![47, 52, 59, 9], ![48, 57, 34, 60], ![49, 58, 32, 57], ![50, 55, 33, 7], ![51, 24, 35, 37], ![52, 51, 38, 21], ![53, 22, 61, 11], ![54, 12, 62, 61], ![55, 61, 63, 18], ![56, 15, 40, 51], ![57, 19, 41, 63], ![58, 20, 42, 19], ![59, 62, 47, 20], ![60, 63, 46, 62], ![61, 27, 53, 34], ![62, 30, 54, 36], ![63, 31, 55, 30]]
private theorem transitions70_3 : ∀ a j, reps70_3 a * edge70_3 j = reps70_3 (next70_3 a j) := by decide +kernel
private theorem check70_3 (_ht : gen70 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen70 3))) : let L := Subgroup.closure (Set.range (edgeGen gen70 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge70_3_eq]
  right; left
  exact noncentric edge70_3 (⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps70_3 0 next70_3
    (by decide +kernel) transitions70_3 (by decide +kernel) (by decide +kernel)

private theorem node70 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 70)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 70 gen70 gen70_closure signatures2 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check70_1
  · exact check70_2
  · exact check70_3

private def gen71 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def generation71 : ClosureWords 3 7 :=
  ⟨![[1, 6], [3, 5], [0]],
   ![[2], [0, 2, 2, 2, 2], [1, 2, 1, 2, 1], [2, 2, 2, 1, 2], [0, 2, 0, 2, 2, 2], [1, 2, 2, 2, 1, 2], [2, 2, 2, 2]]⟩
private theorem gen71_closure : Subgroup.closure (Set.range gen71) = smallParityCensusNode 71 := by
  have h := generation71.sound gen71 orig71 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig71_closure] at h
  exact h

private def edge71_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge71_1_eq : edgeGen gen71 1 = edge71_1 := by decide +kernel
private def reps71_1 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private def next71_1 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 0, 4, 1, 0, 5], ![2, 6, 7, 2, 6, 8], ![3, 9, 8, 3, 9, 7], ![4, 10, 11, 4, 10, 12], ![5, 13, 12, 5, 13, 11], ![6, 2, 14, 6, 2, 15], ![7, 16, 17, 7, 16, 18], ![8, 19, 18, 8, 19, 17], ![9, 3, 15, 9, 3, 14], ![10, 4, 20, 10, 4, 21], ![11, 22, 23, 11, 22, 24], ![12, 25, 24, 12, 25, 23], ![13, 5, 21, 13, 5, 20], ![14, 26, 27, 14, 26, 28], ![15, 29, 28, 15, 29, 27], ![16, 7, 30, 16, 7, 31], ![17, 32, 33, 17, 32, 34], ![18, 35, 34, 18, 35, 33], ![19, 8, 31, 19, 8, 30], ![20, 36, 37, 20, 36, 38], ![21, 39, 38, 21, 39, 37], ![22, 11, 40, 22, 11, 41], ![23, 42, 43, 23, 42, 44], ![24, 45, 44, 24, 45, 43], ![25, 12, 41, 25, 12, 40], ![26, 14, 42, 26, 14, 45], ![27, 40, 46, 27, 40, 47], ![28, 41, 47, 28, 41, 46], ![29, 15, 45, 29, 15, 42], ![30, 37, 1, 30, 37, 48], ![31, 38, 48, 31, 38, 1], ![32, 17, 49, 32, 17, 50], ![33, 43, 51, 33, 43, 52], ![34, 44, 52, 34, 44, 51], ![35, 18, 50, 35, 18, 49], ![36, 20, 32, 36, 20, 35], ![37, 30, 53, 37, 30, 54], ![38, 31, 54, 38, 31, 53], ![39, 21, 35, 39, 21, 32], ![40, 27, 0, 40, 27, 55], ![41, 28, 55, 41, 28, 0], ![42, 23, 56, 42, 23, 57], ![43, 33, 58, 43, 33, 59], ![44, 34, 59, 44, 34, 58], ![45, 24, 57, 45, 24, 56], ![46, 53, 60, 46, 53, 61], ![47, 54, 61, 47, 54, 60], ![48, 55, 5, 48, 55, 4], ![49, 56, 6, 49, 56, 9], ![50, 57, 9, 50, 57, 6], ![51, 60, 22, 51, 60, 25], ![52, 61, 25, 52, 61, 22], ![53, 46, 62, 53, 46, 63], ![54, 47, 63, 54, 47, 62], ![55, 48, 3, 55, 48, 2], ![56, 49, 10, 56, 49, 13], ![57, 50, 13, 57, 50, 10], ![58, 62, 16, 58, 62, 19], ![59, 63, 19, 59, 63, 16], ![60, 51, 36, 60, 51, 39], ![61, 52, 39, 61, 52, 36], ![62, 58, 26, 62, 58, 29], ![63, 59, 29, 63, 59, 26]]
private theorem transitions71_1 : ∀ a j, reps71_1 a * edge71_1 j = reps71_1 (next71_1 a j) := by decide +kernel
private theorem check71_1 (_ht : gen71 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen71 1))) : let L := Subgroup.closure (Set.range (edgeGen gen71 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge71_1_eq]
  right; left
  exact noncentric edge71_1 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps71_1 0 next71_1
    (by decide +kernel) transitions71_1 (by decide +kernel) (by decide +kernel)

private def edge71_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge71_2_eq : edgeGen gen71 2 = edge71_2 := by decide +kernel
private def words71_2 : ClosureWords 6 6 :=
  ⟨![[1, 5], [], [0], [1, 5], [], [4, 0]],
   ![[2], [0, 2, 2, 2, 2], [2, 2], [0, 2, 0, 2, 5, 5], [2, 2, 2, 5], [2, 2, 2, 2]]⟩
private theorem check71_2 (_ht : gen71 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen71 2))) : let L := Subgroup.closure (Set.range (edgeGen gen71 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge71_2_eq]
  right; right
  refine ⟨102, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig102_closure]
  exact words71_2.sound _ _ _ (by decide +kernel)

private def edge71_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge71_3_eq : edgeGen gen71 3 = edge71_3 := by decide +kernel
private def reps71_3 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def next71_3 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 0, 4, 1, 0, 5], ![2, 6, 7, 2, 6, 8], ![3, 9, 8, 3, 9, 7], ![4, 10, 11, 4, 10, 12], ![5, 13, 12, 5, 13, 11], ![6, 2, 14, 6, 2, 15], ![7, 16, 17, 7, 16, 18], ![8, 19, 18, 8, 19, 17], ![9, 3, 15, 9, 3, 14], ![10, 4, 20, 10, 4, 21], ![11, 22, 23, 11, 22, 24], ![12, 25, 24, 12, 25, 23], ![13, 5, 21, 13, 5, 20], ![14, 26, 27, 14, 26, 28], ![15, 29, 28, 15, 29, 27], ![16, 7, 30, 16, 7, 31], ![17, 32, 33, 17, 32, 34], ![18, 35, 34, 18, 35, 33], ![19, 8, 31, 19, 8, 30], ![20, 36, 37, 20, 36, 38], ![21, 39, 38, 21, 39, 37], ![22, 11, 40, 22, 11, 41], ![23, 42, 43, 23, 42, 44], ![24, 45, 44, 24, 45, 43], ![25, 12, 41, 25, 12, 40], ![26, 14, 42, 26, 14, 45], ![27, 40, 46, 27, 40, 47], ![28, 41, 47, 28, 41, 46], ![29, 15, 45, 29, 15, 42], ![30, 37, 1, 30, 37, 48], ![31, 38, 48, 31, 38, 1], ![32, 17, 49, 32, 17, 50], ![33, 43, 51, 33, 43, 52], ![34, 44, 52, 34, 44, 51], ![35, 18, 50, 35, 18, 49], ![36, 20, 32, 36, 20, 35], ![37, 30, 53, 37, 30, 54], ![38, 31, 54, 38, 31, 53], ![39, 21, 35, 39, 21, 32], ![40, 27, 0, 40, 27, 55], ![41, 28, 55, 41, 28, 0], ![42, 23, 56, 42, 23, 57], ![43, 33, 58, 43, 33, 59], ![44, 34, 59, 44, 34, 58], ![45, 24, 57, 45, 24, 56], ![46, 53, 60, 46, 53, 61], ![47, 54, 61, 47, 54, 60], ![48, 55, 5, 48, 55, 4], ![49, 56, 6, 49, 56, 9], ![50, 57, 9, 50, 57, 6], ![51, 60, 22, 51, 60, 25], ![52, 61, 25, 52, 61, 22], ![53, 46, 62, 53, 46, 63], ![54, 47, 63, 54, 47, 62], ![55, 48, 3, 55, 48, 2], ![56, 49, 10, 56, 49, 13], ![57, 50, 13, 57, 50, 10], ![58, 62, 16, 58, 62, 19], ![59, 63, 19, 59, 63, 16], ![60, 51, 36, 60, 51, 39], ![61, 52, 39, 61, 52, 36], ![62, 58, 26, 62, 58, 29], ![63, 59, 29, 63, 59, 26]]
private theorem transitions71_3 : ∀ a j, reps71_3 a * edge71_3 j = reps71_3 (next71_3 a j) := by decide +kernel
private theorem check71_3 (_ht : gen71 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen71 3))) : let L := Subgroup.closure (Set.range (edgeGen gen71 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge71_3_eq]
  right; left
  exact noncentric edge71_3 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps71_3 0 next71_3
    (by decide +kernel) transitions71_3 (by decide +kernel) (by decide +kernel)

private def edge71_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge71_4_eq : edgeGen gen71 4 = edge71_4 := by decide +kernel
private theorem check71_4 (_ht : gen71 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen71 4))) : let L := Subgroup.closure (Set.range (edgeGen gen71 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge71_4_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge71_4 j ∈ character.ker from by decide +kernel) j

private def edge71_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge71_5_eq : edgeGen gen71 5 = edge71_5 := by decide +kernel
private def reps71_5 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private def next71_5 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 0, 4, 1, 0, 5], ![2, 6, 7, 2, 6, 8], ![3, 9, 8, 3, 9, 7], ![4, 10, 11, 4, 10, 12], ![5, 13, 12, 5, 13, 11], ![6, 2, 14, 6, 2, 15], ![7, 16, 17, 7, 16, 18], ![8, 19, 18, 8, 19, 17], ![9, 3, 15, 9, 3, 14], ![10, 4, 20, 10, 4, 21], ![11, 22, 23, 11, 22, 24], ![12, 25, 24, 12, 25, 23], ![13, 5, 21, 13, 5, 20], ![14, 26, 27, 14, 26, 28], ![15, 29, 28, 15, 29, 27], ![16, 7, 30, 16, 7, 31], ![17, 32, 33, 17, 32, 34], ![18, 35, 34, 18, 35, 33], ![19, 8, 31, 19, 8, 30], ![20, 36, 37, 20, 36, 38], ![21, 39, 38, 21, 39, 37], ![22, 11, 40, 22, 11, 41], ![23, 42, 43, 23, 42, 44], ![24, 45, 44, 24, 45, 43], ![25, 12, 41, 25, 12, 40], ![26, 14, 42, 26, 14, 45], ![27, 40, 46, 27, 40, 47], ![28, 41, 47, 28, 41, 46], ![29, 15, 45, 29, 15, 42], ![30, 37, 1, 30, 37, 48], ![31, 38, 48, 31, 38, 1], ![32, 17, 49, 32, 17, 50], ![33, 43, 51, 33, 43, 52], ![34, 44, 52, 34, 44, 51], ![35, 18, 50, 35, 18, 49], ![36, 20, 32, 36, 20, 35], ![37, 30, 53, 37, 30, 54], ![38, 31, 54, 38, 31, 53], ![39, 21, 35, 39, 21, 32], ![40, 27, 0, 40, 27, 55], ![41, 28, 55, 41, 28, 0], ![42, 23, 56, 42, 23, 57], ![43, 33, 58, 43, 33, 59], ![44, 34, 59, 44, 34, 58], ![45, 24, 57, 45, 24, 56], ![46, 53, 60, 46, 53, 61], ![47, 54, 61, 47, 54, 60], ![48, 55, 5, 48, 55, 4], ![49, 56, 6, 49, 56, 9], ![50, 57, 9, 50, 57, 6], ![51, 60, 22, 51, 60, 25], ![52, 61, 25, 52, 61, 22], ![53, 46, 62, 53, 46, 63], ![54, 47, 63, 54, 47, 62], ![55, 48, 3, 55, 48, 2], ![56, 49, 10, 56, 49, 13], ![57, 50, 13, 57, 50, 10], ![58, 62, 16, 58, 62, 19], ![59, 63, 19, 59, 63, 16], ![60, 51, 36, 60, 51, 39], ![61, 52, 39, 61, 52, 36], ![62, 58, 26, 62, 58, 29], ![63, 59, 29, 63, 59, 26]]
private theorem transitions71_5 : ∀ a j, reps71_5 a * edge71_5 j = reps71_5 (next71_5 a j) := by decide +kernel
private theorem check71_5 (_ht : gen71 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen71 5))) : let L := Subgroup.closure (Set.range (edgeGen gen71 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge71_5_eq]
  right; left
  exact noncentric edge71_5 (⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps71_5 0 next71_5
    (by decide +kernel) transitions71_5 (by decide +kernel) (by decide +kernel)

private def edge71_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge71_6_eq : edgeGen gen71 6 = edge71_6 := by decide +kernel
private def words71_6 : ClosureWords 6 6 :=
  ⟨![[1, 3, 5], [], [0, 1], [1, 3, 5], [], [4, 0, 1]],
   ![[0, 2, 2, 2, 2, 2], [2, 0, 2, 2, 2], [0, 2, 0, 2], [0, 2, 0, 2, 5, 5], [2, 2, 2, 5], [2, 2, 2, 2]]⟩
private theorem check71_6 (_ht : gen71 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen71 6))) : let L := Subgroup.closure (Set.range (edgeGen gen71 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge71_6_eq]
  right; right
  refine ⟨102, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig102_closure]
  exact words71_6.sound _ _ _ (by decide +kernel)

private def edge71_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge71_7_eq : edgeGen gen71 7 = edge71_7 := by decide +kernel
private def reps71_7 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private def next71_7 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 0, 4, 1, 0, 5], ![2, 6, 7, 2, 6, 8], ![3, 9, 8, 3, 9, 7], ![4, 10, 11, 4, 10, 12], ![5, 13, 12, 5, 13, 11], ![6, 2, 14, 6, 2, 15], ![7, 16, 17, 7, 16, 18], ![8, 19, 18, 8, 19, 17], ![9, 3, 15, 9, 3, 14], ![10, 4, 20, 10, 4, 21], ![11, 22, 23, 11, 22, 24], ![12, 25, 24, 12, 25, 23], ![13, 5, 21, 13, 5, 20], ![14, 26, 27, 14, 26, 28], ![15, 29, 28, 15, 29, 27], ![16, 7, 30, 16, 7, 31], ![17, 32, 33, 17, 32, 34], ![18, 35, 34, 18, 35, 33], ![19, 8, 31, 19, 8, 30], ![20, 36, 37, 20, 36, 38], ![21, 39, 38, 21, 39, 37], ![22, 11, 40, 22, 11, 41], ![23, 42, 43, 23, 42, 44], ![24, 45, 44, 24, 45, 43], ![25, 12, 41, 25, 12, 40], ![26, 14, 42, 26, 14, 45], ![27, 40, 46, 27, 40, 47], ![28, 41, 47, 28, 41, 46], ![29, 15, 45, 29, 15, 42], ![30, 37, 1, 30, 37, 48], ![31, 38, 48, 31, 38, 1], ![32, 17, 49, 32, 17, 50], ![33, 43, 51, 33, 43, 52], ![34, 44, 52, 34, 44, 51], ![35, 18, 50, 35, 18, 49], ![36, 20, 32, 36, 20, 35], ![37, 30, 53, 37, 30, 54], ![38, 31, 54, 38, 31, 53], ![39, 21, 35, 39, 21, 32], ![40, 27, 0, 40, 27, 55], ![41, 28, 55, 41, 28, 0], ![42, 23, 56, 42, 23, 57], ![43, 33, 58, 43, 33, 59], ![44, 34, 59, 44, 34, 58], ![45, 24, 57, 45, 24, 56], ![46, 53, 60, 46, 53, 61], ![47, 54, 61, 47, 54, 60], ![48, 55, 5, 48, 55, 4], ![49, 56, 6, 49, 56, 9], ![50, 57, 9, 50, 57, 6], ![51, 60, 22, 51, 60, 25], ![52, 61, 25, 52, 61, 22], ![53, 46, 62, 53, 46, 63], ![54, 47, 63, 54, 47, 62], ![55, 48, 3, 55, 48, 2], ![56, 49, 10, 56, 49, 13], ![57, 50, 13, 57, 50, 10], ![58, 62, 16, 58, 62, 19], ![59, 63, 19, 59, 63, 16], ![60, 51, 36, 60, 51, 39], ![61, 52, 39, 61, 52, 36], ![62, 58, 26, 62, 58, 29], ![63, 59, 29, 63, 59, 26]]
private theorem transitions71_7 : ∀ a j, reps71_7 a * edge71_7 j = reps71_7 (next71_7 a j) := by decide +kernel
private theorem check71_7 (_ht : gen71 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen71 7))) : let L := Subgroup.closure (Set.range (edgeGen gen71 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge71_7_eq]
  right; left
  exact noncentric edge71_7 (⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps71_7 0 next71_7
    (by decide +kernel) transitions71_7 (by decide +kernel) (by decide +kernel)

private theorem node71 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 71)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 71 gen71 gen71_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check71_1
  · exact check71_2
  · exact check71_3
  · exact check71_4
  · exact check71_5
  · exact check71_6
  · exact check71_7

private def gen72 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private def generation72 : ClosureWords 3 7 :=
  ⟨![[5, 6], [1], [0]],
   ![[2], [1], [2, 2], [1, 1, 1, 2, 2, 2, 1, 2], [1, 1], [0, 1, 1, 1, 2, 2, 1, 2, 2], [1, 1, 1, 2, 2, 1, 2, 2]]⟩
private theorem gen72_closure : Subgroup.closure (Set.range gen72) = smallParityCensusNode 72 := by
  have h := generation72.sound gen72 orig72 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig72_closure] at h
  exact h

private def edge72_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge72_1_eq : edgeGen gen72 1 = edge72_1 := by decide +kernel
private theorem check72_1 (_ht : gen72 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen72 1))) : let L := Subgroup.closure (Set.range (edgeGen gen72 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge72_1_eq] at _ht ⊢
  right; left
  exact noncentric_short edge72_1 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen72 (pivot 1)) [1, 2, 1, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge72_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge72_2_eq : edgeGen gen72 2 = edge72_2 := by decide +kernel
private def words72_2 : ClosureWords 6 6 :=
  ⟨![[2], [], [0], [2], [2, 4, 5], [1, 0]],
   ![[2], [2, 2, 5, 2], [0], [2, 2], [0, 2, 2, 2, 4, 2], [2, 2, 5, 5]]⟩
private theorem check72_2 (_ht : gen72 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen72 2))) : let L := Subgroup.closure (Set.range (edgeGen gen72 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge72_2_eq]
  right; right
  refine ⟨101, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig101_closure]
  exact words72_2.sound _ _ _ (by decide +kernel)

private def edge72_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge72_3_eq : edgeGen gen72 3 = edge72_3 := by decide +kernel
private theorem check72_3 (_ht : gen72 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen72 3))) : let L := Subgroup.closure (Set.range (edgeGen gen72 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge72_3_eq] at _ht ⊢
  right; left
  exact noncentric_short edge72_3 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen72 (pivot 3)) [1, 2, 1, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge72_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge72_4_eq : edgeGen gen72 4 = edge72_4 := by decide +kernel
private theorem check72_4 (_ht : gen72 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen72 4))) : let L := Subgroup.closure (Set.range (edgeGen gen72 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge72_4_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge72_4 j ∈ character.ker from by decide +kernel) j

private def edge72_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge72_5_eq : edgeGen gen72 5 = edge72_5 := by decide +kernel
private theorem check72_5 (_ht : gen72 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen72 5))) : let L := Subgroup.closure (Set.range (edgeGen gen72 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge72_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge72_5 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen72 (pivot 5)) [1, 2, 1, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge72_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge72_6_eq : edgeGen gen72 6 = edge72_6 := by decide +kernel
private def words72_6 : ClosureWords 6 6 :=
  ⟨![[2], [], [0], [2], [4, 5], [1, 0]],
   ![[2], [2, 2, 5, 2], [0], [2, 2], [2, 2, 2, 4, 2], [2, 2, 5, 5]]⟩
private theorem check72_6 (_ht : gen72 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen72 6))) : let L := Subgroup.closure (Set.range (edgeGen gen72 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge72_6_eq]
  right; right
  refine ⟨101, (⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig101_closure]
  exact words72_6.sound _ _ _ (by decide +kernel)

private def edge72_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge72_7_eq : edgeGen gen72 7 = edge72_7 := by decide +kernel
private theorem check72_7 (_ht : gen72 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen72 7))) : let L := Subgroup.closure (Set.range (edgeGen gen72 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge72_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge72_7 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen72 (pivot 7)) [1, 2, 1, 2] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node72 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 72)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 72 gen72 gen72_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check72_1
  · exact check72_2
  · exact check72_3
  · exact check72_4
  · exact check72_5
  · exact check72_6
  · exact check72_7

private def gen73 : Fin 2 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation73 : ClosureWords 2 7 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 0, 1, 0, 1, 0, 1, 1], [0, 0, 1, 0, 1, 1, 0, 1, 1, 1], [0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1]]⟩
private theorem gen73_closure : Subgroup.closure (Set.range gen73) = smallParityCensusNode 73 := by
  have h := generation73.sound gen73 orig73 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig73_closure] at h
  exact h

private def edge73_1 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge73_1_eq : edgeGen gen73 1 = edge73_1 := by decide +kernel
private theorem check73_1 (_ht : gen73 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen73 1))) : let L := Subgroup.closure (Set.range (edgeGen gen73 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge73_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge73_1 j ∈ character.ker from by decide +kernel) j

private def edge73_2 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge73_2_eq : edgeGen gen73 2 = edge73_2 := by decide +kernel
private def reps73_2 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def next73_2 : Fin 64 → Fin 4 → Fin 64 :=
  ![![1, 0, 2, 3], ![4, 1, 5, 6], ![7, 2, 8, 9], ![10, 3, 11, 0], ![12, 4, 13, 14], ![15, 5, 16, 17], ![18, 6, 19, 1], ![20, 7, 21, 22], ![23, 8, 24, 25], ![26, 9, 27, 2], ![14, 10, 17, 28], ![22, 11, 25, 29], ![0, 12, 30, 31], ![32, 13, 33, 34], ![35, 14, 36, 4], ![37, 15, 38, 39], ![40, 16, 41, 42], ![43, 17, 44, 5], ![31, 18, 34, 45], ![39, 19, 42, 46], ![41, 20, 40, 36], ![38, 21, 37, 35], ![34, 22, 31, 7], ![33, 23, 32, 44], ![30, 24, 0, 43], ![42, 25, 39, 8], ![36, 26, 35, 47], ![44, 27, 43, 48], ![45, 28, 46, 10], ![47, 29, 48, 11], ![49, 30, 50, 51], ![52, 31, 53, 12], ![29, 32, 28, 54], ![55, 33, 56, 57], ![58, 34, 59, 13], ![3, 35, 51, 21], ![54, 36, 57, 20], ![56, 37, 55, 53], ![28, 38, 29, 52], ![51, 39, 3, 15], ![50, 40, 49, 59], ![2, 41, 1, 58], ![57, 42, 54, 16], ![53, 43, 52, 24], ![59, 44, 58, 23], ![21, 45, 20, 18], ![24, 46, 23, 19], ![13, 47, 12, 26], ![16, 48, 15, 27], ![46, 49, 45, 60], ![48, 50, 47, 61], ![62, 51, 63, 30], ![6, 52, 9, 38], ![60, 53, 61, 37], ![9, 54, 6, 32], ![8, 55, 7, 63], ![5, 56, 4, 62], ![61, 57, 60, 33], ![11, 58, 10, 41], ![63, 59, 62, 40], ![17, 60, 14, 49], ![25, 61, 22, 50], ![19, 62, 18, 56], ![27, 63, 26, 55]]
private theorem transitions73_2 : ∀ a j, reps73_2 a * edge73_2 j = reps73_2 (next73_2 a j) := by decide +kernel
private theorem check73_2 (_ht : gen73 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen73 2))) : let L := Subgroup.closure (Set.range (edgeGen gen73 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge73_2_eq]
  right; left
  exact noncentric edge73_2 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps73_2 0 next73_2
    (by decide +kernel) transitions73_2 (by decide +kernel) (by decide +kernel)

private def edge73_3 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge73_3_eq : edgeGen gen73 3 = edge73_3 := by decide +kernel
private def reps73_3 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def next73_3 : Fin 64 → Fin 4 → Fin 64 :=
  ![![0, 1, 2, 3], ![1, 4, 5, 6], ![2, 7, 0, 8], ![3, 9, 10, 4], ![4, 11, 12, 13], ![5, 14, 1, 15], ![6, 16, 17, 11], ![7, 18, 19, 17], ![8, 20, 21, 18], ![9, 13, 20, 22], ![10, 15, 3, 23], ![11, 24, 25, 26], ![12, 27, 4, 28], ![13, 29, 30, 24], ![14, 31, 32, 30], ![15, 33, 34, 31], ![16, 26, 33, 0], ![17, 28, 6, 35], ![18, 35, 36, 37], ![19, 38, 7, 34], ![20, 37, 9, 27], ![21, 34, 8, 32], ![22, 0, 31, 29], ![23, 25, 38, 33], ![24, 39, 40, 41], ![25, 42, 11, 43], ![26, 3, 44, 39], ![27, 2, 45, 44], ![28, 46, 47, 2], ![29, 41, 46, 1], ![30, 43, 13, 48], ![31, 48, 22, 49], ![32, 50, 14, 47], ![33, 49, 16, 42], ![34, 47, 15, 45], ![35, 40, 50, 46], ![36, 22, 18, 16], ![37, 44, 51, 40], ![38, 45, 23, 51], ![39, 36, 52, 9], ![40, 53, 24, 54], ![41, 6, 55, 36], ![42, 5, 56, 55], ![43, 10, 57, 5], ![44, 54, 26, 7], ![45, 58, 27, 57], ![46, 8, 29, 53], ![47, 57, 28, 56], ![48, 52, 58, 10], ![49, 55, 59, 52], ![50, 56, 35, 59], ![51, 59, 37, 58], ![52, 23, 39, 60], ![53, 12, 61, 20], ![54, 17, 62, 12], ![55, 60, 41, 14], ![56, 19, 42, 62], ![57, 62, 43, 61], ![58, 61, 48, 21], ![59, 21, 49, 19], ![60, 30, 63, 25], ![61, 32, 53, 63], ![62, 63, 54, 38], ![63, 51, 60, 50]]
private theorem transitions73_3 : ∀ a j, reps73_3 a * edge73_3 j = reps73_3 (next73_3 a j) := by decide +kernel
private theorem check73_3 (_ht : gen73 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen73 3))) : let L := Subgroup.closure (Set.range (edgeGen gen73 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge73_3_eq]
  right; left
  exact noncentric edge73_3 (⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps73_3 0 next73_3
    (by decide +kernel) transitions73_3 (by decide +kernel) (by decide +kernel)

private theorem node73 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 73)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 73 gen73 gen73_closure signatures2 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check73_1
  · exact check73_2
  · exact check73_3

private def gen74 : Fin 2 → SylowModel :=
  ![⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def generation74 : ClosureWords 2 7 :=
  ⟨![[1], [0]],
   ![[1], [0], [1, 1], [0, 0, 1, 0, 1, 0, 1, 1], [0, 0], [0, 0, 1, 0, 1, 1, 0, 1], [1, 1, 1, 1]]⟩
private theorem gen74_closure : Subgroup.closure (Set.range gen74) = smallParityCensusNode 74 := by
  have h := generation74.sound gen74 orig74 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig74_closure] at h
  exact h

private def edge74_1 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge74_1_eq : edgeGen gen74 1 = edge74_1 := by decide +kernel
private def words74_1 : ClosureWords 4 6 :=
  ⟨![[], [0], [3, 4], [0, 1, 5]],
   ![[1], [1, 1, 1, 3], [1, 1], [1, 1, 2, 3, 2, 3], [1, 1, 3, 2, 3], [1, 1, 1, 1]]⟩
private theorem check74_1 (_ht : gen74 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen74 1))) : let L := Subgroup.closure (Set.range (edgeGen gen74 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge74_1_eq]
  right; right
  refine ⟨102, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig102_closure]
  exact words74_1.sound _ _ _ (by decide +kernel)

private def edge74_2 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge74_2_eq : edgeGen gen74 2 = edge74_2 := by decide +kernel
private theorem check74_2 (_ht : gen74 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen74 2))) : let L := Subgroup.closure (Set.range (edgeGen gen74 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge74_2_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge74_2 j ∈ character.ker from by decide +kernel) j

private def edge74_3 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge74_3_eq : edgeGen gen74 3 = edge74_3 := by decide +kernel
private def words74_3 : ClosureWords 4 6 :=
  ⟨![[], [0, 3, 5], [4, 5], [1, 0]],
   ![[1, 1, 1, 3, 3], [1, 1, 1, 3], [1, 1], [1, 1, 2, 3, 2, 3], [1, 1, 1, 1, 2], [1, 1, 1, 1]]⟩
private theorem check74_3 (_ht : gen74 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen74 3))) : let L := Subgroup.closure (Set.range (edgeGen gen74 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge74_3_eq]
  right; right
  refine ⟨102, (⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig102_closure]
  exact words74_3.sound _ _ _ (by decide +kernel)

private theorem node74 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 74)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 74 gen74 gen74_closure signatures2 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check74_1
  · exact check74_2
  · exact check74_3

private def gen75 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation75 : ClosureWords 4 7 :=
  ⟨![[1], [4, 5], [5], [0]],
   ![[3], [0], [0, 0], [0, 0, 0, 1, 3, 0, 1, 3], [1, 2], [2], [3, 3]]⟩
private theorem gen75_closure : Subgroup.closure (Set.range gen75) = smallParityCensusNode 75 := by
  have h := generation75.sound gen75 orig75 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig75_closure] at h
  exact h

private def edge75_1 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_1_eq : edgeGen gen75 1 = edge75_1 := by decide +kernel
private theorem check75_1 (_ht : gen75 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen75 1))) : let L := Subgroup.closure (Set.range (edgeGen gen75 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge75_1 j ∈ character.ker from by decide +kernel) j

private def edge75_2 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_2_eq : edgeGen gen75 2 = edge75_2 := by decide +kernel
private def words75_2 : ClosureWords 8 6 :=
  ⟨![[1], [], [2], [0], [1, 5], [], [2], [0]],
   ![[3], [0], [2], [0, 0], [0, 0, 0, 3, 4, 3], [3, 3]]⟩
private theorem check75_2 (_ht : gen75 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen75 2))) : let L := Subgroup.closure (Set.range (edgeGen gen75 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_2_eq]
  right; right
  refine ⟨103, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig103_closure]
  exact words75_2.sound _ _ _ (by decide +kernel)

private def edge75_3 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_3_eq : edgeGen gen75 3 = edge75_3 := by decide +kernel
private def words75_3 : ClosureWords 8 6 :=
  ⟨![[], [1, 2, 3, 5], [2], [0, 2], [3, 5], [1, 2, 5], [2], [0, 2, 4]],
   ![[2, 3], [1, 2, 4], [2], [1, 1], [3, 3, 3, 7], [3, 3]]⟩
private theorem check75_3 (_ht : gen75 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen75 3))) : let L := Subgroup.closure (Set.range (edgeGen gen75 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_3_eq]
  right; right
  refine ⟨103, (⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig103_closure]
  exact words75_3.sound _ _ _ (by decide +kernel)

private def edge75_4 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_4_eq : edgeGen gen75 4 = edge75_4 := by decide +kernel
private theorem check75_4 (_ht : gen75 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen75 4))) : let L := Subgroup.closure (Set.range (edgeGen gen75 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_4_eq] at _ht ⊢
  right; left
  exact noncentric_short edge75_4 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen75 (pivot 4)) [3, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge75_5 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_5_eq : edgeGen gen75 5 = edge75_5 := by decide +kernel
private theorem check75_5 (_ht : gen75 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen75 5))) : let L := Subgroup.closure (Set.range (edgeGen gen75 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge75_5 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen75 (pivot 5)) [1, 5, 6] _ht
    (by decide +kernel) (by decide +kernel)

private def edge75_6 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_6_eq : edgeGen gen75 6 = edge75_6 := by decide +kernel
private theorem check75_6 (_ht : gen75 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen75 6))) : let L := Subgroup.closure (Set.range (edgeGen gen75 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge75_6 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen75 (pivot 6)) [2, 3, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge75_7 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_7_eq : edgeGen gen75 7 = edge75_7 := by decide +kernel
private theorem check75_7 (_ht : gen75 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen75 7))) : let L := Subgroup.closure (Set.range (edgeGen gen75 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge75_7 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen75 (pivot 7)) [1, 1, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge75_8 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_8_eq : edgeGen gen75 8 = edge75_8 := by decide +kernel
private def words75_8 : ClosureWords 8 6 :=
  ⟨![[0], [2, 4], [2], [], [0, 1, 5], [2, 4], [2], [5]],
   ![[0], [0, 0, 0, 4, 7], [2], [0, 0], [1, 2], [7]]⟩
private theorem check75_8 (_ht : gen75 (pivot 8) ∉ Subgroup.closure (Set.range (edgeGen gen75 8))) : let L := Subgroup.closure (Set.range (edgeGen gen75 8));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_8_eq]
  right; right
  refine ⟨97, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig97_closure]
  exact words75_8.sound _ _ _ (by decide +kernel)

private def edge75_9 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge75_9_eq : edgeGen gen75 9 = edge75_9 := by decide +kernel
private def words75_9 : ClosureWords 8 6 :=
  ⟨![[], [4], [2], [0, 1, 3, 4], [1, 3, 4], [4, 5], [2], [1, 0, 4]],
   ![[3, 4], [1, 3, 3, 4], [2], [3, 3], [1], [1, 5]]⟩
private theorem check75_9 (_ht : gen75 (pivot 9) ∉ Subgroup.closure (Set.range (edgeGen gen75 9))) : let L := Subgroup.closure (Set.range (edgeGen gen75 9));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_9_eq]
  right; right
  refine ⟨101, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig101_closure]
  exact words75_9.sound _ _ _ (by decide +kernel)

private def edge75_10 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_10_eq : edgeGen gen75 10 = edge75_10 := by decide +kernel
private def words75_10 : ClosureWords 8 6 :=
  ⟨![[1, 4], [], [2], [0, 5], [0, 1, 0], [], [2], [0, 5]],
   ![[3, 3, 3], [3, 4, 3], [2], [0, 0], [0, 0, 0, 3, 4, 3], [3, 3]]⟩
private theorem check75_10 (_ht : gen75 (pivot 10) ∉ Subgroup.closure (Set.range (edgeGen gen75 10))) : let L := Subgroup.closure (Set.range (edgeGen gen75 10));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_10_eq]
  right; right
  refine ⟨103, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig103_closure]
  exact words75_10.sound _ _ _ (by decide +kernel)

private def edge75_11 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge75_11_eq : edgeGen gen75 11 = edge75_11 := by decide +kernel
private def words75_11 : ClosureWords 8 6 :=
  ⟨![[], [0, 1, 0, 2, 3], [2], [1, 0, 3], [3, 5], [0, 1, 0, 2], [2], [0, 1]],
   ![[2, 3, 1, 4], [1, 2, 3, 3], [2], [1, 1], [3, 3, 4], [3, 7]]⟩
private theorem check75_11 (_ht : gen75 (pivot 11) ∉ Subgroup.closure (Set.range (edgeGen gen75 11))) : let L := Subgroup.closure (Set.range (edgeGen gen75 11));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_11_eq]
  right; right
  refine ⟨103, (⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig103_closure]
  exact words75_11.sound _ _ _ (by decide +kernel)

private def edge75_12 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_12_eq : edgeGen gen75 12 = edge75_12 := by decide +kernel
private theorem check75_12 (_ht : gen75 (pivot 12) ∉ Subgroup.closure (Set.range (edgeGen gen75 12))) : let L := Subgroup.closure (Set.range (edgeGen gen75 12));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_12_eq] at _ht ⊢
  right; left
  exact noncentric_short edge75_12 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen75 (pivot 12)) [3, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge75_13 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge75_13_eq : edgeGen gen75 13 = edge75_13 := by decide +kernel
private theorem check75_13 (_ht : gen75 (pivot 13) ∉ Subgroup.closure (Set.range (edgeGen gen75 13))) : let L := Subgroup.closure (Set.range (edgeGen gen75 13));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_13_eq] at _ht ⊢
  right; left
  exact noncentric_short edge75_13 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen75 (pivot 13)) [1, 5, 6] _ht
    (by decide +kernel) (by decide +kernel)

private def edge75_14 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge75_14_eq : edgeGen gen75 14 = edge75_14 := by decide +kernel
private theorem check75_14 (_ht : gen75 (pivot 14) ∉ Subgroup.closure (Set.range (edgeGen gen75 14))) : let L := Subgroup.closure (Set.range (edgeGen gen75 14));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_14_eq] at _ht ⊢
  right; left
  exact noncentric_short edge75_14 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen75 (pivot 14)) [2, 3, 3] _ht
    (by decide +kernel) (by decide +kernel)

private def edge75_15 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge75_15_eq : edgeGen gen75 15 = edge75_15 := by decide +kernel
private theorem check75_15 (_ht : gen75 (pivot 15) ∉ Subgroup.closure (Set.range (edgeGen gen75 15))) : let L := Subgroup.closure (Set.range (edgeGen gen75 15));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge75_15_eq] at _ht ⊢
  right; left
  exact noncentric_short edge75_15 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen75 (pivot 15)) [1, 1, 2] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node75 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 75)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 75 gen75 gen75_closure signatures4 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check75_1
  · exact check75_2
  · exact check75_3
  · exact check75_4
  · exact check75_5
  · exact check75_6
  · exact check75_7
  · exact check75_8
  · exact check75_9
  · exact check75_10
  · exact check75_11
  · exact check75_12
  · exact check75_13
  · exact check75_14
  · exact check75_15

private def gen76 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation76 : ClosureWords 3 7 :=
  ⟨![[1], [4, 5], [0]],
   ![[2], [0], [0, 0], [0, 0, 0, 1, 2, 0, 2], [0, 0, 0, 1, 0, 2, 2], [0, 0, 2, 0, 0, 2], [0, 0, 0, 1, 0, 1]]⟩
private theorem gen76_closure : Subgroup.closure (Set.range gen76) = smallParityCensusNode 76 := by
  have h := generation76.sound gen76 orig76 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig76_closure] at h
  exact h

private def edge76_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge76_1_eq : edgeGen gen76 1 = edge76_1 := by decide +kernel
private theorem check76_1 (_ht : gen76 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen76 1))) : let L := Subgroup.closure (Set.range (edgeGen gen76 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge76_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge76_1 j ∈ character.ker from by decide +kernel) j

private def edge76_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge76_2_eq : edgeGen gen76 2 = edge76_2 := by decide +kernel
private theorem check76_2 (_ht : gen76 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen76 2))) : let L := Subgroup.closure (Set.range (edgeGen gen76 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge76_2_eq] at _ht ⊢
  right; left
  exact noncentric_short edge76_2 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen76 (pivot 2)) [0, 0, 0, 2, 3, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge76_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge76_3_eq : edgeGen gen76 3 = edge76_3 := by decide +kernel
private theorem check76_3 (_ht : gen76 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen76 3))) : let L := Subgroup.closure (Set.range (edgeGen gen76 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge76_3_eq] at _ht ⊢
  right; left
  exact noncentric_short edge76_3 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen76 (pivot 3)) [4, 2, 5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge76_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge76_4_eq : edgeGen gen76 4 = edge76_4 := by decide +kernel
private def words76_4 : ClosureWords 6 6 :=
  ⟨![[0], [2, 4], [], [1, 4, 0], [2, 4], [2, 5]],
   ![[0], [0, 0, 0, 3, 1, 5], [0, 0, 3, 3, 5], [0, 0], [0, 0, 0, 1, 0, 5], [0, 0, 3, 3]]⟩
private theorem check76_4 (_ht : gen76 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen76 4))) : let L := Subgroup.closure (Set.range (edgeGen gen76 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge76_4_eq]
  right; right
  refine ⟨97, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig97_closure]
  exact words76_4.sound _ _ _ (by decide +kernel)

private def edge76_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge76_5_eq : edgeGen gen76 5 = edge76_5 := by decide +kernel
private def words76_5 : ClosureWords 6 6 :=
  ⟨![[], [4], [0, 3, 5], [0, 1, 0, 2], [4, 5], [0, 2]],
   ![[1, 2, 1, 2, 2], [2, 2, 2, 5, 3], [1, 2, 1, 5], [2, 2], [1], [1, 4]]⟩
private theorem check76_5 (_ht : gen76 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen76 5))) : let L := Subgroup.closure (Set.range (edgeGen gen76 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge76_5_eq]
  right; right
  refine ⟨101, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig101_closure]
  exact words76_5.sound _ _ _ (by decide +kernel)

private def edge76_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge76_6_eq : edgeGen gen76 6 = edge76_6 := by decide +kernel
private theorem check76_6 (_ht : gen76 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen76 6))) : let L := Subgroup.closure (Set.range (edgeGen gen76 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge76_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge76_6 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen76 (pivot 6)) [0, 0, 0, 2, 0, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge76_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge76_7_eq : edgeGen gen76 7 = edge76_7 := by decide +kernel
private theorem check76_7 (_ht : gen76 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen76 7))) : let L := Subgroup.closure (Set.range (edgeGen gen76 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge76_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge76_7 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen76 (pivot 7)) [1, 2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node76 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 76)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 76 gen76 gen76_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check76_1
  · exact check76_2
  · exact check76_3
  · exact check76_4
  · exact check76_5
  · exact check76_6
  · exact check76_7

private def gen77 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def generation77 : ClosureWords 3 7 :=
  ⟨![[4, 5], [0], [1]],
   ![[1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [0, 1, 2, 2, 1, 2, 2], [1, 2, 2, 1, 2, 2], [1, 1]]⟩
private theorem gen77_closure : Subgroup.closure (Set.range gen77) = smallParityCensusNode 77 := by
  have h := generation77.sound gen77 orig77 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig77_closure] at h
  exact h

private def edge77_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge77_1_eq : edgeGen gen77 1 = edge77_1 := by decide +kernel
private def words77_1 : ClosureWords 6 6 :=
  ⟨![[], [0], [1], [], [0], [1, 5]],
   ![[1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2], [1, 1]]⟩
private theorem check77_1 (_ht : gen77 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen77 1))) : let L := Subgroup.closure (Set.range (edgeGen gen77 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge77_1_eq]
  right; right
  refine ⟨104, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig104_closure]
  exact words77_1.sound _ _ _ (by decide +kernel)

private def edge77_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge77_2_eq : edgeGen gen77 2 = edge77_2 := by decide +kernel
private def words77_2 : ClosureWords 6 6 :=
  ⟨![[3, 4], [], [0], [3, 4], [5], [1, 0, 5]],
   ![[2], [2, 2, 5, 2], [2, 2], [2, 2, 4, 5, 5], [2, 0, 2, 5, 5], [4]]⟩
private theorem check77_2 (_ht : gen77 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen77 2))) : let L := Subgroup.closure (Set.range (edgeGen gen77 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge77_2_eq]
  right; right
  refine ⟨98, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig98_closure]
  exact words77_2.sound _ _ _ (by decide +kernel)

private def edge77_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge77_3_eq : edgeGen gen77 3 = edge77_3 := by decide +kernel
private def words77_3 : ClosureWords 6 6 :=
  ⟨![[], [0, 5], [3, 1], [], [0, 5], [3, 1, 5]],
   ![[1, 1, 1], [1, 2, 2, 2, 1, 2, 2], [1, 2, 5, 1], [1, 2, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2], [1, 1]]⟩
private theorem check77_3 (_ht : gen77 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen77 3))) : let L := Subgroup.closure (Set.range (edgeGen gen77 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge77_3_eq]
  right; right
  refine ⟨104, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig104_closure]
  exact words77_3.sound _ _ _ (by decide +kernel)

private def edge77_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge77_4_eq : edgeGen gen77 4 = edge77_4 := by decide +kernel
private theorem check77_4 (_ht : gen77 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen77 4))) : let L := Subgroup.closure (Set.range (edgeGen gen77 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge77_4_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge77_4 j ∈ character.ker from by decide +kernel) j

private def edge77_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge77_5_eq : edgeGen gen77 5 = edge77_5 := by decide +kernel
private def words77_5 : ClosureWords 6 6 :=
  ⟨![[], [0, 4], [1, 4, 5], [], [0, 4], [1, 4]],
   ![[2, 2, 1, 2, 5], [1, 2, 2, 1, 2, 2, 5], [2, 2], [1, 2, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2], [1, 1]]⟩
private theorem check77_5 (_ht : gen77 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen77 5))) : let L := Subgroup.closure (Set.range (edgeGen gen77 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge77_5_eq]
  right; right
  refine ⟨104, (⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig104_closure]
  exact words77_5.sound _ _ _ (by decide +kernel)

private def edge77_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge77_6_eq : edgeGen gen77 6 = edge77_6 := by decide +kernel
private def words77_6 : ClosureWords 6 6 :=
  ⟨![[4], [], [1, 4, 0], [4], [5], [0]],
   ![[5], [2, 0, 2, 5, 2], [5, 5], [2, 2, 5, 5], [0], [4]]⟩
private theorem check77_6 (_ht : gen77 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen77 6))) : let L := Subgroup.closure (Set.range (edgeGen gen77 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge77_6_eq]
  right; right
  refine ⟨102, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig102_closure]
  exact words77_6.sound _ _ _ (by decide +kernel)

private def edge77_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge77_7_eq : edgeGen gen77 7 = edge77_7 := by decide +kernel
private def words77_7 : ClosureWords 6 6 :=
  ⟨![[], [0, 4, 5], [0, 1, 0], [], [0, 4, 5], [1, 3]],
   ![[2, 2, 1, 2, 2], [1, 2, 1], [1, 2, 5, 1], [1, 2, 2, 2, 1, 2], [1, 2, 2, 1, 2, 2], [1, 1]]⟩
private theorem check77_7 (_ht : gen77 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen77 7))) : let L := Subgroup.closure (Set.range (edgeGen gen77 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge77_7_eq]
  right; right
  refine ⟨104, (⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig104_closure]
  exact words77_7.sound _ _ _ (by decide +kernel)

private theorem node77 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 77)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 77 gen77 gen77_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check77_1
  · exact check77_2
  · exact check77_3
  · exact check77_4
  · exact check77_5
  · exact check77_6
  · exact check77_7

private def gen78 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def generation78 : ClosureWords 3 7 :=
  ⟨![[4, 5], [0], [1]],
   ![[1], [2], [2, 2], [0, 1, 2, 2, 2, 1, 2], [0, 1, 1, 2, 2, 2, 2], [1, 1, 2, 2, 2, 2], [2, 2, 2, 2]]⟩
private theorem gen78_closure : Subgroup.closure (Set.range gen78) = smallParityCensusNode 78 := by
  have h := generation78.sound gen78 orig78 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig78_closure] at h
  exact h

private def edge78_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge78_1_eq : edgeGen gen78 1 = edge78_1 := by decide +kernel
private def words78_1 : ClosureWords 6 6 :=
  ⟨![[], [0], [1], [], [0], [1, 5]],
   ![[1], [2], [2, 2], [1, 2, 1, 2, 2, 5], [1, 1], [2, 2, 2, 2]]⟩
private theorem check78_1 (_ht : gen78 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen78 1))) : let L := Subgroup.closure (Set.range (edgeGen gen78 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge78_1_eq]
  right; right
  refine ⟨105, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig105_closure]
  exact words78_1.sound _ _ _ (by decide +kernel)

private def edge78_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge78_2_eq : edgeGen gen78 2 = edge78_2 := by decide +kernel
private def words78_2 : ClosureWords 6 6 :=
  ⟨![[3, 4], [], [0], [3, 4], [3, 5], [1, 4, 0]],
   ![[2], [0, 2, 2, 2, 5], [2, 2], [2, 2, 5, 5], [0, 2, 2, 5, 5], [2, 2, 2, 2]]⟩
private theorem check78_2 (_ht : gen78 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen78 2))) : let L := Subgroup.closure (Set.range (edgeGen gen78 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge78_2_eq]
  right; right
  refine ⟨98, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig98_closure]
  exact words78_2.sound _ _ _ (by decide +kernel)

private def edge78_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge78_3_eq : edgeGen gen78 3 = edge78_3 := by decide +kernel
private def words78_3 : ClosureWords 6 6 :=
  ⟨![[], [0, 5], [3, 1], [], [0, 5], [3, 1, 5]],
   ![[1, 2, 2, 2, 2], [1, 2, 1], [1, 1, 2, 2], [1, 2, 1, 2, 2, 5], [1, 1], [2, 2, 2, 2]]⟩
private theorem check78_3 (_ht : gen78 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen78 3))) : let L := Subgroup.closure (Set.range (edgeGen gen78 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge78_3_eq]
  right; right
  refine ⟨105, (⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig105_closure]
  exact words78_3.sound _ _ _ (by decide +kernel)

private def edge78_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge78_4_eq : edgeGen gen78 4 = edge78_4 := by decide +kernel
private theorem check78_4 (_ht : gen78 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen78 4))) : let L := Subgroup.closure (Set.range (edgeGen gen78 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge78_4_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge78_4 j ∈ character.ker from by decide +kernel) j

private def edge78_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge78_5_eq : edgeGen gen78 5 = edge78_5 := by decide +kernel
private def words78_5 : ClosureWords 6 6 :=
  ⟨![[], [0, 4, 5], [1, 4], [], [0, 4, 5], [1, 4, 5]],
   ![[2, 2, 1, 2, 2], [1, 1, 2], [2, 2], [1, 2, 1, 2, 2, 5], [1, 1], [2, 2, 2, 2]]⟩
private theorem check78_5 (_ht : gen78 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen78 5))) : let L := Subgroup.closure (Set.range (edgeGen gen78 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge78_5_eq]
  right; right
  refine ⟨105, (⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig105_closure]
  exact words78_5.sound _ _ _ (by decide +kernel)

private def edge78_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge78_6_eq : edgeGen gen78 6 = edge78_6 := by decide +kernel
private def words78_6 : ClosureWords 6 6 :=
  ⟨![[4], [], [0, 3], [4], [3], [1, 0, 5]],
   ![[2, 4], [2, 2, 2, 5], [2, 2], [4], [0], [2, 2, 2, 2]]⟩
private theorem check78_6 (_ht : gen78 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen78 6))) : let L := Subgroup.closure (Set.range (edgeGen gen78 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge78_6_eq]
  right; right
  refine ⟨102, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig102_closure]
  exact words78_6.sound _ _ _ (by decide +kernel)

private def edge78_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge78_7_eq : edgeGen gen78 7 = edge78_7 := by decide +kernel
private def words78_7 : ClosureWords 6 6 :=
  ⟨![[], [0, 4], [1, 3], [], [0, 4], [1, 3, 5]],
   ![[1, 1, 1], [1, 1, 1, 2, 1], [1, 1, 2, 2], [1, 2, 1, 2, 2, 5], [1, 1], [2, 2, 2, 2]]⟩
private theorem check78_7 (_ht : gen78 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen78 7))) : let L := Subgroup.closure (Set.range (edgeGen gen78 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge78_7_eq]
  right; right
  refine ⟨105, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig105_closure]
  exact words78_7.sound _ _ _ (by decide +kernel)

private theorem node78 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 78)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 78 gen78 gen78_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check78_1
  · exact check78_2
  · exact check78_3
  · exact check78_4
  · exact check78_5
  · exact check78_6
  · exact check78_7

private def gen79 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation79 : ClosureWords 3 7 :=
  ⟨![[1], [4], [0]],
   ![[2], [0], [0, 0], [0, 2, 0, 2, 0, 0], [1], [0, 2, 0, 0, 2, 0], [2, 2]]⟩
private theorem gen79_closure : Subgroup.closure (Set.range gen79) = smallParityCensusNode 79 := by
  have h := generation79.sound gen79 orig79 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig79_closure] at h
  exact h

private def edge79_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge79_1_eq : edgeGen gen79 1 = edge79_1 := by decide +kernel
private theorem check79_1 (_ht : gen79 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen79 1))) : let L := Subgroup.closure (Set.range (edgeGen gen79 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge79_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge79_1 j ∈ character.ker from by decide +kernel) j

private def edge79_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge79_2_eq : edgeGen gen79 2 = edge79_2 := by decide +kernel
private theorem check79_2 (_ht : gen79 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen79 2))) : let L := Subgroup.closure (Set.range (edgeGen gen79 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge79_2_eq] at _ht ⊢
  right; left
  exact noncentric_short edge79_2 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen79 (pivot 2)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge79_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge79_3_eq : edgeGen gen79 3 = edge79_3 := by decide +kernel
private theorem check79_3 (_ht : gen79 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen79 3))) : let L := Subgroup.closure (Set.range (edgeGen gen79 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge79_3_eq] at _ht ⊢
  right; left
  exact noncentric_short edge79_3 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen79 (pivot 3)) [2, 2, 4] _ht
    (by decide +kernel) (by decide +kernel)

private def edge79_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge79_4_eq : edgeGen gen79 4 = edge79_4 := by decide +kernel
private def reps79_4 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private def next79_4 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 2, 0, 3, 2, 4], ![5, 6, 1, 7, 6, 8], ![6, 0, 2, 9, 0, 10], ![11, 9, 3, 12, 9, 13], ![8, 10, 4, 13, 10, 0], ![14, 15, 5, 16, 15, 17], ![15, 1, 6, 18, 1, 19], ![20, 18, 7, 21, 18, 22], ![17, 19, 8, 22, 19, 1], ![23, 3, 9, 24, 3, 25], ![19, 4, 10, 25, 4, 2], ![26, 23, 11, 27, 23, 28], ![29, 24, 12, 30, 24, 31], ![28, 25, 13, 31, 25, 3], ![0, 32, 14, 33, 32, 27], ![32, 5, 15, 34, 5, 35], ![36, 34, 16, 37, 34, 26], ![27, 35, 17, 26, 35, 5], ![38, 7, 18, 39, 7, 40], ![35, 8, 19, 40, 8, 6], ![41, 38, 20, 4, 38, 30], ![42, 39, 21, 43, 39, 29], ![30, 40, 22, 29, 40, 7], ![44, 11, 23, 45, 11, 46], ![47, 12, 24, 48, 12, 49], ![46, 13, 25, 49, 13, 9], ![43, 44, 26, 42, 44, 16], ![4, 45, 27, 41, 45, 14], ![16, 46, 28, 14, 46, 11], ![37, 47, 29, 36, 47, 21], ![33, 48, 30, 0, 48, 20], ![21, 49, 31, 20, 49, 12], ![2, 14, 32, 50, 14, 45], ![51, 50, 33, 52, 50, 41], ![53, 16, 34, 54, 16, 44], ![45, 17, 35, 44, 17, 15], ![13, 53, 36, 8, 53, 43], ![55, 54, 37, 56, 54, 42], ![57, 20, 38, 10, 20, 48], ![58, 21, 39, 59, 21, 47], ![48, 22, 40, 47, 22, 18], ![56, 57, 41, 55, 57, 33], ![52, 58, 42, 51, 58, 37], ![3, 59, 43, 1, 59, 36], ![59, 26, 44, 58, 26, 34], ![10, 27, 45, 57, 27, 32], ![34, 28, 46, 32, 28, 23], ![54, 29, 47, 53, 29, 39], ![50, 30, 48, 2, 30, 38], ![39, 31, 49, 38, 31, 24], ![60, 33, 50, 61, 33, 57], ![22, 60, 51, 17, 60, 56], ![31, 61, 52, 28, 61, 55], ![25, 36, 53, 19, 36, 59], ![62, 37, 54, 63, 37, 58], ![12, 62, 55, 11, 62, 52], ![7, 63, 56, 5, 63, 51], ![63, 41, 57, 62, 41, 50], ![61, 42, 58, 60, 42, 54], ![9, 43, 59, 6, 43, 53], ![40, 51, 60, 35, 51, 63], ![49, 52, 61, 46, 52, 62], ![24, 55, 62, 23, 55, 61], ![18, 56, 63, 15, 56, 60]]
private theorem transitions79_4 : ∀ a j, reps79_4 a * edge79_4 j = reps79_4 (next79_4 a j) := by decide +kernel
private theorem check79_4 (_ht : gen79 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen79 4))) : let L := Subgroup.closure (Set.range (edgeGen gen79 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge79_4_eq]
  right; left
  exact noncentric edge79_4 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps79_4 0 next79_4
    (by decide +kernel) transitions79_4 (by decide +kernel) (by decide +kernel)

private def edge79_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge79_5_eq : edgeGen gen79 5 = edge79_5 := by decide +kernel
private def reps79_5 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩]
private def next79_5 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 3, 1, 4], ![1, 0, 5, 6, 0, 7], ![2, 5, 8, 9, 5, 10], ![3, 6, 11, 0, 6, 12], ![4, 7, 10, 13, 7, 14], ![5, 2, 15, 16, 2, 17], ![6, 3, 18, 1, 3, 19], ![7, 4, 17, 20, 4, 21], ![8, 15, 4, 22, 15, 23], ![9, 16, 24, 2, 16, 25], ![10, 17, 23, 26, 17, 27], ![11, 18, 28, 29, 18, 26], ![12, 19, 26, 30, 19, 22], ![13, 20, 31, 4, 20, 24], ![14, 21, 27, 28, 21, 2], ![15, 8, 7, 32, 8, 33], ![16, 9, 34, 5, 9, 35], ![17, 10, 33, 36, 10, 37], ![18, 11, 38, 39, 11, 36], ![19, 12, 36, 40, 12, 32], ![20, 13, 41, 7, 13, 34], ![21, 14, 37, 38, 14, 5], ![22, 32, 42, 8, 32, 11], ![23, 33, 14, 43, 33, 0], ![24, 34, 44, 45, 34, 43], ![25, 35, 43, 46, 35, 13], ![26, 36, 47, 10, 36, 42], ![27, 37, 0, 44, 37, 8], ![28, 38, 12, 14, 38, 47], ![29, 39, 48, 11, 39, 46], ![30, 40, 49, 12, 40, 48], ![31, 41, 9, 49, 41, 44], ![32, 22, 50, 15, 22, 18], ![33, 23, 21, 51, 23, 1], ![34, 24, 52, 53, 24, 51], ![35, 25, 51, 54, 25, 20], ![36, 26, 55, 17, 26, 50], ![37, 27, 1, 52, 27, 15], ![38, 28, 19, 21, 28, 55], ![39, 29, 56, 18, 29, 54], ![40, 30, 57, 19, 30, 56], ![41, 31, 16, 57, 31, 52], ![42, 50, 3, 58, 50, 28], ![43, 51, 59, 23, 51, 31], ![44, 52, 25, 27, 52, 59], ![45, 53, 30, 24, 53, 29], ![46, 54, 60, 25, 54, 30], ![47, 55, 22, 60, 55, 3], ![48, 56, 58, 59, 56, 60], ![49, 57, 29, 31, 57, 58], ![50, 42, 6, 61, 42, 38], ![51, 43, 62, 33, 43, 41], ![52, 44, 35, 37, 44, 62], ![53, 45, 40, 34, 45, 39], ![54, 46, 63, 35, 46, 40], ![55, 47, 32, 63, 47, 6], ![56, 48, 61, 62, 48, 63], ![57, 49, 39, 41, 49, 61], ![58, 61, 46, 42, 61, 45], ![59, 62, 13, 48, 62, 9], ![60, 63, 45, 47, 63, 49], ![61, 58, 54, 50, 58, 53], ![62, 59, 20, 56, 59, 16], ![63, 60, 53, 55, 60, 57]]
private theorem transitions79_5 : ∀ a j, reps79_5 a * edge79_5 j = reps79_5 (next79_5 a j) := by decide +kernel
private theorem check79_5 (_ht : gen79 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen79 5))) : let L := Subgroup.closure (Set.range (edgeGen gen79 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge79_5_eq]
  right; left
  exact noncentric edge79_5 (⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps79_5 0 next79_5
    (by decide +kernel) transitions79_5 (by decide +kernel) (by decide +kernel)

private def edge79_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge79_6_eq : edgeGen gen79 6 = edge79_6 := by decide +kernel
private theorem check79_6 (_ht : gen79 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen79 6))) : let L := Subgroup.closure (Set.range (edgeGen gen79 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge79_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge79_6 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen79 (pivot 6)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge79_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge79_7_eq : edgeGen gen79 7 = edge79_7 := by decide +kernel
private theorem check79_7 (_ht : gen79 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen79 7))) : let L := Subgroup.closure (Set.range (edgeGen gen79 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge79_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge79_7 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen79 (pivot 7)) [2, 5, 4] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node79 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 79)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 79 gen79 gen79_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check79_1
  · exact check79_2
  · exact check79_3
  · exact check79_4
  · exact check79_5
  · exact check79_6
  · exact check79_7

private def gen80 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation80 : ClosureWords 3 7 :=
  ⟨![[4], [1], [0]],
   ![[2], [1], [1, 1], [1, 1, 1, 2, 1, 2], [0], [1, 1, 2, 1, 1, 2], [2, 2]]⟩
private theorem gen80_closure : Subgroup.closure (Set.range gen80) = smallParityCensusNode 80 := by
  have h := generation80.sound gen80 orig80 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig80_closure] at h
  exact h

private def edge80_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge80_1_eq : edgeGen gen80 1 = edge80_1 := by decide +kernel
private theorem check80_1 (_ht : gen80 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen80 1))) : let L := Subgroup.closure (Set.range (edgeGen gen80 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge80_1_eq] at _ht ⊢
  right; left
  exact noncentric_short edge80_1 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen80 (pivot 1)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge80_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge80_2_eq : edgeGen gen80 2 = edge80_2 := by decide +kernel
private theorem check80_2 (_ht : gen80 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen80 2))) : let L := Subgroup.closure (Set.range (edgeGen gen80 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge80_2_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge80_2 j ∈ character.ker from by decide +kernel) j

private def edge80_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge80_3_eq : edgeGen gen80 3 = edge80_3 := by decide +kernel
private theorem check80_3 (_ht : gen80 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen80 3))) : let L := Subgroup.closure (Set.range (edgeGen gen80 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge80_3_eq] at _ht ⊢
  right; left
  exact noncentric_short edge80_3 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen80 (pivot 3)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge80_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge80_4_eq : edgeGen gen80 4 = edge80_4 := by decide +kernel
private def reps80_4 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private def next80_4 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 2, 0, 1, 3, 4], ![0, 5, 1, 0, 6, 7], ![5, 8, 2, 5, 9, 10], ![6, 11, 3, 6, 12, 13], ![7, 10, 4, 7, 13, 0], ![2, 14, 5, 2, 15, 16], ![3, 17, 6, 3, 18, 19], ![4, 16, 7, 4, 19, 1], ![14, 20, 8, 14, 21, 22], ![15, 23, 9, 15, 24, 25], ![16, 22, 10, 16, 25, 2], ![17, 26, 11, 17, 27, 28], ![18, 29, 12, 18, 30, 31], ![19, 28, 13, 19, 31, 3], ![8, 32, 14, 8, 33, 34], ![9, 35, 15, 9, 36, 37], ![10, 34, 16, 10, 37, 5], ![11, 38, 17, 11, 39, 40], ![12, 41, 18, 12, 42, 43], ![13, 40, 19, 13, 43, 6], ![32, 4, 20, 32, 44, 27], ![33, 45, 21, 33, 46, 26], ![34, 27, 22, 34, 26, 8], ![35, 47, 23, 35, 0, 30], ![36, 48, 24, 36, 49, 29], ![37, 30, 25, 37, 29, 9], ![38, 49, 26, 38, 48, 21], ![39, 0, 27, 39, 47, 20], ![40, 21, 28, 40, 20, 11], ![41, 46, 29, 41, 45, 24], ![42, 44, 30, 42, 4, 23], ![43, 24, 31, 43, 23, 12], ![20, 7, 32, 20, 50, 39], ![21, 51, 33, 21, 52, 38], ![22, 39, 34, 22, 38, 14], ![23, 53, 35, 23, 1, 42], ![24, 54, 36, 24, 55, 41], ![25, 42, 37, 25, 41, 15], ![26, 55, 38, 26, 54, 33], ![27, 1, 39, 27, 53, 32], ![28, 33, 40, 28, 32, 17], ![29, 52, 41, 29, 51, 36], ![30, 50, 42, 30, 7, 35], ![31, 36, 43, 31, 35, 18], ![50, 56, 44, 50, 57, 47], ![51, 3, 45, 51, 2, 49], ![52, 58, 46, 52, 59, 48], ![53, 59, 47, 53, 58, 44], ![54, 57, 48, 54, 56, 46], ![55, 13, 49, 55, 10, 45], ![44, 60, 50, 44, 61, 53], ![45, 6, 51, 45, 5, 55], ![46, 62, 52, 46, 63, 54], ![47, 63, 53, 47, 62, 50], ![48, 61, 54, 48, 60, 52], ![49, 19, 55, 49, 16, 51], ![60, 9, 56, 60, 8, 59], ![61, 12, 57, 61, 11, 58], ![62, 31, 58, 62, 28, 57], ![63, 25, 59, 63, 22, 56], ![56, 15, 60, 56, 14, 63], ![57, 18, 61, 57, 17, 62], ![58, 43, 62, 58, 40, 61], ![59, 37, 63, 59, 34, 60]]
private theorem transitions80_4 : ∀ a j, reps80_4 a * edge80_4 j = reps80_4 (next80_4 a j) := by decide +kernel
private theorem check80_4 (_ht : gen80 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen80 4))) : let L := Subgroup.closure (Set.range (edgeGen gen80 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge80_4_eq]
  right; left
  exact noncentric edge80_4 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps80_4 0 next80_4
    (by decide +kernel) transitions80_4 (by decide +kernel) (by decide +kernel)

private def edge80_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge80_5_eq : edgeGen gen80 5 = edge80_5 := by decide +kernel
private theorem check80_5 (_ht : gen80 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen80 5))) : let L := Subgroup.closure (Set.range (edgeGen gen80 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge80_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge80_5 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen80 (pivot 5)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge80_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge80_6_eq : edgeGen gen80 6 = edge80_6 := by decide +kernel
private def reps80_6 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩]
private def next80_6 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 0, 2, 1, 3, 4], ![0, 1, 5, 0, 6, 7], ![5, 2, 8, 5, 9, 10], ![6, 3, 11, 6, 10, 12], ![7, 4, 10, 7, 13, 8], ![2, 5, 14, 2, 15, 16], ![3, 6, 17, 3, 16, 18], ![4, 7, 16, 4, 19, 14], ![14, 8, 20, 14, 21, 22], ![15, 9, 23, 15, 22, 24], ![16, 10, 22, 16, 25, 20], ![17, 11, 26, 17, 27, 25], ![18, 12, 25, 18, 28, 26], ![19, 13, 29, 19, 20, 30], ![8, 14, 31, 8, 32, 33], ![9, 15, 34, 9, 33, 35], ![10, 16, 33, 10, 36, 31], ![11, 17, 37, 11, 38, 36], ![12, 18, 36, 12, 39, 37], ![13, 19, 40, 13, 31, 41], ![31, 20, 0, 31, 42, 43], ![32, 21, 12, 32, 43, 11], ![33, 22, 43, 33, 44, 0], ![34, 23, 13, 34, 45, 44], ![35, 24, 44, 35, 46, 13], ![36, 25, 47, 36, 0, 48], ![37, 26, 48, 37, 8, 47], ![38, 27, 49, 38, 47, 46], ![39, 28, 50, 39, 48, 45], ![40, 29, 9, 40, 50, 42], ![41, 30, 42, 41, 49, 9], ![20, 31, 1, 20, 51, 52], ![21, 32, 18, 21, 52, 17], ![22, 33, 52, 22, 53, 1], ![23, 34, 19, 23, 54, 53], ![24, 35, 53, 24, 55, 19], ![25, 36, 56, 25, 1, 57], ![26, 37, 57, 26, 14, 56], ![27, 38, 58, 27, 56, 55], ![28, 39, 59, 28, 57, 54], ![29, 40, 15, 29, 59, 51], ![30, 41, 51, 30, 58, 15], ![51, 42, 24, 51, 4, 23], ![52, 43, 4, 52, 26, 2], ![53, 44, 30, 53, 2, 29], ![54, 45, 60, 54, 30, 27], ![55, 46, 61, 55, 29, 28], ![56, 47, 21, 56, 61, 3], ![57, 48, 3, 57, 60, 21], ![58, 49, 28, 58, 23, 61], ![59, 50, 27, 59, 24, 60], ![42, 51, 35, 42, 7, 34], ![43, 52, 7, 43, 37, 5], ![44, 53, 41, 44, 5, 40], ![45, 54, 62, 45, 41, 38], ![46, 55, 63, 46, 40, 39], ![47, 56, 32, 47, 63, 6], ![48, 57, 6, 48, 62, 32], ![49, 58, 39, 49, 34, 63], ![50, 59, 38, 50, 35, 62], ![62, 60, 46, 62, 12, 49], ![63, 61, 45, 63, 11, 50], ![60, 62, 55, 60, 18, 58], ![61, 63, 54, 61, 17, 59]]
private theorem transitions80_6 : ∀ a j, reps80_6 a * edge80_6 j = reps80_6 (next80_6 a j) := by decide +kernel
private theorem check80_6 (_ht : gen80 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen80 6))) : let L := Subgroup.closure (Set.range (edgeGen gen80 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge80_6_eq]
  right; left
  exact noncentric edge80_6 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps80_6 0 next80_6
    (by decide +kernel) transitions80_6 (by decide +kernel) (by decide +kernel)

private def edge80_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge80_7_eq : edgeGen gen80 7 = edge80_7 := by decide +kernel
private theorem check80_7 (_ht : gen80 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen80 7))) : let L := Subgroup.closure (Set.range (edgeGen gen80 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge80_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge80_7 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen80 (pivot 7)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node80 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 80)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 80 gen80 gen80_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check80_1
  · exact check80_2
  · exact check80_3
  · exact check80_4
  · exact check80_5
  · exact check80_6
  · exact check80_7

private def gen81 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation81 : ClosureWords 4 7 :=
  ⟨![[1], [4, 6], [3], [0]],
   ![[3], [0], [0, 0], [2], [0, 0, 0, 1, 0], [2, 3, 2, 3], [0, 0, 0, 1, 0, 1]]⟩
private theorem gen81_closure : Subgroup.closure (Set.range gen81) = smallParityCensusNode 81 := by
  have h := generation81.sound gen81 orig81 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig81_closure] at h
  exact h

private def edge81_1 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_1_eq : edgeGen gen81 1 = edge81_1 := by decide +kernel
private theorem check81_1 (_ht : gen81 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen81 1))) : let L := Subgroup.closure (Set.range (edgeGen gen81 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge81_1 j ∈ character.ker from by decide +kernel) j

private def edge81_2 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_2_eq : edgeGen gen81 2 = edge81_2 := by decide +kernel
private def words81_2 : ClosureWords 8 6 :=
  ⟨![[1], [], [2], [0], [1, 5], [], [2], [0]],
   ![[3], [0], [2], [0, 0], [3, 3], [0, 0, 0, 4]]⟩
private theorem check81_2 (_ht : gen81 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen81 2))) : let L := Subgroup.closure (Set.range (edgeGen gen81 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_2_eq]
  right; right
  refine ⟨106, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig106_closure]
  exact words81_2.sound _ _ _ (by decide +kernel)

private def edge81_3 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_3_eq : edgeGen gen81 3 = edge81_3 := by decide +kernel
private def words81_3 : ClosureWords 8 6 :=
  ⟨![[], [1, 3, 4], [2], [0], [3, 5], [1, 4], [2], [0]],
   ![[3], [3, 3, 5], [2], [1, 1], [3, 3], [1, 1, 4]]⟩
private theorem check81_3 (_ht : gen81 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen81 3))) : let L := Subgroup.closure (Set.range (edgeGen gen81 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_3_eq]
  right; right
  refine ⟨106, (⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig106_closure]
  exact words81_3.sound _ _ _ (by decide +kernel)

private def edge81_4 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_4_eq : edgeGen gen81 4 = edge81_4 := by decide +kernel
private def words81_4 : ClosureWords 8 6 :=
  ⟨![[1], [2, 5], [], [0], [1], [2, 5], [], [0, 5]],
   ![[3], [0], [0, 0, 0, 1, 0], [0, 0], [3, 3], [3, 3, 3, 7]]⟩
private theorem check81_4 (_ht : gen81 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen81 4))) : let L := Subgroup.closure (Set.range (edgeGen gen81 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_4_eq]
  right; right
  refine ⟨107, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig107_closure]
  exact words81_4.sound _ _ _ (by decide +kernel)

private def edge81_5 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_5_eq : edgeGen gen81 5 = edge81_5 := by decide +kernel
private def words81_5 : ClosureWords 8 6 :=
  ⟨![[], [2, 5], [1, 3, 5], [0, 2], [3], [2], [1, 5], [0, 2]],
   ![[3, 5], [1, 5, 6], [5], [4], [3, 3], [1, 5]]⟩
private theorem check81_5 (_ht : gen81 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen81 5))) : let L := Subgroup.closure (Set.range (edgeGen gen81 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_5_eq]
  right; right
  refine ⟨107, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig107_closure]
  exact words81_5.sound _ _ _ (by decide +kernel)

private def edge81_6 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_6_eq : edgeGen gen81 6 = edge81_6 := by decide +kernel
private def words81_6 : ClosureWords 8 6 :=
  ⟨![[1], [], [2, 5], [0], [1, 5], [], [2, 5], [0]],
   ![[3], [0], [0, 0, 0, 2, 0], [0, 0], [3, 3], [0, 0, 0, 4]]⟩
private theorem check81_6 (_ht : gen81 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen81 6))) : let L := Subgroup.closure (Set.range (edgeGen gen81 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_6_eq]
  right; right
  refine ⟨108, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig108_closure]
  exact words81_6.sound _ _ _ (by decide +kernel)

private def edge81_7 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_7_eq : edgeGen gen81 7 = edge81_7 := by decide +kernel
private def words81_7 : ClosureWords 8 6 :=
  ⟨![[], [1, 3, 4], [1, 2, 3, 4], [0], [3, 5], [1, 4], [2, 1, 4], [0]],
   ![[3], [3, 3, 5], [5, 2], [1, 1], [3, 3], [1, 1, 4]]⟩
private theorem check81_7 (_ht : gen81 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen81 7))) : let L := Subgroup.closure (Set.range (edgeGen gen81 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_7_eq]
  right; right
  refine ⟨108, (⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig108_closure]
  exact words81_7.sound _ _ _ (by decide +kernel)

private def edge81_8 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_8_eq : edgeGen gen81 8 = edge81_8 := by decide +kernel
private def words81_8 : ClosureWords 8 6 :=
  ⟨![[0], [2, 4], [1, 5], [], [0], [2, 4], [1], [2, 5]],
   ![[0], [6], [2, 6, 7], [0, 0], [1, 2, 6, 7], [2, 6]]⟩
private theorem check81_8 (_ht : gen81 (pivot 8) ∉ Subgroup.closure (Set.range (edgeGen gen81 8))) : let L := Subgroup.closure (Set.range (edgeGen gen81 8));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_8_eq]
  right; right
  refine ⟨97, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig97_closure]
  exact words81_8.sound _ _ _ (by decide +kernel)

private def edge81_9 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge81_9_eq : edgeGen gen81 9 = edge81_9 := by decide +kernel
private def words81_9 : ClosureWords 8 6 :=
  ⟨![[], [2, 4], [1, 2, 5], [0, 1, 2, 3, 4], [2, 3, 5], [2, 4, 5], [1, 2, 5], [1, 0, 4]],
   ![[1, 2, 7], [2, 3, 7], [1, 3, 1, 7], [3, 3], [3, 1, 7], [1, 5]]⟩
private theorem check81_9 (_ht : gen81 (pivot 9) ∉ Subgroup.closure (Set.range (edgeGen gen81 9))) : let L := Subgroup.closure (Set.range (edgeGen gen81 9));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_9_eq]
  right; right
  refine ⟨101, (⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig101_closure]
  exact words81_9.sound _ _ _ (by decide +kernel)

private def edge81_10 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_10_eq : edgeGen gen81 10 = edge81_10 := by decide +kernel
private def words81_10 : ClosureWords 8 6 :=
  ⟨![[1, 2], [], [2, 5], [0, 5], [1, 2, 5], [], [2, 5], [0, 5]],
   ![[2, 3, 2], [2, 4], [0, 0, 0, 2, 4], [0, 0], [3, 3], [0, 0, 0, 4]]⟩
private theorem check81_10 (_ht : gen81 (pivot 10) ∉ Subgroup.closure (Set.range (edgeGen gen81 10))) : let L := Subgroup.closure (Set.range (edgeGen gen81 10));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_10_eq]
  right; right
  refine ⟨106, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig106_closure]
  exact words81_10.sound _ _ _ (by decide +kernel)

private def edge81_11 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge81_11_eq : edgeGen gen81 11 = edge81_11 := by decide +kernel
private def words81_11 : ClosureWords 8 6 :=
  ⟨![[], [1, 2, 3, 4], [2, 5], [1, 2, 0, 3, 4], [3, 5], [1, 2, 4], [2, 5], [0, 1, 2, 4]],
   ![[5, 3], [1, 2, 3, 3], [1, 1, 2, 4], [1, 1], [3, 7], [1, 1, 4]]⟩
private theorem check81_11 (_ht : gen81 (pivot 11) ∉ Subgroup.closure (Set.range (edgeGen gen81 11))) : let L := Subgroup.closure (Set.range (edgeGen gen81 11));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_11_eq]
  right; right
  refine ⟨106, (⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig106_closure]
  exact words81_11.sound _ _ _ (by decide +kernel)

private def edge81_12 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_12_eq : edgeGen gen81 12 = edge81_12 := by decide +kernel
private def words81_12 : ClosureWords 8 6 :=
  ⟨![[1], [2, 5], [], [0], [1], [2, 5], [], [0, 5]],
   ![[3], [0], [0, 0, 0, 1, 0], [0, 0], [3, 7], [3, 3, 3, 7]]⟩
private theorem check81_12 (_ht : gen81 (pivot 12) ∉ Subgroup.closure (Set.range (edgeGen gen81 12))) : let L := Subgroup.closure (Set.range (edgeGen gen81 12));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_12_eq]
  right; right
  refine ⟨109, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig109_closure]
  exact words81_12.sound _ _ _ (by decide +kernel)

private def edge81_13 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge81_13_eq : edgeGen gen81 13 = edge81_13 := by decide +kernel
private def words81_13 : ClosureWords 8 6 :=
  ⟨![[], [2, 5], [1, 3, 5], [0, 2, 1, 3], [3], [2], [1, 5], [0, 2, 1]],
   ![[1, 3, 6], [1, 5, 6], [5], [4], [3, 7], [1, 5]]⟩
private theorem check81_13 (_ht : gen81 (pivot 13) ∉ Subgroup.closure (Set.range (edgeGen gen81 13))) : let L := Subgroup.closure (Set.range (edgeGen gen81 13));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_13_eq]
  right; right
  refine ⟨109, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig109_closure]
  exact words81_13.sound _ _ _ (by decide +kernel)

private def edge81_14 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge81_14_eq : edgeGen gen81 14 = edge81_14 := by decide +kernel
private def words81_14 : ClosureWords 8 6 :=
  ⟨![[2, 1, 4], [], [2], [0, 5], [1, 2, 4], [], [2], [0, 5]],
   ![[2, 3, 2], [0, 3, 2, 3], [2], [0, 4], [3, 3], [0, 0, 0, 4]]⟩
private theorem check81_14 (_ht : gen81 (pivot 14) ∉ Subgroup.closure (Set.range (edgeGen gen81 14))) : let L := Subgroup.closure (Set.range (edgeGen gen81 14));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_14_eq]
  right; right
  refine ⟨108, (⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig108_closure]
  exact words81_14.sound _ _ _ (by decide +kernel)

private def edge81_15 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge81_15_eq : edgeGen gen81 15 = edge81_15 := by decide +kernel
private def words81_15 : ClosureWords 8 6 :=
  ⟨![[], [1, 2, 3], [1, 3, 5], [0, 2, 1, 3], [3], [2, 1], [1, 5], [0, 2, 1]],
   ![[5, 3], [1, 1, 2], [1, 6], [4], [3, 7], [1, 1, 4]]⟩
private theorem check81_15 (_ht : gen81 (pivot 15) ∉ Subgroup.closure (Set.range (edgeGen gen81 15))) : let L := Subgroup.closure (Set.range (edgeGen gen81 15));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge81_15_eq]
  right; right
  refine ⟨108, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig108_closure]
  exact words81_15.sound _ _ _ (by decide +kernel)

private theorem node81 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 81)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 81 gen81 gen81_closure signatures4 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check81_1
  · exact check81_2
  · exact check81_3
  · exact check81_4
  · exact check81_5
  · exact check81_6
  · exact check81_7
  · exact check81_8
  · exact check81_9
  · exact check81_10
  · exact check81_11
  · exact check81_12
  · exact check81_13
  · exact check81_14
  · exact check81_15

private def gen82 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation82 : ClosureWords 3 7 :=
  ⟨![[1], [1, 1, 2], [0]],
   ![[2], [0], [0, 0, 1], [0, 0, 0, 2, 0, 1, 2], [0, 0, 0, 2, 0, 2, 2, 2], [1, 2, 1, 2], [1, 2, 1, 2, 2, 2]]⟩
private theorem gen82_closure : Subgroup.closure (Set.range gen82) = smallParityCensusNode 82 := by
  have h := generation82.sound gen82 orig82 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig82_closure] at h
  exact h

private def edge82_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge82_1_eq : edgeGen gen82 1 = edge82_1 := by decide +kernel
private theorem check82_1 (_ht : gen82 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen82 1))) : let L := Subgroup.closure (Set.range (edgeGen gen82 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge82_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge82_1 j ∈ character.ker from by decide +kernel) j

private def edge82_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge82_2_eq : edgeGen gen82 2 = edge82_2 := by decide +kernel
private theorem check82_2 (_ht : gen82 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen82 2))) : let L := Subgroup.closure (Set.range (edgeGen gen82 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge82_2_eq] at _ht ⊢
  right; left
  exact noncentric_short edge82_2 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen82 (pivot 2)) [0, 0] _ht
    (by decide +kernel) (by decide +kernel)

private def edge82_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge82_3_eq : edgeGen gen82 3 = edge82_3 := by decide +kernel
private theorem check82_3 (_ht : gen82 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen82 3))) : let L := Subgroup.closure (Set.range (edgeGen gen82 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge82_3_eq] at _ht ⊢
  right; left
  exact noncentric_short edge82_3 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen82 (pivot 3)) [1] _ht
    (by decide +kernel) (by decide +kernel)

private def edge82_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge82_4_eq : edgeGen gen82 4 = edge82_4 := by decide +kernel
private def words82_4 : ClosureWords 6 6 :=
  ⟨![[2, 4, 0], [1, 2], [], [0, 2], [1, 2, 5], [2, 5]],
   ![[1, 3, 4, 5], [4, 5], [1, 4, 5], [3, 3], [0, 0, 3, 0], [1, 4]]⟩
private theorem check82_4 (_ht : gen82 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen82 4))) : let L := Subgroup.closure (Set.range (edgeGen gen82 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge82_4_eq]
  right; right
  refine ⟨97, (⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig97_closure]
  exact words82_4.sound _ _ _ (by decide +kernel)

private def edge82_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge82_5_eq : edgeGen gen82 5 = edge82_5 := by decide +kernel
private def words82_5 : ClosureWords 6 6 :=
  ⟨![[], [1, 2], [0, 1, 3, 4], [2, 3, 4], [1, 2], [1, 0, 2, 4]],
   ![[1, 3, 2], [2, 1, 5], [1, 2, 1, 5], [2, 2], [2, 2, 2, 3, 5], [1, 2, 1, 2, 2, 2]]⟩
private theorem check82_5 (_ht : gen82 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen82 5))) : let L := Subgroup.closure (Set.range (edgeGen gen82 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge82_5_eq]
  right; right
  refine ⟨101, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig101_closure]
  exact words82_5.sound _ _ _ (by decide +kernel)

private def edge82_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge82_6_eq : edgeGen gen82 6 = edge82_6 := by decide +kernel
private theorem check82_6 (_ht : gen82 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen82 6))) : let L := Subgroup.closure (Set.range (edgeGen gen82 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge82_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge82_6 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen82 (pivot 6)) [0, 0] _ht
    (by decide +kernel) (by decide +kernel)

private def edge82_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge82_7_eq : edgeGen gen82 7 = edge82_7 := by decide +kernel
private theorem check82_7 (_ht : gen82 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen82 7))) : let L := Subgroup.closure (Set.range (edgeGen gen82 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge82_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge82_7 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen82 (pivot 7)) [1] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node82 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 82)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 82 gen82 gen82_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check82_1
  · exact check82_2
  · exact check82_3
  · exact check82_4
  · exact check82_5
  · exact check82_6
  · exact check82_7

private def gen83 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation83 : ClosureWords 3 7 :=
  ⟨![[1], [2, 4, 5, 6], [0]],
   ![[2], [0], [0, 0, 0, 1, 0, 2, 2], [0, 0], [0, 0, 1, 0, 1, 0], [2, 2], [0, 0, 1, 0, 0, 1]]⟩
private theorem gen83_closure : Subgroup.closure (Set.range gen83) = smallParityCensusNode 83 := by
  have h := generation83.sound gen83 orig83 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig83_closure] at h
  exact h

private def edge83_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge83_1_eq : edgeGen gen83 1 = edge83_1 := by decide +kernel
private theorem check83_1 (_ht : gen83 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen83 1))) : let L := Subgroup.closure (Set.range (edgeGen gen83 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge83_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge83_1 j ∈ character.ker from by decide +kernel) j

private def edge83_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge83_2_eq : edgeGen gen83 2 = edge83_2 := by decide +kernel
private def words83_2 : ClosureWords 6 6 :=
  ⟨![[1], [], [0], [2, 1, 4], [], [0]],
   ![[2], [0], [0, 0, 2, 2, 3, 0], [0, 0], [2, 2], [0, 0, 3, 3]]⟩
private theorem check83_2 (_ht : gen83 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen83 2))) : let L := Subgroup.closure (Set.range (edgeGen gen83 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge83_2_eq]
  right; right
  refine ⟨107, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig107_closure]
  exact words83_2.sound _ _ _ (by decide +kernel)

private def edge83_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge83_3_eq : edgeGen gen83 3 = edge83_3 := by decide +kernel
private def words83_3 : ClosureWords 6 6 :=
  ⟨![[], [1, 3, 4, 5], [0, 4, 5], [1, 2, 1, 4], [1, 4, 5], [0, 4, 5]],
   ![[1, 2, 2, 2, 3, 4, 3], [2, 2, 3, 4, 3], [1, 2, 2, 3, 1], [1, 1], [2, 2], [1, 3, 4, 3]]⟩
private theorem check83_3 (_ht : gen83 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen83 3))) : let L := Subgroup.closure (Set.range (edgeGen gen83 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge83_3_eq]
  right; right
  refine ⟨107, (⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig107_closure]
  exact words83_3.sound _ _ _ (by decide +kernel)

private def edge83_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge83_4_eq : edgeGen gen83 4 = edge83_4 := by decide +kernel
private theorem check83_4 (_ht : gen83 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen83 4))) : let L := Subgroup.closure (Set.range (edgeGen gen83 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge83_4_eq] at _ht ⊢
  right; left
  exact noncentric_short edge83_4 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen83 (pivot 4)) [] _ht
    (by decide +kernel) (by decide +kernel)

private def edge83_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge83_5_eq : edgeGen gen83 5 = edge83_5 := by decide +kernel
private theorem check83_5 (_ht : gen83 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen83 5))) : let L := Subgroup.closure (Set.range (edgeGen gen83 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge83_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge83_5 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen83 (pivot 5)) [2, 2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge83_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge83_6_eq : edgeGen gen83 6 = edge83_6 := by decide +kernel
private theorem check83_6 (_ht : gen83 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen83 6))) : let L := Subgroup.closure (Set.range (edgeGen gen83 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge83_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge83_6 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen83 (pivot 6)) [2, 2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge83_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge83_7_eq : edgeGen gen83 7 = edge83_7 := by decide +kernel
private theorem check83_7 (_ht : gen83 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen83 7))) : let L := Subgroup.closure (Set.range (edgeGen gen83 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge83_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge83_7 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen83 (pivot 7)) [2, 2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node83 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 83)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 83 gen83 gen83_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check83_1
  · exact check83_2
  · exact check83_3
  · exact check83_4
  · exact check83_5
  · exact check83_6
  · exact check83_7

private def gen84 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation84 : ClosureWords 3 7 :=
  ⟨![[1], [2], [0]],
   ![[2], [0], [1], [0, 0], [0, 0, 0, 1, 0, 1], [2, 2], [0, 0, 1, 0, 0, 1]]⟩
private theorem gen84_closure : Subgroup.closure (Set.range gen84) = smallParityCensusNode 84 := by
  have h := generation84.sound gen84 orig84 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig84_closure] at h
  exact h

private def edge84_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge84_1_eq : edgeGen gen84 1 = edge84_1 := by decide +kernel
private theorem check84_1 (_ht : gen84 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen84 1))) : let L := Subgroup.closure (Set.range (edgeGen gen84 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge84_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge84_1 j ∈ character.ker from by decide +kernel) j

private def edge84_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge84_2_eq : edgeGen gen84 2 = edge84_2 := by decide +kernel
private def words84_2 : ClosureWords 6 6 :=
  ⟨![[1], [], [0], [1, 2, 4], [], [0, 5]],
   ![[2], [0], [0, 0, 0, 2, 2, 3], [0, 0], [2, 2], [0, 0, 3, 3]]⟩
private theorem check84_2 (_ht : gen84 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen84 2))) : let L := Subgroup.closure (Set.range (edgeGen gen84 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge84_2_eq]
  right; right
  refine ⟨107, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig107_closure]
  exact words84_2.sound _ _ _ (by decide +kernel)

private def edge84_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge84_3_eq : edgeGen gen84 3 = edge84_3 := by decide +kernel
private def words84_3 : ClosureWords 6 6 :=
  ⟨![[], [1, 2, 3], [0, 2, 4, 5], [1, 2, 1, 4], [2, 1], [0, 2, 4, 5]],
   ![[1, 2, 1, 3], [2, 1, 2, 3], [1, 1, 2, 2, 3], [1, 3, 1, 3], [2, 2], [1, 3, 4, 3]]⟩
private theorem check84_3 (_ht : gen84 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen84 3))) : let L := Subgroup.closure (Set.range (edgeGen gen84 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge84_3_eq]
  right; right
  refine ⟨107, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig107_closure]
  exact words84_3.sound _ _ _ (by decide +kernel)

private def edge84_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge84_4_eq : edgeGen gen84 4 = edge84_4 := by decide +kernel
private theorem check84_4 (_ht : gen84 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen84 4))) : let L := Subgroup.closure (Set.range (edgeGen gen84 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge84_4_eq] at _ht ⊢
  right; left
  exact noncentric_short edge84_4 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen84 (pivot 4)) [0, 0] _ht
    (by decide +kernel) (by decide +kernel)

private def edge84_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge84_5_eq : edgeGen gen84 5 = edge84_5 := by decide +kernel
private theorem check84_5 (_ht : gen84 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen84 5))) : let L := Subgroup.closure (Set.range (edgeGen gen84 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge84_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge84_5 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen84 (pivot 5)) [2, 2, 5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge84_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge84_6_eq : edgeGen gen84 6 = edge84_6 := by decide +kernel
private theorem check84_6 (_ht : gen84 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen84 6))) : let L := Subgroup.closure (Set.range (edgeGen gen84 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge84_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge84_6 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen84 (pivot 6)) [0, 0, 2, 2, 5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge84_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge84_7_eq : edgeGen gen84 7 = edge84_7 := by decide +kernel
private theorem check84_7 (_ht : gen84 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen84 7))) : let L := Subgroup.closure (Set.range (edgeGen gen84 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge84_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge84_7 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen84 (pivot 7)) [2, 2, 5] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node84 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 84)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 84 gen84 gen84_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check84_1
  · exact check84_2
  · exact check84_3
  · exact check84_4
  · exact check84_5
  · exact check84_6
  · exact check84_7

private def gen85 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation85 : ClosureWords 3 7 :=
  ⟨![[1], [0, 0, 2, 4], [0]],
   ![[2], [0], [0, 1, 0, 0, 0, 2, 2], [0, 0], [0, 0, 1, 0, 1, 0], [0, 0, 1, 0, 0, 1, 2, 2], [0, 0, 1, 0, 0, 1]]⟩
private theorem gen85_closure : Subgroup.closure (Set.range gen85) = smallParityCensusNode 85 := by
  have h := generation85.sound gen85 orig85 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig85_closure] at h
  exact h

private def edge85_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge85_1_eq : edgeGen gen85 1 = edge85_1 := by decide +kernel
private theorem check85_1 (_ht : gen85 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen85 1))) : let L := Subgroup.closure (Set.range (edgeGen gen85 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge85_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge85_1 j ∈ character.ker from by decide +kernel) j

private def edge85_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge85_2_eq : edgeGen gen85 2 = edge85_2 := by decide +kernel
private def words85_2 : ClosureWords 6 6 :=
  ⟨![[1], [], [0], [2, 1, 4], [], [0]],
   ![[2], [0], [0, 0, 0, 2, 2, 3], [0, 0], [0, 0, 2, 2, 3, 3], [0, 0, 3, 3]]⟩
private theorem check85_2 (_ht : gen85 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen85 2))) : let L := Subgroup.closure (Set.range (edgeGen gen85 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge85_2_eq]
  right; right
  refine ⟨109, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig109_closure]
  exact words85_2.sound _ _ _ (by decide +kernel)

private def edge85_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge85_3_eq : edgeGen gen85 3 = edge85_3 := by decide +kernel
private def words85_3 : ClosureWords 6 6 :=
  ⟨![[], [0, 0, 1, 3], [0], [0, 0, 2, 3], [0, 0, 1], [0]],
   ![[2], [2, 2, 4], [1, 1, 2, 2, 3], [1, 1], [1, 2, 2, 3, 4, 3], [1, 3, 4, 3]]⟩
private theorem check85_3 (_ht : gen85 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen85 3))) : let L := Subgroup.closure (Set.range (edgeGen gen85 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge85_3_eq]
  right; right
  refine ⟨109, (⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig109_closure]
  exact words85_3.sound _ _ _ (by decide +kernel)

private def edge85_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge85_4_eq : edgeGen gen85 4 = edge85_4 := by decide +kernel
private theorem check85_4 (_ht : gen85 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen85 4))) : let L := Subgroup.closure (Set.range (edgeGen gen85 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge85_4_eq] at _ht ⊢
  right; left
  exact noncentric_short edge85_4 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen85 (pivot 4)) [] _ht
    (by decide +kernel) (by decide +kernel)

private def edge85_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge85_5_eq : edgeGen gen85 5 = edge85_5 := by decide +kernel
private theorem check85_5 (_ht : gen85 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen85 5))) : let L := Subgroup.closure (Set.range (edgeGen gen85 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge85_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge85_5 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen85 (pivot 5)) [2, 2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge85_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge85_6_eq : edgeGen gen85 6 = edge85_6 := by decide +kernel
private theorem check85_6 (_ht : gen85 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen85 6))) : let L := Subgroup.closure (Set.range (edgeGen gen85 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge85_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge85_6 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen85 (pivot 6)) [2, 2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge85_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge85_7_eq : edgeGen gen85 7 = edge85_7 := by decide +kernel
private theorem check85_7 (_ht : gen85 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen85 7))) : let L := Subgroup.closure (Set.range (edgeGen gen85 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge85_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge85_7 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen85 (pivot 7)) [2, 2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node85 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 85)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 85 gen85 gen85_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check85_1
  · exact check85_2
  · exact check85_3
  · exact check85_4
  · exact check85_5
  · exact check85_6
  · exact check85_7

private def gen86 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def generation86 : ClosureWords 3 7 :=
  ⟨![[1], [2], [0]],
   ![[2], [0], [1], [0, 0], [0, 0, 0, 1, 0, 1], [1, 2, 1, 2], [0, 0, 1, 0, 0, 1]]⟩
private theorem gen86_closure : Subgroup.closure (Set.range gen86) = smallParityCensusNode 86 := by
  have h := generation86.sound gen86 orig86 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig86_closure] at h
  exact h

private def edge86_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge86_1_eq : edgeGen gen86 1 = edge86_1 := by decide +kernel
private theorem check86_1 (_ht : gen86 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen86 1))) : let L := Subgroup.closure (Set.range (edgeGen gen86 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge86_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge86_1 j ∈ character.ker from by decide +kernel) j

private def edge86_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge86_2_eq : edgeGen gen86 2 = edge86_2 := by decide +kernel
private def words86_2 : ClosureWords 6 6 :=
  ⟨![[1], [], [0], [1, 2, 4], [], [0, 5]],
   ![[2], [0], [0, 0, 0, 2, 3, 5], [0, 0], [2, 5], [0, 0, 3, 3]]⟩
private theorem check86_2 (_ht : gen86 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen86 2))) : let L := Subgroup.closure (Set.range (edgeGen gen86 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge86_2_eq]
  right; right
  refine ⟨109, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig109_closure]
  exact words86_2.sound _ _ _ (by decide +kernel)

private def edge86_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge86_3_eq : edgeGen gen86 3 = edge86_3 := by decide +kernel
private def words86_3 : ClosureWords 6 6 :=
  ⟨![[], [1, 2, 3], [0, 2, 5], [0, 0, 2, 3], [2, 1], [0, 2, 5]],
   ![[1, 1, 2, 2, 2, 3], [1, 2, 2, 3], [1, 2, 1, 2, 3], [1, 3, 1, 3], [1, 2, 4, 2], [1, 3, 4, 3]]⟩
private theorem check86_3 (_ht : gen86 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen86 3))) : let L := Subgroup.closure (Set.range (edgeGen gen86 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge86_3_eq]
  right; right
  refine ⟨109, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig109_closure]
  exact words86_3.sound _ _ _ (by decide +kernel)

private def edge86_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge86_4_eq : edgeGen gen86 4 = edge86_4 := by decide +kernel
private theorem check86_4 (_ht : gen86 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen86 4))) : let L := Subgroup.closure (Set.range (edgeGen gen86 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge86_4_eq] at _ht ⊢
  right; left
  exact noncentric_short edge86_4 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen86 (pivot 4)) [0, 0] _ht
    (by decide +kernel) (by decide +kernel)

private def edge86_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge86_5_eq : edgeGen gen86 5 = edge86_5 := by decide +kernel
private theorem check86_5 (_ht : gen86 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen86 5))) : let L := Subgroup.closure (Set.range (edgeGen gen86 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge86_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge86_5 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen86 (pivot 5)) [2, 2, 5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge86_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge86_6_eq : edgeGen gen86 6 = edge86_6 := by decide +kernel
private theorem check86_6 (_ht : gen86 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen86 6))) : let L := Subgroup.closure (Set.range (edgeGen gen86 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge86_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge86_6 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen86 (pivot 6)) [0, 0, 2, 2, 5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge86_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge86_7_eq : edgeGen gen86 7 = edge86_7 := by decide +kernel
private theorem check86_7 (_ht : gen86 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen86 7))) : let L := Subgroup.closure (Set.range (edgeGen gen86 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge86_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge86_7 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen86 (pivot 7)) [2, 2, 5] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node86 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 86)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 86 gen86 gen86_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check86_1
  · exact check86_2
  · exact check86_3
  · exact check86_4
  · exact check86_5
  · exact check86_6
  · exact check86_7

private def gen87 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def generation87 : ClosureWords 3 7 :=
  ⟨![[1], [4, 6], [0]],
   ![[2], [0], [0, 0], [0, 2, 0, 2, 0, 0], [1, 2, 2], [0, 2, 0, 0, 2, 0], [2, 2]]⟩
private theorem gen87_closure : Subgroup.closure (Set.range gen87) = smallParityCensusNode 87 := by
  have h := generation87.sound gen87 orig87 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig87_closure] at h
  exact h

private def edge87_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge87_1_eq : edgeGen gen87 1 = edge87_1 := by decide +kernel
private theorem check87_1 (_ht : gen87 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen87 1))) : let L := Subgroup.closure (Set.range (edgeGen gen87 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge87_1_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge87_1 j ∈ character.ker from by decide +kernel) j

private def edge87_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge87_2_eq : edgeGen gen87 2 = edge87_2 := by decide +kernel
private theorem check87_2 (_ht : gen87 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen87 2))) : let L := Subgroup.closure (Set.range (edgeGen gen87 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge87_2_eq] at _ht ⊢
  right; left
  exact noncentric_short edge87_2 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen87 (pivot 2)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge87_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge87_3_eq : edgeGen gen87 3 = edge87_3 := by decide +kernel
private theorem check87_3 (_ht : gen87 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen87 3))) : let L := Subgroup.closure (Set.range (edgeGen gen87 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge87_3_eq] at _ht ⊢
  right; left
  exact noncentric_short edge87_3 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen87 (pivot 3)) [2, 2, 4] _ht
    (by decide +kernel) (by decide +kernel)

private def edge87_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge87_4_eq : edgeGen gen87 4 = edge87_4 := by decide +kernel
private def reps87_4 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def next87_4 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 2, 0, 3, 2, 4], ![5, 6, 1, 7, 6, 8], ![6, 0, 2, 9, 0, 10], ![11, 9, 3, 12, 9, 13], ![8, 10, 4, 13, 10, 0], ![14, 15, 5, 16, 15, 17], ![15, 1, 6, 18, 1, 19], ![20, 18, 7, 21, 18, 22], ![17, 19, 8, 22, 19, 1], ![23, 3, 9, 24, 3, 25], ![19, 4, 10, 25, 4, 2], ![26, 23, 11, 27, 23, 28], ![29, 24, 12, 30, 24, 31], ![28, 25, 13, 31, 25, 3], ![0, 32, 14, 33, 32, 27], ![32, 5, 15, 34, 5, 35], ![36, 34, 16, 37, 34, 26], ![27, 35, 17, 26, 35, 5], ![38, 7, 18, 39, 7, 40], ![35, 8, 19, 40, 8, 6], ![41, 38, 20, 4, 38, 30], ![42, 39, 21, 43, 39, 29], ![30, 40, 22, 29, 40, 7], ![44, 11, 23, 45, 11, 46], ![47, 12, 24, 48, 12, 49], ![46, 13, 25, 49, 13, 9], ![43, 44, 26, 42, 44, 16], ![4, 45, 27, 41, 45, 14], ![16, 46, 28, 14, 46, 11], ![37, 47, 29, 36, 47, 21], ![33, 48, 30, 0, 48, 20], ![21, 49, 31, 20, 49, 12], ![2, 14, 32, 50, 14, 45], ![51, 50, 33, 52, 50, 41], ![53, 16, 34, 54, 16, 44], ![45, 17, 35, 44, 17, 15], ![13, 53, 36, 8, 53, 43], ![55, 54, 37, 56, 54, 42], ![57, 20, 38, 10, 20, 48], ![58, 21, 39, 59, 21, 47], ![48, 22, 40, 47, 22, 18], ![56, 57, 41, 55, 57, 33], ![52, 58, 42, 51, 58, 37], ![3, 59, 43, 1, 59, 36], ![59, 26, 44, 58, 26, 34], ![10, 27, 45, 57, 27, 32], ![34, 28, 46, 32, 28, 23], ![54, 29, 47, 53, 29, 39], ![50, 30, 48, 2, 30, 38], ![39, 31, 49, 38, 31, 24], ![60, 33, 50, 61, 33, 57], ![22, 60, 51, 17, 60, 56], ![31, 61, 52, 28, 61, 55], ![25, 36, 53, 19, 36, 59], ![62, 37, 54, 63, 37, 58], ![12, 62, 55, 11, 62, 52], ![7, 63, 56, 5, 63, 51], ![63, 41, 57, 62, 41, 50], ![61, 42, 58, 60, 42, 54], ![9, 43, 59, 6, 43, 53], ![40, 51, 60, 35, 51, 63], ![49, 52, 61, 46, 52, 62], ![24, 55, 62, 23, 55, 61], ![18, 56, 63, 15, 56, 60]]
private theorem transitions87_4 : ∀ a j, reps87_4 a * edge87_4 j = reps87_4 (next87_4 a j) := by decide +kernel
private theorem check87_4 (_ht : gen87 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen87 4))) : let L := Subgroup.closure (Set.range (edgeGen gen87 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge87_4_eq]
  right; left
  exact noncentric edge87_4 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps87_4 0 next87_4
    (by decide +kernel) transitions87_4 (by decide +kernel) (by decide +kernel)

private def edge87_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge87_5_eq : edgeGen gen87 5 = edge87_5 := by decide +kernel
private def reps87_5 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩]
private def next87_5 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 3, 1, 4], ![1, 0, 5, 6, 0, 7], ![2, 5, 8, 9, 5, 10], ![3, 6, 11, 0, 6, 12], ![4, 7, 10, 13, 7, 14], ![5, 2, 15, 16, 2, 17], ![6, 3, 18, 1, 3, 19], ![7, 4, 17, 20, 4, 21], ![8, 15, 4, 22, 15, 23], ![9, 16, 24, 2, 16, 25], ![10, 17, 23, 26, 17, 27], ![11, 18, 28, 29, 18, 26], ![12, 19, 26, 30, 19, 22], ![13, 20, 31, 4, 20, 24], ![14, 21, 27, 28, 21, 2], ![15, 8, 7, 32, 8, 33], ![16, 9, 34, 5, 9, 35], ![17, 10, 33, 36, 10, 37], ![18, 11, 38, 39, 11, 36], ![19, 12, 36, 40, 12, 32], ![20, 13, 41, 7, 13, 34], ![21, 14, 37, 38, 14, 5], ![22, 32, 42, 8, 32, 11], ![23, 33, 14, 43, 33, 0], ![24, 34, 44, 45, 34, 43], ![25, 35, 43, 46, 35, 13], ![26, 36, 47, 10, 36, 42], ![27, 37, 0, 44, 37, 8], ![28, 38, 12, 14, 38, 47], ![29, 39, 48, 11, 39, 46], ![30, 40, 49, 12, 40, 48], ![31, 41, 9, 49, 41, 44], ![32, 22, 50, 15, 22, 18], ![33, 23, 21, 51, 23, 1], ![34, 24, 52, 53, 24, 51], ![35, 25, 51, 54, 25, 20], ![36, 26, 55, 17, 26, 50], ![37, 27, 1, 52, 27, 15], ![38, 28, 19, 21, 28, 55], ![39, 29, 56, 18, 29, 54], ![40, 30, 57, 19, 30, 56], ![41, 31, 16, 57, 31, 52], ![42, 50, 3, 58, 50, 28], ![43, 51, 59, 23, 51, 31], ![44, 52, 25, 27, 52, 59], ![45, 53, 30, 24, 53, 29], ![46, 54, 60, 25, 54, 30], ![47, 55, 22, 60, 55, 3], ![48, 56, 58, 59, 56, 60], ![49, 57, 29, 31, 57, 58], ![50, 42, 6, 61, 42, 38], ![51, 43, 62, 33, 43, 41], ![52, 44, 35, 37, 44, 62], ![53, 45, 40, 34, 45, 39], ![54, 46, 63, 35, 46, 40], ![55, 47, 32, 63, 47, 6], ![56, 48, 61, 62, 48, 63], ![57, 49, 39, 41, 49, 61], ![58, 61, 46, 42, 61, 45], ![59, 62, 13, 48, 62, 9], ![60, 63, 45, 47, 63, 49], ![61, 58, 54, 50, 58, 53], ![62, 59, 20, 56, 59, 16], ![63, 60, 53, 55, 60, 57]]
private theorem transitions87_5 : ∀ a j, reps87_5 a * edge87_5 j = reps87_5 (next87_5 a j) := by decide +kernel
private theorem check87_5 (_ht : gen87 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen87 5))) : let L := Subgroup.closure (Set.range (edgeGen gen87 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge87_5_eq]
  right; left
  exact noncentric edge87_5 (⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps87_5 0 next87_5
    (by decide +kernel) transitions87_5 (by decide +kernel) (by decide +kernel)

private def edge87_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge87_6_eq : edgeGen gen87 6 = edge87_6 := by decide +kernel
private theorem check87_6 (_ht : gen87 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen87 6))) : let L := Subgroup.closure (Set.range (edgeGen gen87 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge87_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge87_6 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen87 (pivot 6)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge87_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge87_7_eq : edgeGen gen87 7 = edge87_7 := by decide +kernel
private theorem check87_7 (_ht : gen87 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen87 7))) : let L := Subgroup.closure (Set.range (edgeGen gen87 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge87_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge87_7 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen87 (pivot 7)) [2, 5, 4] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node87 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 87)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 87 gen87 gen87_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check87_1
  · exact check87_2
  · exact check87_3
  · exact check87_4
  · exact check87_5
  · exact check87_6
  · exact check87_7

private def gen88 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def generation88 : ClosureWords 3 7 :=
  ⟨![[4, 6], [1], [0]],
   ![[2], [1], [1, 1], [1, 1, 1, 2, 1, 2], [0, 2, 2], [1, 1, 2, 1, 1, 2], [2, 2]]⟩
private theorem gen88_closure : Subgroup.closure (Set.range gen88) = smallParityCensusNode 88 := by
  have h := generation88.sound gen88 orig88 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig88_closure] at h
  exact h

private def edge88_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge88_1_eq : edgeGen gen88 1 = edge88_1 := by decide +kernel
private theorem check88_1 (_ht : gen88 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen88 1))) : let L := Subgroup.closure (Set.range (edgeGen gen88 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge88_1_eq] at _ht ⊢
  right; left
  exact noncentric_short edge88_1 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen88 (pivot 1)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge88_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge88_2_eq : edgeGen gen88 2 = edge88_2 := by decide +kernel
private theorem check88_2 (_ht : gen88 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen88 2))) : let L := Subgroup.closure (Set.range (edgeGen gen88 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge88_2_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge88_2 j ∈ character.ker from by decide +kernel) j

private def edge88_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge88_3_eq : edgeGen gen88 3 = edge88_3 := by decide +kernel
private theorem check88_3 (_ht : gen88 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen88 3))) : let L := Subgroup.closure (Set.range (edgeGen gen88 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge88_3_eq] at _ht ⊢
  right; left
  exact noncentric_short edge88_3 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen88 (pivot 3)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge88_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge88_4_eq : edgeGen gen88 4 = edge88_4 := by decide +kernel
private def reps88_4 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def next88_4 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 2, 0, 1, 3, 4], ![0, 5, 1, 0, 6, 7], ![5, 8, 2, 5, 9, 10], ![6, 11, 3, 6, 12, 13], ![7, 10, 4, 7, 13, 0], ![2, 14, 5, 2, 15, 16], ![3, 17, 6, 3, 18, 19], ![4, 16, 7, 4, 19, 1], ![14, 20, 8, 14, 21, 22], ![15, 23, 9, 15, 24, 25], ![16, 22, 10, 16, 25, 2], ![17, 26, 11, 17, 27, 28], ![18, 29, 12, 18, 30, 31], ![19, 28, 13, 19, 31, 3], ![8, 32, 14, 8, 33, 34], ![9, 35, 15, 9, 36, 37], ![10, 34, 16, 10, 37, 5], ![11, 38, 17, 11, 39, 40], ![12, 41, 18, 12, 42, 43], ![13, 40, 19, 13, 43, 6], ![32, 4, 20, 32, 44, 27], ![33, 45, 21, 33, 46, 26], ![34, 27, 22, 34, 26, 8], ![35, 47, 23, 35, 0, 30], ![36, 48, 24, 36, 49, 29], ![37, 30, 25, 37, 29, 9], ![38, 49, 26, 38, 48, 21], ![39, 0, 27, 39, 47, 20], ![40, 21, 28, 40, 20, 11], ![41, 46, 29, 41, 45, 24], ![42, 44, 30, 42, 4, 23], ![43, 24, 31, 43, 23, 12], ![20, 7, 32, 20, 50, 39], ![21, 51, 33, 21, 52, 38], ![22, 39, 34, 22, 38, 14], ![23, 53, 35, 23, 1, 42], ![24, 54, 36, 24, 55, 41], ![25, 42, 37, 25, 41, 15], ![26, 55, 38, 26, 54, 33], ![27, 1, 39, 27, 53, 32], ![28, 33, 40, 28, 32, 17], ![29, 52, 41, 29, 51, 36], ![30, 50, 42, 30, 7, 35], ![31, 36, 43, 31, 35, 18], ![50, 56, 44, 50, 57, 47], ![51, 3, 45, 51, 2, 49], ![52, 58, 46, 52, 59, 48], ![53, 59, 47, 53, 58, 44], ![54, 57, 48, 54, 56, 46], ![55, 13, 49, 55, 10, 45], ![44, 60, 50, 44, 61, 53], ![45, 6, 51, 45, 5, 55], ![46, 62, 52, 46, 63, 54], ![47, 63, 53, 47, 62, 50], ![48, 61, 54, 48, 60, 52], ![49, 19, 55, 49, 16, 51], ![60, 9, 56, 60, 8, 59], ![61, 12, 57, 61, 11, 58], ![62, 31, 58, 62, 28, 57], ![63, 25, 59, 63, 22, 56], ![56, 15, 60, 56, 14, 63], ![57, 18, 61, 57, 17, 62], ![58, 43, 62, 58, 40, 61], ![59, 37, 63, 59, 34, 60]]
private theorem transitions88_4 : ∀ a j, reps88_4 a * edge88_4 j = reps88_4 (next88_4 a j) := by decide +kernel
private theorem check88_4 (_ht : gen88 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen88 4))) : let L := Subgroup.closure (Set.range (edgeGen gen88 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge88_4_eq]
  right; left
  exact noncentric edge88_4 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps88_4 0 next88_4
    (by decide +kernel) transitions88_4 (by decide +kernel) (by decide +kernel)

private def edge88_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge88_5_eq : edgeGen gen88 5 = edge88_5 := by decide +kernel
private theorem check88_5 (_ht : gen88 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen88 5))) : let L := Subgroup.closure (Set.range (edgeGen gen88 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge88_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge88_5 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen88 (pivot 5)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge88_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge88_6_eq : edgeGen gen88 6 = edge88_6 := by decide +kernel
private def reps88_6 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩]
private def next88_6 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 0, 2, 1, 3, 4], ![0, 1, 5, 0, 6, 7], ![5, 2, 8, 5, 9, 10], ![6, 3, 11, 6, 10, 12], ![7, 4, 10, 7, 13, 8], ![2, 5, 14, 2, 15, 16], ![3, 6, 17, 3, 16, 18], ![4, 7, 16, 4, 19, 14], ![14, 8, 20, 14, 21, 22], ![15, 9, 23, 15, 22, 24], ![16, 10, 22, 16, 25, 20], ![17, 11, 26, 17, 27, 25], ![18, 12, 25, 18, 28, 26], ![19, 13, 29, 19, 20, 30], ![8, 14, 31, 8, 32, 33], ![9, 15, 34, 9, 33, 35], ![10, 16, 33, 10, 36, 31], ![11, 17, 37, 11, 38, 36], ![12, 18, 36, 12, 39, 37], ![13, 19, 40, 13, 31, 41], ![31, 20, 0, 31, 42, 43], ![32, 21, 12, 32, 43, 11], ![33, 22, 43, 33, 44, 0], ![34, 23, 13, 34, 45, 44], ![35, 24, 44, 35, 46, 13], ![36, 25, 47, 36, 0, 48], ![37, 26, 48, 37, 8, 47], ![38, 27, 49, 38, 47, 46], ![39, 28, 50, 39, 48, 45], ![40, 29, 9, 40, 50, 42], ![41, 30, 42, 41, 49, 9], ![20, 31, 1, 20, 51, 52], ![21, 32, 18, 21, 52, 17], ![22, 33, 52, 22, 53, 1], ![23, 34, 19, 23, 54, 53], ![24, 35, 53, 24, 55, 19], ![25, 36, 56, 25, 1, 57], ![26, 37, 57, 26, 14, 56], ![27, 38, 58, 27, 56, 55], ![28, 39, 59, 28, 57, 54], ![29, 40, 15, 29, 59, 51], ![30, 41, 51, 30, 58, 15], ![51, 42, 24, 51, 4, 23], ![52, 43, 4, 52, 26, 2], ![53, 44, 30, 53, 2, 29], ![54, 45, 60, 54, 30, 27], ![55, 46, 61, 55, 29, 28], ![56, 47, 21, 56, 61, 3], ![57, 48, 3, 57, 60, 21], ![58, 49, 28, 58, 23, 61], ![59, 50, 27, 59, 24, 60], ![42, 51, 35, 42, 7, 34], ![43, 52, 7, 43, 37, 5], ![44, 53, 41, 44, 5, 40], ![45, 54, 62, 45, 41, 38], ![46, 55, 63, 46, 40, 39], ![47, 56, 32, 47, 63, 6], ![48, 57, 6, 48, 62, 32], ![49, 58, 39, 49, 34, 63], ![50, 59, 38, 50, 35, 62], ![62, 60, 46, 62, 12, 49], ![63, 61, 45, 63, 11, 50], ![60, 62, 55, 60, 18, 58], ![61, 63, 54, 61, 17, 59]]
private theorem transitions88_6 : ∀ a j, reps88_6 a * edge88_6 j = reps88_6 (next88_6 a j) := by decide +kernel
private theorem check88_6 (_ht : gen88 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen88 6))) : let L := Subgroup.closure (Set.range (edgeGen gen88 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge88_6_eq]
  right; left
  exact noncentric edge88_6 (⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps88_6 0 next88_6
    (by decide +kernel) transitions88_6 (by decide +kernel) (by decide +kernel)

private def edge88_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge88_7_eq : edgeGen gen88 7 = edge88_7 := by decide +kernel
private theorem check88_7 (_ht : gen88 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen88 7))) : let L := Subgroup.closure (Set.range (edgeGen gen88 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge88_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge88_7 (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen88 (pivot 7)) [2, 2] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node88 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 88)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 88 gen88 gen88_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check88_1
  · exact check88_2
  · exact check88_3
  · exact check88_4
  · exact check88_5
  · exact check88_6
  · exact check88_7

private def gen89 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def generation89 : ClosureWords 4 7 :=
  ⟨![[4, 6], [0], [3], [1]],
   ![[1], [3], [3, 3], [2], [0, 3, 3, 3, 3], [1, 2, 1, 2], [3, 3, 3, 3]]⟩
private theorem gen89_closure : Subgroup.closure (Set.range gen89) = smallParityCensusNode 89 := by
  have h := generation89.sound gen89 orig89 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig89_closure] at h
  exact h

private def edge89_1 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_1_eq : edgeGen gen89 1 = edge89_1 := by decide +kernel
private def words89_1 : ClosureWords 8 6 :=
  ⟨![[], [0], [2], [1], [], [0], [2], [1, 5]],
   ![[1], [3], [2], [3, 3], [1, 1], [3, 3, 3, 3]]⟩
private theorem check89_1 (_ht : gen89 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen89 1))) : let L := Subgroup.closure (Set.range (edgeGen gen89 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_1_eq]
  right; right
  refine ⟨110, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig110_closure]
  exact words89_1.sound _ _ _ (by decide +kernel)

private def edge89_2 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_2_eq : edgeGen gen89 2 = edge89_2 := by decide +kernel
private def words89_2 : ClosureWords 8 6 :=
  ⟨![[3, 4], [], [1, 3, 5], [0], [3, 4], [3, 5], [1, 3], [0, 3]],
   ![[3], [2, 5], [3, 3], [2, 5, 6], [0, 2, 5, 6], [2, 6]]⟩
private theorem check89_2 (_ht : gen89 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen89 2))) : let L := Subgroup.closure (Set.range (edgeGen gen89 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_2_eq]
  right; right
  refine ⟨98, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig98_closure]
  exact words89_2.sound _ _ _ (by decide +kernel)

private def edge89_3 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_3_eq : edgeGen gen89 3 = edge89_3 := by decide +kernel
private def words89_3 : ClosureWords 8 6 :=
  ⟨![[], [0, 5], [2, 5], [2, 1], [], [0, 5], [2, 5], [1, 2, 4]],
   ![[2, 1, 2], [2, 7], [1, 1, 1, 2, 1], [1, 1, 3, 7], [1, 1], [3, 3, 3, 3]]⟩
private theorem check89_3 (_ht : gen89 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen89 3))) : let L := Subgroup.closure (Set.range (edgeGen gen89 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_3_eq]
  right; right
  refine ⟨110, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig110_closure]
  exact words89_3.sound _ _ _ (by decide +kernel)

private def edge89_4 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_4_eq : edgeGen gen89 4 = edge89_4 := by decide +kernel
private def words89_4 : ClosureWords 8 6 :=
  ⟨![[2, 5], [0], [], [1], [2, 5], [0, 5], [], [1, 4, 5]],
   ![[1], [3], [0, 1, 1, 1, 5], [3, 3], [1, 1], [1, 1, 1, 5]]⟩
private theorem check89_4 (_ht : gen89 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen89 4))) : let L := Subgroup.closure (Set.range (edgeGen gen89 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_4_eq]
  right; right
  refine ⟨111, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig111_closure]
  exact words89_4.sound _ _ _ (by decide +kernel)

private def edge89_5 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_5_eq : edgeGen gen89 5 = edge89_5 := by decide +kernel
private def words89_5 : ClosureWords 8 6 :=
  ⟨![[], [0], [2, 5], [1], [], [0], [2, 5], [1, 5]],
   ![[1], [3], [1, 1, 1, 2, 1], [3, 3], [1, 1], [3, 3, 3, 3]]⟩
private theorem check89_5 (_ht : gen89 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen89 5))) : let L := Subgroup.closure (Set.range (edgeGen gen89 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_5_eq]
  right; right
  refine ⟨112, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig112_closure]
  exact words89_5.sound _ _ _ (by decide +kernel)

private def edge89_6 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_6_eq : edgeGen gen89 6 = edge89_6 := by decide +kernel
private def words89_6 : ClosureWords 8 6 :=
  ⟨![[2, 5], [], [0, 0, 0], [1], [2, 5], [4], [0], [0, 0, 1]],
   ![[6], [3], [0, 2, 2, 5], [3, 3], [5], [2, 2, 5]]⟩
private theorem check89_6 (_ht : gen89 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen89 6))) : let L := Subgroup.closure (Set.range (edgeGen gen89 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_6_eq]
  right; right
  refine ⟨113, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig113_closure]
  exact words89_6.sound _ _ _ (by decide +kernel)

private def edge89_7 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_7_eq : edgeGen gen89 7 = edge89_7 := by decide +kernel
private def words89_7 : ClosureWords 8 6 :=
  ⟨![[], [0, 5], [2], [1, 2], [], [0, 5], [2], [1, 2, 5]],
   ![[2, 1, 2], [3, 2], [2], [1, 1, 3, 3], [1, 1], [3, 3, 3, 3]]⟩
private theorem check89_7 (_ht : gen89 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen89 7))) : let L := Subgroup.closure (Set.range (edgeGen gen89 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_7_eq]
  right; right
  refine ⟨112, (⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig112_closure]
  exact words89_7.sound _ _ _ (by decide +kernel)

private def edge89_8 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge89_8_eq : edgeGen gen89 8 = edge89_8 := by decide +kernel
private theorem check89_8 (_ht : gen89 (pivot 8) ∉ Subgroup.closure (Set.range (edgeGen gen89 8))) : let L := Subgroup.closure (Set.range (edgeGen gen89 8));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_8_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge89_8 j ∈ character.ker from by decide +kernel) j

private def edge89_9 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_9_eq : edgeGen gen89 9 = edge89_9 := by decide +kernel
private def words89_9 : ClosureWords 8 6 :=
  ⟨![[], [0], [2], [1, 4], [], [0], [2], [1, 4, 5]],
   ![[1], [1, 1, 3], [2], [3, 3], [1, 1], [3, 3, 3, 3]]⟩
private theorem check89_9 (_ht : gen89 (pivot 9) ∉ Subgroup.closure (Set.range (edgeGen gen89 9))) : let L := Subgroup.closure (Set.range (edgeGen gen89 9));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_9_eq]
  right; right
  refine ⟨110, (⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig110_closure]
  exact words89_9.sound _ _ _ (by decide +kernel)

private def edge89_10 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_10_eq : edgeGen gen89 10 = edge89_10 := by decide +kernel
private def words89_10 : ClosureWords 8 6 :=
  ⟨![[3, 4, 5], [], [1, 5], [1, 4, 0], [3, 4, 5], [3], [1], [1, 0, 4]],
   ![[0, 3, 2], [6], [3, 5, 7], [5], [0, 2, 5, 6], [2, 6]]⟩
private theorem check89_10 (_ht : gen89 (pivot 10) ∉ Subgroup.closure (Set.range (edgeGen gen89 10))) : let L := Subgroup.closure (Set.range (edgeGen gen89 10));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_10_eq]
  right; right
  refine ⟨102, (⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig102_closure]
  exact words89_10.sound _ _ _ (by decide +kernel)

private def edge89_11 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_11_eq : edgeGen gen89 11 = edge89_11 := by decide +kernel
private def words89_11 : ClosureWords 8 6 :=
  ⟨![[], [0, 5], [2, 5], [1, 2, 5], [], [0, 5], [2, 5], [1, 2]],
   ![[2, 1, 2], [3, 2], [1, 1, 1, 2, 1], [1, 1, 3, 7], [1, 1], [3, 3, 3, 3]]⟩
private theorem check89_11 (_ht : gen89 (pivot 11) ∉ Subgroup.closure (Set.range (edgeGen gen89 11))) : let L := Subgroup.closure (Set.range (edgeGen gen89 11));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_11_eq]
  right; right
  refine ⟨110, (⟨⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig110_closure]
  exact words89_11.sound _ _ _ (by decide +kernel)

private def edge89_12 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_12_eq : edgeGen gen89 12 = edge89_12 := by decide +kernel
private def words89_12 : ClosureWords 8 6 :=
  ⟨![[2, 5], [0, 2], [], [1, 4], [2, 5], [0, 2, 5], [], [1, 5]],
   ![[0, 5], [0, 7, 0], [0, 1, 1, 1, 5], [3, 3], [1, 1], [1, 1, 1, 5]]⟩
private theorem check89_12 (_ht : gen89 (pivot 12) ∉ Subgroup.closure (Set.range (edgeGen gen89 12))) : let L := Subgroup.closure (Set.range (edgeGen gen89 12));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_12_eq]
  right; right
  refine ⟨111, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig111_closure]
  exact words89_12.sound _ _ _ (by decide +kernel)

private def edge89_13 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_13_eq : edgeGen gen89 13 = edge89_13 := by decide +kernel
private def words89_13 : ClosureWords 8 6 :=
  ⟨![[], [0], [2, 5], [1, 4], [], [0], [2, 5], [1, 4, 5]],
   ![[1], [1, 1, 3], [1, 1, 1, 2, 1], [3, 3], [1, 1], [3, 3, 3, 3]]⟩
private theorem check89_13 (_ht : gen89 (pivot 13) ∉ Subgroup.closure (Set.range (edgeGen gen89 13))) : let L := Subgroup.closure (Set.range (edgeGen gen89 13));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_13_eq]
  right; right
  refine ⟨112, (⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig112_closure]
  exact words89_13.sound _ _ _ (by decide +kernel)

private def edge89_14 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_14_eq : edgeGen gen89 14 = edge89_14 := by decide +kernel
private def words89_14 : ClosureWords 8 6 :=
  ⟨![[2, 5], [], [0, 2, 4], [0, 1, 2], [2, 5], [4], [0, 2, 5], [0, 2, 1]],
   ![[0, 6], [2, 3], [0, 2, 2, 5], [3, 3, 5], [5], [2, 2, 5]]⟩
private theorem check89_14 (_ht : gen89 (pivot 14) ∉ Subgroup.closure (Set.range (edgeGen gen89 14))) : let L := Subgroup.closure (Set.range (edgeGen gen89 14));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_14_eq]
  right; right
  refine ⟨113, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig113_closure]
  exact words89_14.sound _ _ _ (by decide +kernel)

private def edge89_15 : Fin 8 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge89_15_eq : edgeGen gen89 15 = edge89_15 := by decide +kernel
private def words89_15 : ClosureWords 8 6 :=
  ⟨![[], [0, 5], [2], [2, 1], [], [0, 5], [2], [2, 1, 5]],
   ![[2, 1, 2], [2, 3], [2], [1, 1, 3, 3], [1, 1], [3, 3, 3, 3]]⟩
private theorem check89_15 (_ht : gen89 (pivot 15) ∉ Subgroup.closure (Set.range (edgeGen gen89 15))) : let L := Subgroup.closure (Set.range (edgeGen gen89 15));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge89_15_eq]
  right; right
  refine ⟨112, (⟨⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig112_closure]
  exact words89_15.sound _ _ _ (by decide +kernel)

private theorem node89 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 89)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 89 gen89 gen89_closure signatures4 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check89_1
  · exact check89_2
  · exact check89_3
  · exact check89_4
  · exact check89_5
  · exact check89_6
  · exact check89_7
  · exact check89_8
  · exact check89_9
  · exact check89_10
  · exact check89_11
  · exact check89_12
  · exact check89_13
  · exact check89_14
  · exact check89_15

private def gen90 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private def generation90 : ClosureWords 3 7 :=
  ⟨![[0], [3], [1]],
   ![[0], [2], [0, 2, 0, 2, 1], [1], [0, 2, 2, 2, 0, 2], [0, 1, 0, 1], [2, 2, 2, 2]]⟩
private theorem gen90_closure : Subgroup.closure (Set.range gen90) = smallParityCensusNode 90 := by
  have h := generation90.sound gen90 orig90 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig90_closure] at h
  exact h

private def edge90_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge90_1_eq : edgeGen gen90 1 = edge90_1 := by decide +kernel
private def words90_1 : ClosureWords 6 6 :=
  ⟨![[], [1, 3, 4, 5], [4, 0], [3, 5], [1, 3, 4], [0, 3]],
   ![[1, 5, 4], [1, 2, 2, 5, 2], [5, 5], [1, 3, 4], [2, 2, 3, 5, 2], [1, 4]]⟩
private theorem check90_1 (_ht : gen90 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen90 1))) : let L := Subgroup.closure (Set.range (edgeGen gen90 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge90_1_eq]
  right; right
  refine ⟨98, (⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig98_closure]
  exact words90_1.sound _ _ _ (by decide +kernel)

private def edge90_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge90_2_eq : edgeGen gen90 2 = edge90_2 := by decide +kernel
private def reps90_2 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private def next90_2 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 0, 2, 3, 0, 4], ![5, 1, 6, 7, 1, 8], ![9, 2, 10, 11, 2, 12], ![7, 3, 13, 5, 3, 14], ![15, 4, 12, 16, 4, 10], ![17, 5, 4, 18, 5, 2], ![19, 6, 20, 21, 6, 22], ![18, 7, 23, 17, 7, 24], ![25, 8, 22, 26, 8, 20], ![4, 9, 27, 23, 9, 28], ![29, 10, 30, 20, 10, 31], ![23, 11, 32, 4, 11, 33], ![34, 12, 31, 22, 12, 30], ![21, 13, 29, 19, 13, 34], ![26, 14, 34, 25, 14, 29], ![2, 15, 28, 24, 15, 27], ![24, 16, 33, 2, 16, 32], ![0, 17, 8, 35, 17, 6], ![35, 18, 14, 0, 18, 13], ![8, 19, 36, 14, 19, 37], ![38, 20, 39, 12, 20, 40], ![14, 21, 41, 8, 21, 42], ![43, 22, 40, 10, 22, 39], ![16, 23, 38, 15, 23, 43], ![11, 24, 43, 9, 24, 38], ![6, 25, 37, 13, 25, 36], ![13, 26, 42, 6, 26, 41], ![41, 27, 44, 36, 27, 45], ![42, 28, 45, 37, 28, 44], ![12, 29, 46, 38, 29, 47], ![48, 30, 35, 44, 30, 7], ![49, 31, 7, 45, 31, 35], ![36, 32, 48, 41, 32, 49], ![37, 33, 49, 42, 33, 48], ![10, 34, 47, 43, 34, 46], ![3, 35, 24, 1, 35, 23], ![33, 36, 50, 28, 36, 51], ![32, 37, 51, 27, 37, 50], ![22, 38, 52, 34, 38, 53], ![54, 39, 3, 50, 39, 18], ![55, 40, 18, 51, 40, 3], ![28, 41, 54, 33, 41, 55], ![27, 42, 55, 32, 42, 54], ![20, 43, 53, 29, 43, 52], ![52, 44, 56, 31, 44, 57], ![53, 45, 57, 30, 45, 56], ![50, 46, 1, 54, 46, 17], ![51, 47, 17, 55, 47, 1], ![31, 48, 58, 52, 48, 59], ![30, 49, 59, 53, 49, 58], ![47, 50, 60, 40, 50, 61], ![46, 51, 61, 39, 51, 60], ![45, 52, 5, 49, 52, 0], ![44, 53, 0, 48, 53, 5], ![40, 54, 62, 47, 54, 63], ![39, 55, 63, 46, 55, 62], ![60, 56, 11, 62, 56, 16], ![61, 57, 16, 63, 57, 11], ![62, 58, 9, 60, 58, 15], ![63, 59, 15, 61, 59, 9], ![57, 60, 21, 59, 60, 26], ![56, 61, 26, 58, 61, 21], ![59, 62, 19, 57, 62, 25], ![58, 63, 25, 56, 63, 19]]
private theorem transitions90_2 : ∀ a j, reps90_2 a * edge90_2 j = reps90_2 (next90_2 a j) := by decide +kernel
private theorem check90_2 (_ht : gen90 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen90 2))) : let L := Subgroup.closure (Set.range (edgeGen gen90 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge90_2_eq]
  right; left
  exact noncentric edge90_2 (⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps90_2 0 next90_2
    (by decide +kernel) transitions90_2 (by decide +kernel) (by decide +kernel)

private def edge90_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge90_3_eq : edgeGen gen90 3 = edge90_3 := by decide +kernel
private def reps90_3 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def next90_3 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 6, 7, 8, 0, 9], ![2, 10, 11, 12, 13, 14], ![3, 8, 12, 0, 15, 16], ![4, 0, 17, 15, 6, 18], ![5, 19, 20, 16, 21, 22], ![6, 4, 23, 24, 1, 25], ![7, 26, 27, 19, 16, 28], ![8, 24, 19, 1, 3, 10], ![9, 29, 30, 10, 12, 31], ![10, 23, 32, 9, 2, 33], ![11, 31, 34, 35, 36, 37], ![12, 9, 35, 2, 18, 38], ![13, 2, 28, 18, 23, 27], ![14, 30, 39, 38, 40, 41], ![15, 3, 21, 4, 24, 13], ![16, 7, 42, 5, 17, 43], ![17, 16, 33, 21, 26, 32], ![18, 12, 40, 13, 29, 36], ![19, 25, 36, 7, 5, 40], ![20, 28, 37, 42, 32, 34], ![21, 5, 31, 17, 25, 30], ![22, 27, 41, 43, 33, 39], ![23, 13, 43, 29, 10, 42], ![24, 15, 29, 6, 8, 26], ![25, 21, 38, 26, 19, 35], ![26, 17, 14, 25, 7, 11], ![27, 35, 44, 36, 22, 45], ![28, 38, 46, 40, 20, 47], ![29, 18, 22, 23, 9, 20], ![30, 42, 45, 32, 14, 44], ![31, 43, 47, 33, 11, 46], ![32, 20, 48, 30, 38, 49], ![33, 22, 50, 31, 35, 51], ![34, 51, 24, 52, 45, 53], ![35, 33, 52, 11, 27, 54], ![36, 11, 49, 27, 43, 48], ![37, 50, 55, 54, 44, 0], ![38, 32, 56, 14, 28, 57], ![39, 49, 53, 56, 47, 24], ![40, 14, 51, 28, 42, 50], ![41, 48, 0, 57, 46, 55], ![42, 40, 54, 20, 30, 52], ![43, 36, 57, 22, 31, 56], ![44, 37, 15, 49, 56, 58], ![45, 34, 59, 48, 57, 1], ![46, 41, 58, 51, 52, 15], ![47, 39, 1, 50, 54, 59], ![48, 52, 60, 45, 41, 8], ![49, 54, 4, 44, 39, 61], ![50, 56, 8, 47, 37, 60], ![51, 57, 61, 46, 34, 4], ![52, 46, 6, 34, 48, 62], ![53, 58, 5, 62, 60, 2], ![54, 47, 63, 37, 49, 3], ![55, 59, 26, 63, 61, 29], ![56, 44, 62, 39, 50, 6], ![57, 45, 3, 41, 51, 63], ![58, 63, 9, 61, 53, 7], ![59, 62, 13, 60, 55, 21], ![60, 53, 18, 59, 63, 17], ![61, 55, 10, 58, 62, 19], ![62, 61, 16, 53, 59, 12], ![63, 60, 25, 55, 58, 23]]
private theorem transitions90_3 : ∀ a j, reps90_3 a * edge90_3 j = reps90_3 (next90_3 a j) := by decide +kernel
private theorem check90_3 (_ht : gen90 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen90 3))) : let L := Subgroup.closure (Set.range (edgeGen gen90 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge90_3_eq]
  right; left
  exact noncentric edge90_3 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps90_3 0 next90_3
    (by decide +kernel) transitions90_3 (by decide +kernel) (by decide +kernel)

private def edge90_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩]
private theorem edge90_4_eq : edgeGen gen90 4 = edge90_4 := by decide +kernel
private theorem check90_4 (_ht : gen90 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen90 4))) : let L := Subgroup.closure (Set.range (edgeGen gen90 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge90_4_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge90_4 j ∈ character.ker from by decide +kernel) j

private def edge90_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge90_5_eq : edgeGen gen90 5 = edge90_5 := by decide +kernel
private def words90_5 : ClosureWords 6 6 :=
  ⟨![[], [1, 3, 4], [1, 4, 0], [3], [1, 3, 4, 5], [1, 0, 5]],
   ![[2, 4], [2, 1, 2, 2, 5], [3, 5, 5], [3], [2, 2, 5, 2], [1, 4]]⟩
private theorem check90_5 (_ht : gen90 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen90 5))) : let L := Subgroup.closure (Set.range (edgeGen gen90 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge90_5_eq]
  right; right
  refine ⟨102, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig102_closure]
  exact words90_5.sound _ _ _ (by decide +kernel)

private def edge90_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge90_6_eq : edgeGen gen90 6 = edge90_6 := by decide +kernel
private def reps90_6 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def next90_6 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 0, 2, 3, 0, 4], ![5, 1, 6, 7, 1, 8], ![9, 2, 10, 11, 2, 12], ![7, 3, 13, 5, 3, 14], ![15, 4, 12, 16, 4, 10], ![17, 5, 4, 18, 5, 2], ![19, 6, 20, 21, 6, 22], ![18, 7, 23, 17, 7, 24], ![25, 8, 22, 26, 8, 20], ![4, 9, 27, 23, 9, 28], ![29, 10, 30, 20, 10, 31], ![23, 11, 32, 4, 11, 33], ![34, 12, 31, 22, 12, 30], ![21, 13, 29, 19, 13, 34], ![26, 14, 34, 25, 14, 29], ![2, 15, 28, 24, 15, 27], ![24, 16, 33, 2, 16, 32], ![0, 17, 8, 35, 17, 6], ![35, 18, 14, 0, 18, 13], ![8, 19, 36, 14, 19, 37], ![38, 20, 39, 12, 20, 40], ![14, 21, 41, 8, 21, 42], ![43, 22, 40, 10, 22, 39], ![16, 23, 38, 15, 23, 43], ![11, 24, 43, 9, 24, 38], ![6, 25, 37, 13, 25, 36], ![13, 26, 42, 6, 26, 41], ![41, 27, 44, 36, 27, 45], ![42, 28, 45, 37, 28, 44], ![12, 29, 46, 38, 29, 47], ![48, 30, 35, 44, 30, 7], ![49, 31, 7, 45, 31, 35], ![36, 32, 48, 41, 32, 49], ![37, 33, 49, 42, 33, 48], ![10, 34, 47, 43, 34, 46], ![3, 35, 24, 1, 35, 23], ![33, 36, 50, 28, 36, 51], ![32, 37, 51, 27, 37, 50], ![22, 38, 52, 34, 38, 53], ![54, 39, 3, 50, 39, 18], ![55, 40, 18, 51, 40, 3], ![28, 41, 54, 33, 41, 55], ![27, 42, 55, 32, 42, 54], ![20, 43, 53, 29, 43, 52], ![52, 44, 56, 31, 44, 57], ![53, 45, 57, 30, 45, 56], ![50, 46, 1, 54, 46, 17], ![51, 47, 17, 55, 47, 1], ![31, 48, 58, 52, 48, 59], ![30, 49, 59, 53, 49, 58], ![47, 50, 60, 40, 50, 61], ![46, 51, 61, 39, 51, 60], ![45, 52, 5, 49, 52, 0], ![44, 53, 0, 48, 53, 5], ![40, 54, 62, 47, 54, 63], ![39, 55, 63, 46, 55, 62], ![60, 56, 11, 62, 56, 16], ![61, 57, 16, 63, 57, 11], ![62, 58, 9, 60, 58, 15], ![63, 59, 15, 61, 59, 9], ![57, 60, 21, 59, 60, 26], ![56, 61, 26, 58, 61, 21], ![59, 62, 19, 57, 62, 25], ![58, 63, 25, 56, 63, 19]]
private theorem transitions90_6 : ∀ a j, reps90_6 a * edge90_6 j = reps90_6 (next90_6 a j) := by decide +kernel
private theorem check90_6 (_ht : gen90 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen90 6))) : let L := Subgroup.closure (Set.range (edgeGen gen90 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge90_6_eq]
  right; left
  exact noncentric edge90_6 (⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps90_6 0 next90_6
    (by decide +kernel) transitions90_6 (by decide +kernel) (by decide +kernel)

private def edge90_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge90_7_eq : edgeGen gen90 7 = edge90_7 := by decide +kernel
private def reps90_7 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def next90_7 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 6, 7, 8, 0, 9], ![2, 10, 11, 12, 13, 14], ![3, 8, 12, 0, 15, 16], ![4, 0, 17, 15, 6, 18], ![5, 19, 20, 16, 21, 22], ![6, 4, 23, 24, 1, 25], ![7, 16, 26, 21, 27, 28], ![8, 24, 21, 1, 3, 13], ![9, 12, 29, 13, 30, 31], ![10, 23, 28, 18, 2, 26], ![11, 31, 32, 33, 34, 35], ![12, 18, 33, 2, 9, 36], ![13, 2, 37, 9, 23, 38], ![14, 29, 39, 36, 40, 41], ![15, 3, 19, 4, 24, 10], ![16, 17, 42, 5, 7, 43], ![17, 27, 38, 19, 16, 37], ![18, 30, 40, 10, 12, 34], ![19, 25, 31, 17, 5, 29], ![20, 28, 35, 42, 37, 32], ![21, 5, 34, 7, 25, 40], ![22, 26, 41, 43, 38, 39], ![23, 13, 43, 30, 10, 42], ![24, 15, 30, 6, 8, 27], ![25, 21, 36, 27, 19, 33], ![26, 33, 44, 34, 22, 45], ![27, 7, 14, 25, 17, 11], ![28, 36, 46, 40, 20, 47], ![29, 42, 45, 37, 14, 44], ![30, 9, 22, 23, 18, 20], ![31, 43, 47, 38, 11, 46], ![32, 45, 24, 48, 49, 50], ![33, 38, 48, 11, 26, 51], ![34, 11, 52, 26, 43, 53], ![35, 44, 54, 51, 55, 0], ![36, 37, 56, 14, 28, 57], ![37, 20, 53, 29, 36, 52], ![38, 22, 55, 31, 33, 49], ![39, 47, 50, 56, 52, 24], ![40, 14, 49, 28, 42, 55], ![41, 46, 0, 57, 53, 54], ![42, 40, 51, 20, 29, 48], ![43, 34, 57, 22, 31, 56], ![44, 56, 15, 52, 35, 58], ![45, 57, 59, 53, 32, 1], ![46, 48, 58, 49, 41, 15], ![47, 51, 1, 55, 39, 59], ![48, 53, 6, 32, 46, 60], ![49, 32, 61, 46, 57, 4], ![50, 58, 5, 60, 62, 2], ![51, 52, 63, 35, 47, 3], ![52, 39, 4, 44, 51, 61], ![53, 41, 62, 45, 48, 8], ![54, 59, 27, 63, 61, 30], ![55, 35, 8, 47, 56, 62], ![56, 55, 60, 39, 44, 6], ![57, 49, 3, 41, 45, 63], ![58, 63, 9, 61, 50, 7], ![59, 60, 10, 62, 54, 19], ![60, 61, 16, 50, 59, 12], ![61, 54, 13, 58, 60, 21], ![62, 50, 18, 59, 63, 17], ![63, 62, 25, 54, 58, 23]]
private theorem transitions90_7 : ∀ a j, reps90_7 a * edge90_7 j = reps90_7 (next90_7 a j) := by decide +kernel
private theorem check90_7 (_ht : gen90 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen90 7))) : let L := Subgroup.closure (Set.range (edgeGen gen90 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge90_7_eq]
  right; left
  exact noncentric edge90_7 (⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps90_7 0 next90_7
    (by decide +kernel) transitions90_7 (by decide +kernel) (by decide +kernel)

private theorem node90 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 90)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 90 gen90 gen90_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check90_1
  · exact check90_2
  · exact check90_3
  · exact check90_4
  · exact check90_5
  · exact check90_6
  · exact check90_7

private def gen91 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def generation91 : ClosureWords 3 7 :=
  ⟨![[2, 4, 5, 6], [0], [1]],
   ![[1], [2], [1, 1, 2, 0, 2, 2, 2], [2, 2], [0, 2, 2, 2, 0, 2], [1, 1], [2, 2, 2, 2]]⟩
private theorem gen91_closure : Subgroup.closure (Set.range gen91) = smallParityCensusNode 91 := by
  have h := generation91.sound gen91 orig91 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig91_closure] at h
  exact h

private def edge91_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge91_1_eq : edgeGen gen91 1 = edge91_1 := by decide +kernel
private def words91_1 : ClosureWords 6 6 :=
  ⟨![[], [0], [1], [], [0], [2, 1, 4]],
   ![[1], [2], [1, 1, 2, 2, 2, 5], [2, 2], [1, 1], [2, 2, 2, 2]]⟩
private theorem check91_1 (_ht : gen91 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen91 1))) : let L := Subgroup.closure (Set.range (edgeGen gen91 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge91_1_eq]
  right; right
  refine ⟨111, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig111_closure]
  exact words91_1.sound _ _ _ (by decide +kernel)

private def edge91_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge91_2_eq : edgeGen gen91 2 = edge91_2 := by decide +kernel
private def reps91_2 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def next91_2 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 0, 2, 1, 3, 4], ![0, 1, 5, 0, 6, 7], ![8, 2, 9, 8, 10, 11], ![6, 3, 10, 6, 0, 12], ![13, 4, 11, 13, 12, 9], ![14, 5, 15, 14, 16, 17], ![3, 6, 16, 3, 1, 18], ![19, 7, 17, 19, 18, 15], ![2, 8, 20, 2, 21, 22], ![23, 9, 24, 23, 25, 26], ![21, 10, 25, 21, 2, 27], ![28, 11, 26, 28, 27, 24], ![29, 12, 27, 29, 4, 25], ![4, 13, 22, 4, 29, 20], ![5, 14, 30, 5, 31, 32], ![27, 15, 33, 27, 28, 34], ![31, 16, 28, 31, 5, 23], ![25, 17, 34, 25, 23, 33], ![35, 18, 23, 35, 7, 28], ![7, 19, 32, 7, 35, 30], ![36, 20, 37, 36, 38, 39], ![10, 21, 38, 10, 8, 40], ![41, 22, 39, 41, 40, 37], ![9, 23, 42, 9, 17, 43], ![44, 24, 45, 44, 46, 3], ![17, 25, 46, 17, 9, 47], ![48, 26, 3, 48, 47, 45], ![15, 27, 47, 15, 11, 46], ![11, 28, 43, 11, 15, 42], ![12, 29, 40, 12, 13, 38], ![40, 30, 49, 40, 41, 50], ![16, 31, 41, 16, 14, 36], ![38, 32, 50, 38, 36, 49], ![51, 33, 52, 51, 43, 6], ![53, 34, 6, 53, 42, 52], ![18, 35, 36, 18, 19, 41], ![20, 36, 51, 20, 32, 53], ![47, 37, 54, 47, 48, 55], ![32, 38, 48, 32, 20, 44], ![46, 39, 55, 46, 44, 54], ![30, 40, 44, 30, 22, 48], ![22, 41, 53, 22, 30, 51], ![49, 42, 1, 49, 34, 56], ![50, 43, 56, 50, 33, 1], ![24, 44, 57, 24, 39, 58], ![52, 45, 12, 52, 59, 10], ![39, 46, 59, 39, 24, 0], ![37, 47, 0, 37, 26, 59], ![26, 48, 58, 26, 37, 57], ![42, 49, 60, 42, 53, 61], ![43, 50, 61, 43, 51, 60], ![33, 51, 62, 33, 50, 63], ![45, 52, 18, 45, 56, 16], ![34, 53, 63, 34, 49, 62], ![60, 54, 29, 60, 58, 21], ![61, 55, 21, 61, 57, 29], ![59, 56, 7, 59, 52, 5], ![62, 57, 8, 62, 55, 13], ![63, 58, 13, 63, 54, 8], ![56, 59, 4, 56, 45, 2], ![54, 60, 35, 54, 63, 31], ![55, 61, 31, 55, 62, 35], ![57, 62, 14, 57, 61, 19], ![58, 63, 19, 58, 60, 14]]
private theorem transitions91_2 : ∀ a j, reps91_2 a * edge91_2 j = reps91_2 (next91_2 a j) := by decide +kernel
private theorem check91_2 (_ht : gen91 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen91 2))) : let L := Subgroup.closure (Set.range (edgeGen gen91 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge91_2_eq]
  right; left
  exact noncentric edge91_2 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps91_2 0 next91_2
    (by decide +kernel) transitions91_2 (by decide +kernel) (by decide +kernel)

private def edge91_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge91_3_eq : edgeGen gen91 3 = edge91_3 := by decide +kernel
private def reps91_3 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def next91_3 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 4, 5, 1, 4, 6], ![2, 7, 8, 2, 7, 9], ![3, 10, 11, 3, 10, 12], ![4, 13, 14, 4, 13, 15], ![5, 16, 17, 5, 16, 18], ![6, 19, 20, 6, 19, 21], ![7, 14, 22, 7, 14, 23], ![8, 21, 24, 8, 21, 25], ![9, 20, 26, 9, 20, 27], ![10, 15, 28, 10, 15, 29], ![11, 18, 25, 11, 18, 24], ![12, 17, 27, 12, 17, 26], ![13, 0, 30, 13, 0, 31], ![14, 32, 33, 14, 32, 34], ![15, 35, 36, 15, 35, 37], ![16, 30, 9, 16, 30, 8], ![17, 37, 38, 17, 37, 39], ![18, 36, 40, 18, 36, 41], ![19, 31, 12, 19, 31, 11], ![20, 34, 39, 20, 34, 38], ![21, 33, 41, 21, 33, 40], ![22, 11, 42, 22, 11, 43], ![23, 12, 44, 23, 12, 45], ![24, 45, 46, 24, 45, 47], ![25, 44, 48, 25, 44, 0], ![26, 43, 47, 26, 43, 46], ![27, 42, 0, 27, 42, 48], ![28, 8, 43, 28, 8, 42], ![29, 9, 45, 29, 9, 44], ![30, 49, 23, 30, 49, 22], ![31, 50, 29, 31, 50, 28], ![32, 2, 18, 32, 2, 17], ![33, 28, 51, 33, 28, 52], ![34, 29, 53, 34, 29, 54], ![35, 3, 21, 35, 3, 20], ![36, 22, 52, 36, 22, 51], ![37, 23, 54, 37, 23, 53], ![38, 25, 55, 38, 25, 56], ![39, 24, 57, 39, 24, 1], ![40, 27, 56, 40, 27, 55], ![41, 26, 1, 41, 26, 57], ![42, 54, 58, 42, 54, 59], ![43, 53, 13, 43, 53, 60], ![44, 52, 59, 44, 52, 58], ![45, 51, 60, 45, 51, 13], ![46, 55, 19, 46, 55, 16], ![47, 56, 3, 47, 56, 2], ![48, 57, 16, 48, 57, 19], ![49, 5, 34, 49, 5, 33], ![50, 6, 37, 50, 6, 36], ![51, 39, 61, 51, 39, 62], ![52, 38, 63, 52, 38, 4], ![53, 41, 62, 53, 41, 61], ![54, 40, 4, 54, 40, 63], ![55, 61, 35, 55, 61, 32], ![56, 62, 6, 56, 62, 5], ![57, 63, 32, 57, 63, 35], ![58, 47, 31, 58, 47, 30], ![59, 46, 10, 59, 46, 7], ![60, 48, 7, 60, 48, 10], ![61, 59, 50, 61, 59, 49], ![62, 58, 15, 62, 58, 14], ![63, 60, 49, 63, 60, 50]]
private theorem transitions91_3 : ∀ a j, reps91_3 a * edge91_3 j = reps91_3 (next91_3 a j) := by decide +kernel
private theorem check91_3 (_ht : gen91 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen91 3))) : let L := Subgroup.closure (Set.range (edgeGen gen91 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge91_3_eq]
  right; left
  exact noncentric edge91_3 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps91_3 0 next91_3
    (by decide +kernel) transitions91_3 (by decide +kernel) (by decide +kernel)

private def edge91_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge91_4_eq : edgeGen gen91 4 = edge91_4 := by decide +kernel
private theorem check91_4 (_ht : gen91 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen91 4))) : let L := Subgroup.closure (Set.range (edgeGen gen91 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge91_4_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge91_4 j ∈ character.ker from by decide +kernel) j

private def edge91_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge91_5_eq : edgeGen gen91 5 = edge91_5 := by decide +kernel
private def words91_5 : ClosureWords 6 6 :=
  ⟨![[], [0, 4, 5], [1, 4, 5], [], [0, 4, 5], [1, 2]],
   ![[2, 1, 2, 5, 5], [1, 1, 1, 2, 1], [1, 1, 2, 2, 2, 5], [2, 2], [1, 1], [2, 2, 2, 2]]⟩
private theorem check91_5 (_ht : gen91 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen91 5))) : let L := Subgroup.closure (Set.range (edgeGen gen91 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge91_5_eq]
  right; right
  refine ⟨111, (⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig111_closure]
  exact words91_5.sound _ _ _ (by decide +kernel)

private def edge91_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge91_6_eq : edgeGen gen91 6 = edge91_6 := by decide +kernel
private def reps91_6 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩]
private def next91_6 : Fin 64 → Fin 6 → Fin 64 :=
  ![![1, 0, 2, 1, 3, 4], ![0, 1, 5, 0, 6, 7], ![8, 2, 9, 8, 10, 11], ![6, 3, 10, 6, 0, 12], ![13, 4, 11, 13, 12, 9], ![14, 5, 15, 14, 16, 17], ![3, 6, 16, 3, 1, 18], ![19, 7, 17, 19, 18, 15], ![2, 8, 20, 2, 21, 22], ![17, 9, 23, 17, 24, 25], ![21, 10, 24, 21, 2, 26], ![15, 11, 25, 15, 26, 23], ![27, 12, 26, 27, 4, 24], ![4, 13, 22, 4, 27, 20], ![5, 14, 28, 5, 29, 30], ![11, 15, 31, 11, 32, 33], ![29, 16, 32, 29, 5, 34], ![9, 17, 33, 9, 34, 31], ![35, 18, 34, 35, 7, 32], ![7, 19, 30, 7, 35, 28], ![30, 20, 36, 30, 37, 38], ![10, 21, 37, 10, 8, 39], ![28, 22, 38, 28, 39, 36], ![38, 23, 40, 38, 41, 0], ![34, 24, 41, 34, 9, 42], ![36, 25, 0, 36, 42, 40], ![32, 26, 42, 32, 11, 41], ![12, 27, 39, 12, 13, 37], ![22, 28, 43, 22, 44, 45], ![16, 29, 44, 16, 14, 46], ![20, 30, 45, 20, 46, 43], ![45, 31, 47, 45, 48, 1], ![26, 32, 48, 26, 15, 49], ![43, 33, 1, 43, 49, 47], ![24, 34, 49, 24, 17, 48], ![18, 35, 46, 18, 19, 44], ![25, 36, 50, 25, 51, 52], ![46, 37, 51, 46, 20, 53], ![23, 38, 52, 23, 53, 50], ![44, 39, 53, 44, 22, 51], ![47, 40, 4, 47, 54, 2], ![53, 41, 54, 53, 23, 3], ![51, 42, 3, 51, 25, 54], ![33, 43, 55, 33, 56, 57], ![39, 44, 56, 39, 28, 58], ![31, 45, 57, 31, 58, 55], ![37, 46, 58, 37, 30, 56], ![40, 47, 7, 40, 59, 5], ![58, 48, 59, 58, 31, 6], ![56, 49, 6, 56, 33, 59], ![55, 50, 13, 55, 60, 8], ![42, 51, 60, 42, 36, 61], ![57, 52, 8, 57, 61, 13], ![41, 53, 61, 41, 38, 60], ![59, 54, 12, 59, 40, 10], ![50, 55, 19, 50, 62, 14], ![49, 56, 62, 49, 43, 63], ![52, 57, 14, 52, 63, 19], ![48, 58, 63, 48, 45, 62], ![54, 59, 18, 54, 47, 16], ![62, 60, 27, 62, 50, 21], ![63, 61, 21, 63, 52, 27], ![60, 62, 35, 60, 55, 29], ![61, 63, 29, 61, 57, 35]]
private theorem transitions91_6 : ∀ a j, reps91_6 a * edge91_6 j = reps91_6 (next91_6 a j) := by decide +kernel
private theorem check91_6 (_ht : gen91 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen91 6))) : let L := Subgroup.closure (Set.range (edgeGen gen91 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge91_6_eq]
  right; left
  exact noncentric edge91_6 (⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps91_6 0 next91_6
    (by decide +kernel) transitions91_6 (by decide +kernel) (by decide +kernel)

private def edge91_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge91_7_eq : edgeGen gen91 7 = edge91_7 := by decide +kernel
private def reps91_7 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private def next91_7 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 0, 1, 3], ![1, 4, 5, 1, 4, 6], ![2, 7, 8, 2, 7, 9], ![3, 10, 11, 3, 10, 12], ![4, 13, 14, 4, 13, 15], ![5, 16, 17, 5, 16, 18], ![6, 19, 20, 6, 19, 21], ![7, 14, 22, 7, 14, 23], ![8, 21, 24, 8, 21, 25], ![9, 20, 26, 9, 20, 27], ![10, 15, 28, 10, 15, 29], ![11, 18, 25, 11, 18, 24], ![12, 17, 27, 12, 17, 26], ![13, 0, 30, 13, 0, 31], ![14, 32, 33, 14, 32, 34], ![15, 35, 36, 15, 35, 37], ![16, 30, 9, 16, 30, 8], ![17, 37, 38, 17, 37, 39], ![18, 36, 40, 18, 36, 41], ![19, 31, 12, 19, 31, 11], ![20, 34, 39, 20, 34, 38], ![21, 33, 41, 21, 33, 40], ![22, 11, 42, 22, 11, 43], ![23, 12, 44, 23, 12, 45], ![24, 45, 46, 24, 45, 47], ![25, 44, 48, 25, 44, 0], ![26, 43, 47, 26, 43, 46], ![27, 42, 0, 27, 42, 48], ![28, 8, 43, 28, 8, 42], ![29, 9, 45, 29, 9, 44], ![30, 49, 23, 30, 49, 22], ![31, 50, 29, 31, 50, 28], ![32, 2, 18, 32, 2, 17], ![33, 28, 51, 33, 28, 52], ![34, 29, 53, 34, 29, 54], ![35, 3, 21, 35, 3, 20], ![36, 22, 52, 36, 22, 51], ![37, 23, 54, 37, 23, 53], ![38, 25, 55, 38, 25, 56], ![39, 24, 57, 39, 24, 1], ![40, 27, 56, 40, 27, 55], ![41, 26, 1, 41, 26, 57], ![42, 54, 58, 42, 54, 59], ![43, 53, 13, 43, 53, 60], ![44, 52, 59, 44, 52, 58], ![45, 51, 60, 45, 51, 13], ![46, 55, 19, 46, 55, 16], ![47, 56, 3, 47, 56, 2], ![48, 57, 16, 48, 57, 19], ![49, 5, 34, 49, 5, 33], ![50, 6, 37, 50, 6, 36], ![51, 39, 61, 51, 39, 62], ![52, 38, 63, 52, 38, 4], ![53, 41, 62, 53, 41, 61], ![54, 40, 4, 54, 40, 63], ![55, 61, 35, 55, 61, 32], ![56, 62, 6, 56, 62, 5], ![57, 63, 32, 57, 63, 35], ![58, 47, 31, 58, 47, 30], ![59, 46, 10, 59, 46, 7], ![60, 48, 7, 60, 48, 10], ![61, 59, 50, 61, 59, 49], ![62, 58, 15, 62, 58, 14], ![63, 60, 49, 63, 60, 50]]
private theorem transitions91_7 : ∀ a j, reps91_7 a * edge91_7 j = reps91_7 (next91_7 a j) := by decide +kernel
private theorem check91_7 (_ht : gen91 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen91 7))) : let L := Subgroup.closure (Set.range (edgeGen gen91 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge91_7_eq]
  right; left
  exact noncentric edge91_7 (⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps91_7 0 next91_7
    (by decide +kernel) transitions91_7 (by decide +kernel) (by decide +kernel)

private theorem node91 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 91)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 91 gen91 gen91_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check91_1
  · exact check91_2
  · exact check91_3
  · exact check91_4
  · exact check91_5
  · exact check91_6
  · exact check91_7

private def gen92 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private def generation92 : ClosureWords 3 7 :=
  ⟨![[0], [2], [1]],
   ![[0], [2], [1], [2, 2], [0, 0, 1, 2, 2, 2, 1, 2], [0, 0], [2, 2, 2, 2]]⟩
private theorem gen92_closure : Subgroup.closure (Set.range gen92) = smallParityCensusNode 92 := by
  have h := generation92.sound gen92 orig92 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig92_closure] at h
  exact h

private def edge92_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge92_1_eq : edgeGen gen92 1 = edge92_1 := by decide +kernel
private def reps92_1 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def next92_1 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 0, 6, 7, 8, 9], ![2, 10, 11, 12, 13, 14], ![3, 7, 12, 0, 15, 16], ![4, 8, 17, 15, 0, 18], ![5, 19, 14, 16, 20, 11], ![6, 21, 22, 18, 23, 24], ![7, 3, 18, 1, 25, 17], ![8, 4, 16, 25, 1, 12], ![9, 26, 24, 17, 27, 22], ![10, 2, 28, 20, 16, 29], ![11, 30, 31, 32, 22, 33], ![12, 20, 32, 2, 19, 34], ![13, 16, 35, 19, 2, 36], ![14, 37, 33, 34, 24, 31], ![15, 25, 9, 4, 3, 6], ![16, 13, 34, 5, 10, 32], ![17, 23, 30, 9, 21, 37], ![18, 27, 37, 6, 26, 30], ![19, 5, 29, 13, 12, 28], ![20, 12, 36, 10, 5, 35], ![21, 6, 38, 27, 17, 39], ![22, 34, 40, 37, 11, 41], ![23, 17, 42, 26, 6, 43], ![24, 32, 41, 30, 14, 40], ![25, 15, 5, 8, 7, 2], ![26, 9, 39, 23, 18, 38], ![27, 18, 43, 21, 9, 42], ![28, 42, 44, 36, 38, 45], ![29, 43, 45, 35, 39, 44], ![30, 11, 46, 24, 34, 47], ![31, 48, 8, 49, 44, 3], ![32, 24, 49, 11, 37, 50], ![33, 51, 3, 50, 45, 8], ![34, 22, 50, 14, 30, 49], ![35, 38, 48, 29, 42, 51], ![36, 39, 51, 28, 43, 48], ![37, 14, 47, 22, 32, 46], ![38, 35, 52, 43, 28, 53], ![39, 36, 53, 42, 29, 52], ![40, 54, 4, 47, 52, 7], ![41, 55, 7, 46, 53, 4], ![42, 28, 54, 39, 35, 55], ![43, 29, 55, 38, 36, 54], ![44, 50, 56, 51, 31, 57], ![45, 49, 57, 48, 33, 56], ![46, 52, 1, 41, 54, 15], ![47, 53, 15, 40, 55, 1], ![48, 31, 58, 45, 50, 59], ![49, 45, 25, 31, 51, 0], ![50, 44, 0, 33, 48, 25], ![51, 33, 59, 44, 49, 58], ![52, 46, 60, 55, 40, 61], ![53, 47, 61, 54, 41, 60], ![54, 40, 62, 53, 46, 63], ![55, 41, 63, 52, 47, 62], ![56, 60, 13, 59, 62, 20], ![57, 61, 20, 58, 63, 13], ![58, 62, 10, 57, 60, 19], ![59, 63, 19, 56, 61, 10], ![60, 56, 23, 63, 58, 27], ![61, 57, 27, 62, 59, 23], ![62, 58, 21, 61, 56, 26], ![63, 59, 26, 60, 57, 21]]
private theorem transitions92_1 : ∀ a j, reps92_1 a * edge92_1 j = reps92_1 (next92_1 a j) := by decide +kernel
private theorem check92_1 (_ht : gen92 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen92 1))) : let L := Subgroup.closure (Set.range (edgeGen gen92 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge92_1_eq]
  right; left
  exact noncentric edge92_1 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps92_1 0 next92_1
    (by decide +kernel) transitions92_1 (by decide +kernel) (by decide +kernel)

private def edge92_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge92_2_eq : edgeGen gen92 2 = edge92_2 := by decide +kernel
private def words92_2 : ClosureWords 6 6 :=
  ⟨![[0], [], [1], [0, 5], [], [2, 1]],
   ![[0], [2], [2, 2, 2, 5], [2, 2], [0, 0], [0, 0, 0, 3]]⟩
private theorem check92_2 (_ht : gen92 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen92 2))) : let L := Subgroup.closure (Set.range (edgeGen gen92 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge92_2_eq]
  right; right
  refine ⟨111, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig111_closure]
  exact words92_2.sound _ _ _ (by decide +kernel)

private def edge92_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge92_3_eq : edgeGen gen92 3 = edge92_3 := by decide +kernel
private def reps92_3 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def next92_3 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 6, 7, 8, 0, 9], ![2, 10, 11, 12, 13, 14], ![3, 8, 12, 0, 15, 16], ![4, 0, 9, 15, 6, 7], ![5, 13, 14, 16, 10, 11], ![6, 4, 5, 17, 1, 2], ![7, 18, 19, 20, 21, 22], ![8, 17, 20, 1, 3, 23], ![9, 21, 22, 23, 18, 19], ![10, 5, 24, 25, 2, 26], ![11, 27, 28, 29, 30, 31], ![12, 25, 29, 2, 32, 33], ![13, 2, 26, 32, 5, 24], ![14, 30, 31, 33, 27, 28], ![15, 3, 23, 4, 17, 20], ![16, 32, 33, 5, 25, 29], ![17, 15, 16, 6, 8, 12], ![18, 9, 34, 35, 7, 36], ![19, 29, 37, 30, 33, 38], ![20, 35, 30, 7, 39, 27], ![21, 7, 36, 39, 9, 34], ![22, 33, 38, 27, 29, 37], ![23, 39, 27, 9, 35, 30], ![24, 40, 41, 42, 43, 44], ![25, 16, 42, 10, 12, 45], ![26, 43, 44, 45, 40, 41], ![27, 14, 46, 22, 11, 47], ![28, 48, 17, 49, 50, 3], ![29, 22, 49, 11, 19, 51], ![30, 11, 47, 19, 14, 46], ![31, 50, 3, 51, 48, 17], ![32, 12, 45, 13, 16, 42], ![33, 19, 51, 14, 22, 49], ![34, 42, 52, 43, 45, 53], ![35, 23, 43, 18, 20, 40], ![36, 45, 53, 40, 42, 52], ![37, 54, 15, 47, 55, 8], ![38, 55, 8, 46, 54, 15], ![39, 20, 40, 21, 23, 43], ![40, 26, 54, 36, 24, 55], ![41, 49, 56, 50, 51, 57], ![42, 36, 50, 24, 34, 48], ![43, 24, 55, 34, 26, 54], ![44, 51, 57, 48, 49, 56], ![45, 34, 48, 26, 36, 50], ![46, 52, 1, 38, 53, 4], ![47, 53, 4, 37, 52, 1], ![48, 31, 58, 44, 28, 59], ![49, 44, 6, 28, 41, 0], ![50, 28, 59, 41, 31, 58], ![51, 41, 0, 31, 44, 6], ![52, 47, 60, 55, 46, 61], ![53, 46, 61, 54, 47, 60], ![54, 38, 62, 53, 37, 63], ![55, 37, 63, 52, 38, 62], ![56, 60, 32, 59, 61, 25], ![57, 61, 25, 58, 60, 32], ![58, 62, 10, 57, 63, 13], ![59, 63, 13, 56, 62, 10], ![60, 57, 39, 63, 56, 35], ![61, 56, 35, 62, 57, 39], ![62, 59, 18, 61, 58, 21], ![63, 58, 21, 60, 59, 18]]
private theorem transitions92_3 : ∀ a j, reps92_3 a * edge92_3 j = reps92_3 (next92_3 a j) := by decide +kernel
private theorem check92_3 (_ht : gen92 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen92 3))) : let L := Subgroup.closure (Set.range (edgeGen gen92 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge92_3_eq]
  right; left
  exact noncentric edge92_3 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps92_3 0 next92_3
    (by decide +kernel) transitions92_3 (by decide +kernel) (by decide +kernel)

private def edge92_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge92_4_eq : edgeGen gen92 4 = edge92_4 := by decide +kernel
private theorem check92_4 (_ht : gen92 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen92 4))) : let L := Subgroup.closure (Set.range (edgeGen gen92 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge92_4_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge92_4 j ∈ character.ker from by decide +kernel) j

private def edge92_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge92_5_eq : edgeGen gen92 5 = edge92_5 := by decide +kernel
private def reps92_5 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def next92_5 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 0, 6, 7, 8, 9], ![2, 10, 11, 12, 13, 14], ![3, 7, 12, 0, 15, 16], ![4, 8, 9, 15, 0, 6], ![5, 13, 14, 16, 10, 11], ![6, 17, 18, 19, 20, 21], ![7, 3, 19, 1, 22, 23], ![8, 4, 5, 22, 1, 2], ![9, 20, 21, 23, 17, 18], ![10, 2, 24, 25, 5, 26], ![11, 21, 27, 28, 18, 29], ![12, 25, 28, 2, 30, 31], ![13, 5, 26, 30, 2, 24], ![14, 18, 29, 31, 21, 27], ![15, 22, 23, 4, 3, 19], ![16, 30, 31, 5, 25, 28], ![17, 6, 32, 33, 9, 34], ![18, 14, 35, 36, 11, 37], ![19, 33, 36, 6, 38, 39], ![20, 9, 34, 38, 6, 32], ![21, 11, 37, 39, 14, 35], ![22, 15, 16, 8, 7, 12], ![23, 38, 39, 9, 33, 36], ![24, 34, 40, 41, 32, 42], ![25, 12, 41, 10, 16, 43], ![26, 32, 42, 43, 34, 40], ![27, 42, 8, 44, 40, 0], ![28, 39, 44, 11, 36, 45], ![29, 40, 0, 45, 42, 8], ![30, 16, 43, 13, 12, 41], ![31, 36, 45, 14, 39, 44], ![32, 26, 46, 47, 24, 48], ![33, 19, 47, 17, 23, 49], ![34, 24, 48, 49, 26, 46], ![35, 48, 4, 50, 46, 1], ![36, 31, 50, 18, 28, 51], ![37, 46, 1, 51, 48, 4], ![38, 23, 49, 20, 19, 47], ![39, 28, 51, 21, 31, 50], ![40, 29, 52, 53, 27, 54], ![41, 49, 53, 24, 47, 55], ![42, 27, 54, 55, 29, 52], ![43, 47, 55, 26, 49, 53], ![44, 55, 22, 27, 53, 3], ![45, 53, 3, 29, 55, 22], ![46, 37, 56, 57, 35, 58], ![47, 43, 57, 32, 41, 59], ![48, 35, 58, 59, 37, 56], ![49, 41, 59, 34, 43, 57], ![50, 59, 15, 35, 57, 7], ![51, 57, 7, 37, 59, 15], ![52, 56, 13, 60, 58, 10], ![53, 45, 60, 40, 44, 61], ![54, 58, 10, 61, 56, 13], ![55, 44, 61, 42, 45, 60], ![56, 52, 20, 62, 54, 17], ![57, 51, 62, 46, 50, 63], ![58, 54, 17, 63, 52, 20], ![59, 50, 63, 48, 51, 62], ![60, 62, 30, 52, 63, 25], ![61, 63, 25, 54, 62, 30], ![62, 60, 38, 56, 61, 33], ![63, 61, 33, 58, 60, 38]]
private theorem transitions92_5 : ∀ a j, reps92_5 a * edge92_5 j = reps92_5 (next92_5 a j) := by decide +kernel
private theorem check92_5 (_ht : gen92 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen92 5))) : let L := Subgroup.closure (Set.range (edgeGen gen92 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge92_5_eq]
  right; left
  exact noncentric edge92_5 (⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) reps92_5 0 next92_5
    (by decide +kernel) transitions92_5 (by decide +kernel) (by decide +kernel)

private def edge92_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge92_6_eq : edgeGen gen92 6 = edge92_6 := by decide +kernel
private def words92_6 : ClosureWords 6 6 :=
  ⟨![[0, 2, 4, 5], [], [1, 2, 4], [0, 2, 4], [], [1, 4, 5]],
   ![[2, 0, 2, 5, 2], [0, 3, 5], [2, 2, 2, 5], [5, 5], [0, 0], [0, 0, 0, 3]]⟩
private theorem check92_6 (_ht : gen92 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen92 6))) : let L := Subgroup.closure (Set.range (edgeGen gen92 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge92_6_eq]
  right; right
  refine ⟨111, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig111_closure]
  exact words92_6.sound _ _ _ (by decide +kernel)

private def edge92_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩]
private theorem edge92_7_eq : edgeGen gen92 7 = edge92_7 := by decide +kernel
private def reps92_7 : Fin 64 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private def next92_7 : Fin 64 → Fin 6 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 6, 7, 8, 0, 9], ![2, 10, 11, 12, 13, 14], ![3, 8, 12, 0, 15, 16], ![4, 0, 17, 15, 6, 18], ![5, 19, 14, 16, 20, 11], ![6, 4, 16, 21, 1, 12], ![7, 22, 23, 18, 24, 25], ![8, 21, 18, 1, 3, 17], ![9, 26, 25, 17, 27, 23], ![10, 16, 28, 20, 2, 29], ![11, 25, 30, 31, 32, 33], ![12, 20, 31, 2, 19, 34], ![13, 2, 35, 19, 16, 36], ![14, 23, 33, 34, 37, 30], ![15, 3, 9, 4, 21, 7], ![16, 13, 34, 5, 10, 31], ![17, 24, 37, 9, 22, 32], ![18, 27, 32, 7, 26, 37], ![19, 12, 29, 13, 5, 28], ![20, 5, 36, 10, 12, 35], ![21, 15, 5, 6, 8, 2], ![22, 17, 38, 27, 7, 39], ![23, 31, 40, 32, 14, 41], ![24, 7, 42, 26, 17, 43], ![25, 34, 41, 37, 11, 40], ![26, 18, 39, 24, 9, 38], ![27, 9, 43, 22, 18, 42], ![28, 39, 44, 36, 43, 45], ![29, 38, 45, 35, 42, 44], ![30, 45, 21, 46, 47, 0], ![31, 37, 46, 11, 23, 48], ![32, 11, 49, 23, 34, 50], ![33, 44, 0, 48, 51, 21], ![34, 32, 48, 14, 25, 46], ![35, 43, 51, 29, 39, 47], ![36, 42, 47, 28, 38, 51], ![37, 14, 50, 25, 31, 49], ![38, 36, 52, 43, 29, 53], ![39, 35, 53, 42, 28, 52], ![40, 53, 15, 49, 54, 1], ![41, 52, 1, 50, 55, 15], ![42, 29, 55, 39, 36, 54], ![43, 28, 54, 38, 35, 55], ![44, 46, 56, 47, 33, 57], ![45, 48, 57, 51, 30, 56], ![46, 51, 6, 30, 44, 3], ![47, 30, 58, 44, 48, 59], ![48, 47, 3, 33, 45, 6], ![49, 55, 4, 40, 52, 8], ![50, 54, 8, 41, 53, 4], ![51, 33, 59, 45, 46, 58], ![52, 49, 60, 54, 41, 61], ![53, 50, 61, 55, 40, 60], ![54, 40, 62, 52, 50, 63], ![55, 41, 63, 53, 49, 62], ![56, 60, 19, 58, 63, 10], ![57, 61, 10, 59, 62, 19], ![58, 62, 13, 56, 61, 20], ![59, 63, 20, 57, 60, 13], ![60, 59, 26, 62, 56, 22], ![61, 58, 22, 63, 57, 26], ![62, 57, 24, 60, 58, 27], ![63, 56, 27, 61, 59, 24]]
private theorem transitions92_7 : ∀ a j, reps92_7 a * edge92_7 j = reps92_7 (next92_7 a j) := by decide +kernel
private theorem check92_7 (_ht : gen92 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen92 7))) : let L := Subgroup.closure (Set.range (edgeGen gen92 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge92_7_eq]
  right; left
  exact noncentric edge92_7 (⟨⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) reps92_7 0 next92_7
    (by decide +kernel) transitions92_7 (by decide +kernel) (by decide +kernel)

private theorem node92 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 92)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 92 gen92 gen92_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check92_1
  · exact check92_2
  · exact check92_3
  · exact check92_4
  · exact check92_5
  · exact check92_6
  · exact check92_7

private def gen93 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private def generation93 : ClosureWords 3 7 :=
  ⟨![[0, 0, 2, 4], [1], [0]],
   ![[2], [1], [1, 1, 1, 0, 1, 2, 2], [1, 1], [0, 1, 1, 1, 0, 1], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1]]⟩
private theorem gen93_closure : Subgroup.closure (Set.range gen93) = smallParityCensusNode 93 := by
  have h := generation93.sound gen93 orig93 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig93_closure] at h
  exact h

private def edge93_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge93_1_eq : edgeGen gen93 1 = edge93_1 := by decide +kernel
private def words93_1 : ClosureWords 6 6 :=
  ⟨![[], [1], [0], [], [2, 1, 4], [0]],
   ![[2], [1], [1, 1, 2, 2, 4, 1], [1, 1], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1]]⟩
private theorem check93_1 (_ht : gen93 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen93 1))) : let L := Subgroup.closure (Set.range (edgeGen gen93 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge93_1_eq]
  right; right
  refine ⟨113, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig113_closure]
  exact words93_1.sound _ _ _ (by decide +kernel)

private def edge93_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge93_2_eq : edgeGen gen93 2 = edge93_2 := by decide +kernel
private theorem check93_2 (_ht : gen93 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen93 2))) : let L := Subgroup.closure (Set.range (edgeGen gen93 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge93_2_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge93_2 j ∈ character.ker from by decide +kernel) j

private def edge93_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge93_3_eq : edgeGen gen93 3 = edge93_3 := by decide +kernel
private def words93_3 : ClosureWords 6 6 :=
  ⟨![[], [0, 0, 1], [0], [], [1, 2], [0]],
   ![[2], [1, 2, 2], [1, 1, 2, 2, 4, 1], [1, 1], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1]]⟩
private theorem check93_3 (_ht : gen93 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen93 3))) : let L := Subgroup.closure (Set.range (edgeGen gen93 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge93_3_eq]
  right; right
  refine ⟨113, (⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig113_closure]
  exact words93_3.sound _ _ _ (by decide +kernel)

private def edge93_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge93_4_eq : edgeGen gen93 4 = edge93_4 := by decide +kernel
private theorem check93_4 (_ht : gen93 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen93 4))) : let L := Subgroup.closure (Set.range (edgeGen gen93 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge93_4_eq] at _ht ⊢
  right; left
  exact noncentric_short edge93_4 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen93 (pivot 4)) [5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge93_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge93_5_eq : edgeGen gen93 5 = edge93_5 := by decide +kernel
private theorem check93_5 (_ht : gen93 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen93 5))) : let L := Subgroup.closure (Set.range (edgeGen gen93 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge93_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge93_5 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen93 (pivot 5)) [2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge93_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge93_6_eq : edgeGen gen93 6 = edge93_6 := by decide +kernel
private theorem check93_6 (_ht : gen93 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen93 6))) : let L := Subgroup.closure (Set.range (edgeGen gen93 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge93_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge93_6 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen93 (pivot 6)) [5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge93_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge93_7_eq : edgeGen gen93 7 = edge93_7 := by decide +kernel
private theorem check93_7 (_ht : gen93 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen93 7))) : let L := Subgroup.closure (Set.range (edgeGen gen93 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge93_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge93_7 (⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel) (gen93 (pivot 7)) [2] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node93 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 93)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 93 gen93 gen93_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check93_1
  · exact check93_2
  · exact check93_3
  · exact check93_4
  · exact check93_5
  · exact check93_6
  · exact check93_7

private def gen94 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private def generation94 : ClosureWords 3 7 :=
  ⟨![[2], [1], [0]],
   ![[2], [1], [0], [1, 1], [0, 1, 0, 1, 1, 1, 2, 2], [0, 2, 0, 2], [1, 1, 1, 1]]⟩
private theorem gen94_closure : Subgroup.closure (Set.range gen94) = smallParityCensusNode 94 := by
  have h := generation94.sound gen94 orig94 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig94_closure] at h
  exact h

private def edge94_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge94_1_eq : edgeGen gen94 1 = edge94_1 := by decide +kernel
private def words94_1 : ClosureWords 6 6 :=
  ⟨![[], [1], [0], [], [2, 1], [0, 5]],
   ![[2], [1], [1, 1, 1, 4], [1, 1], [2, 5], [1, 1, 1, 1]]⟩
private theorem check94_1 (_ht : gen94 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen94 1))) : let L := Subgroup.closure (Set.range (edgeGen gen94 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge94_1_eq]
  right; right
  refine ⟨113, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig113_closure]
  exact words94_1.sound _ _ _ (by decide +kernel)

private def edge94_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge94_2_eq : edgeGen gen94 2 = edge94_2 := by decide +kernel
private theorem check94_2 (_ht : gen94 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen94 2))) : let L := Subgroup.closure (Set.range (edgeGen gen94 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge94_2_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge94_2 j ∈ character.ker from by decide +kernel) j

private def edge94_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge94_3_eq : edgeGen gen94 3 = edge94_3 := by decide +kernel
private def words94_3 : ClosureWords 6 6 :=
  ⟨![[], [1, 2, 4], [0, 2, 5], [], [0, 0, 1], [0, 2]],
   ![[1, 1, 1, 2, 4], [2, 2, 4], [1, 1, 1, 4], [4, 4], [2, 5], [1, 1, 1, 1]]⟩
private theorem check94_3 (_ht : gen94 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen94 3))) : let L := Subgroup.closure (Set.range (edgeGen gen94 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge94_3_eq]
  right; right
  refine ⟨113, (⟨⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig113_closure]
  exact words94_3.sound _ _ _ (by decide +kernel)

private def edge94_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, Multiplicative.ofAdd 0⟩]
private theorem edge94_4_eq : edgeGen gen94 4 = edge94_4 := by decide +kernel
private theorem check94_4 (_ht : gen94 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen94 4))) : let L := Subgroup.closure (Set.range (edgeGen gen94 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge94_4_eq] at _ht ⊢
  right; left
  exact noncentric_short edge94_4 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen94 (pivot 4)) [0, 1, 1, 0, 5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge94_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge94_5_eq : edgeGen gen94 5 = edge94_5 := by decide +kernel
private theorem check94_5 (_ht : gen94 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen94 5))) : let L := Subgroup.closure (Set.range (edgeGen gen94 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge94_5_eq] at _ht ⊢
  right; left
  exact noncentric_short edge94_5 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen94 (pivot 5)) [1, 1, 5] _ht
    (by decide +kernel) (by decide +kernel)

private def edge94_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩]
private theorem edge94_6_eq : edgeGen gen94 6 = edge94_6 := by decide +kernel
private theorem check94_6 (_ht : gen94 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen94 6))) : let L := Subgroup.closure (Set.range (edgeGen gen94 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge94_6_eq] at _ht ⊢
  right; left
  exact noncentric_short edge94_6 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen94 (pivot 6)) [2] _ht
    (by decide +kernel) (by decide +kernel)

private def edge94_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, Multiplicative.ofAdd 1⟩, ⟨⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩]
private theorem edge94_7_eq : edgeGen gen94 7 = edge94_7 := by decide +kernel
private theorem check94_7 (_ht : gen94 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen94 7))) : let L := Subgroup.closure (Set.range (edgeGen gen94 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge94_7_eq] at _ht ⊢
  right; left
  exact noncentric_short edge94_7 (⟨⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩ : SylowModel) (gen94 (pivot 7)) [1, 2, 1] _ht
    (by decide +kernel) (by decide +kernel)

private theorem node94 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 94)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 94 gen94 gen94_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check94_1
  · exact check94_2
  · exact check94_3
  · exact check94_4
  · exact check94_5
  · exact check94_6
  · exact check94_7

private def gen95 : Fin 2 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩]
private def generation95 : ClosureWords 2 7 :=
  ⟨![[0], [1]],
   ![[0], [1], [0, 0], [0, 1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]]⟩
private theorem gen95_closure : Subgroup.closure (Set.range gen95) = smallParityCensusNode 95 := by
  have h := generation95.sound gen95 orig95 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig95_closure] at h
  exact h

private def edge95_1 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 1, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩]
private theorem edge95_1_eq : edgeGen gen95 1 = edge95_1 := by decide +kernel
private def words95_1 : ClosureWords 4 6 :=
  ⟨![[], [1, 2, 0, 1], [0, 2, 0, 3], [4, 0]],
   ![[1, 2, 1, 2, 1, 2], [2, 1, 2, 1, 2, 2], [2, 1, 1], [2, 2], [2, 2, 2, 3, 1], [2, 2, 2, 2]]⟩
private theorem check95_1 (_ht : gen95 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen95 1))) : let L := Subgroup.closure (Set.range (edgeGen gen95 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge95_1_eq]
  right; right
  refine ⟨100, (⟨⟨0, 1, 1, 0, 1, 1, 0, 1, 0, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig100_closure]
  exact words95_1.sound _ _ _ (by decide +kernel)

private def edge95_2 : Fin 4 → SylowModel :=
  ![⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 1⟩, Multiplicative.ofAdd 2⟩]
private theorem edge95_2_eq : edgeGen gen95 2 = edge95_2 := by decide +kernel
private def words95_2 : ClosureWords 4 6 :=
  ⟨![[0], [], [0, 2, 3], [2, 1, 3]],
   ![[0], [0, 0], [0, 0, 3], [3, 3], [2, 0, 3, 3, 3], [3, 3, 3, 3]]⟩
private theorem check95_2 (_ht : gen95 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen95 2))) : let L := Subgroup.closure (Set.range (edgeGen gen95 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge95_2_eq]
  right; right
  refine ⟨99, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig99_closure]
  exact words95_2.sound _ _ _ (by decide +kernel)

private def edge95_3 : Fin 4 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 1⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge95_3_eq : edgeGen gen95 3 = edge95_3 := by decide +kernel
private theorem check95_3 (_ht : gen95 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen95 3))) : let L := Subgroup.closure (Set.range (edgeGen gen95 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge95_3_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge95_3 j ∈ character.ker from by decide +kernel) j

private theorem node95 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 95)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 95 gen95 gen95_closure signatures2 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check95_1
  · exact check95_2
  · exact check95_3

private def gen96 : Fin 3 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩]
private def generation96 : ClosureWords 3 7 :=
  ⟨![[3, 5], [0], [1]],
   ![[1], [2], [1, 1], [1, 1, 2, 0, 2], [1, 1, 1, 1], [0, 1, 1, 2, 0, 2], [0, 1, 1, 0, 2, 2]]⟩
private theorem gen96_closure : Subgroup.closure (Set.range gen96) = smallParityCensusNode 96 := by
  have h := generation96.sound gen96 orig96 (MonoidHom.id _) (by decide +kernel)
  rw [Subgroup.map_id, orig96_closure] at h
  exact h

private def edge96_1 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩]
private theorem edge96_1_eq : edgeGen gen96 1 = edge96_1 := by decide +kernel
private def words96_1 : ClosureWords 6 6 :=
  ⟨![[], [0], [1], [], [3, 0], [3, 1]],
   ![[1], [2], [1, 1], [1, 1, 5, 2], [1, 1, 1, 1], [1, 1, 5, 5]]⟩
private theorem check96_1 (_ht : gen96 (pivot 1) ∉ Subgroup.closure (Set.range (edgeGen gen96 1))) : let L := Subgroup.closure (Set.range (edgeGen gen96 1));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge96_1_eq]
  right; right
  refine ⟨114, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig114_closure]
  exact words96_1.sound _ _ _ (by decide +kernel)

private def edge96_2 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨1, 0, 0, 1, 1, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩]
private theorem edge96_2_eq : edgeGen gen96 2 = edge96_2 := by decide +kernel
private def words96_2 : ClosureWords 6 6 :=
  ⟨![[2], [], [1, 2, 0, 1], [2, 4, 5], [0, 3, 4, 0], [0, 2]],
   ![[3, 5], [0, 2, 2, 3], [0], [0, 4, 0, 4], [2, 2, 5, 2], [4, 4, 4, 4]]⟩
private theorem check96_2 (_ht : gen96 (pivot 2) ∉ Subgroup.closure (Set.range (edgeGen gen96 2))) : let L := Subgroup.closure (Set.range (edgeGen gen96 2));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge96_2_eq]
  right; right
  refine ⟨100, (⟨⟨0, 1, 1, 0, 0, 1, 0, 1, 1, 1⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig100_closure]
  exact words96_2.sound _ _ _ (by decide +kernel)

private def edge96_3 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 3⟩]
private theorem edge96_3_eq : edgeGen gen96 3 = edge96_3 := by decide +kernel
private def words96_3 : ClosureWords 6 6 :=
  ⟨![[], [0, 5], [3, 1], [], [0, 3], [1]],
   ![[1, 1, 1, 5, 2], [5], [1, 1], [1, 1, 5, 5], [1, 1, 1, 1], [1, 1, 5, 2]]⟩
private theorem check96_3 (_ht : gen96 (pivot 3) ∉ Subgroup.closure (Set.range (edgeGen gen96 3))) : let L := Subgroup.closure (Set.range (edgeGen gen96 3));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge96_3_eq]
  right; right
  refine ⟨115, (⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig115_closure]
  exact words96_3.sound _ _ _ (by decide +kernel)

private def edge96_4 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, Multiplicative.ofAdd 2⟩]
private theorem edge96_4_eq : edgeGen gen96 4 = edge96_4 := by decide +kernel
private def words96_4 : ClosureWords 6 6 :=
  ⟨![[2], [0], [], [2, 4, 5], [0, 3, 4], [1, 3, 5]],
   ![[1], [1, 1], [0], [0, 5, 0, 5], [1, 1, 4, 1], [5, 5, 5, 5]]⟩
private theorem check96_4 (_ht : gen96 (pivot 4) ∉ Subgroup.closure (Set.range (edgeGen gen96 4))) : let L := Subgroup.closure (Set.range (edgeGen gen96 4));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge96_4_eq]
  right; right
  refine ⟨99, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig99_closure]
  exact words96_4.sound _ _ _ (by decide +kernel)

private def edge96_5 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩]
private theorem edge96_5_eq : edgeGen gen96 5 = edge96_5 := by decide +kernel
private def words96_5 : ClosureWords 6 6 :=
  ⟨![[], [0], [3, 1], [], [3, 0], [1]],
   ![[1], [5], [1, 1], [1, 1, 5, 5], [1, 1, 1, 1], [1, 1, 5, 2]]⟩
private theorem check96_5 (_ht : gen96 (pivot 5) ∉ Subgroup.closure (Set.range (edgeGen gen96 5))) : let L := Subgroup.closure (Set.range (edgeGen gen96 5));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge96_5_eq]
  right; right
  refine ⟨115, (⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig115_closure]
  exact words96_5.sound _ _ _ (by decide +kernel)

private def edge96_6 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨0, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, Multiplicative.ofAdd 2⟩, ⟨⟨0, 1, 0, 0, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 2⟩]
private theorem edge96_6_eq : edgeGen gen96 6 = edge96_6 := by decide +kernel
private theorem check96_6 (_ht : gen96 (pivot 6) ∉ Subgroup.closure (Set.range (edgeGen gen96 6))) : let L := Subgroup.closure (Set.range (edgeGen gen96 6));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge96_6_eq]
  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (show ∀ j, edge96_6 j ∈ character.ker from by decide +kernel) j

private def edge96_7 : Fin 6 → SylowModel :=
  ![⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, Multiplicative.ofAdd 3⟩, ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩, ⟨⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, Multiplicative.ofAdd 3⟩, ⟨⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, Multiplicative.ofAdd 3⟩]
private theorem edge96_7_eq : edgeGen gen96 7 = edge96_7 := by decide +kernel
private def words96_7 : ClosureWords 6 6 :=
  ⟨![[], [0, 5], [1], [], [0, 3], [3, 1]],
   ![[1, 1, 1, 5, 5], [2], [1, 1], [1, 1, 5, 2], [1, 1, 1, 1], [1, 1, 5, 5]]⟩
private theorem check96_7 (_ht : gen96 (pivot 7) ∉ Subgroup.closure (Set.range (edgeGen gen96 7))) : let L := Subgroup.closure (Set.range (edgeGen gen96 7));
    L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [edge96_7_eq]
  right; right
  refine ⟨114, (⟨⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, Multiplicative.ofAdd 0⟩ : SylowModel), ?_⟩
  rw [← orig114_closure]
  exact words96_7.sound _ _ _ (by decide +kernel)

private theorem node96 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 96)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  apply step 96 gen96 gen96_closure signatures3 ?_ H hmax hcent hpar
  intro m
  fin_cases m
  · exact check96_1
  · exact check96_2
  · exact check96_3
  · exact check96_4
  · exact check96_5
  · exact check96_6
  · exact check96_7

end SmallParityOrder128

/-- Maximal-step coverage for the prescribed census nodes 61 through 96. -/
public theorem smallParityCensusStep_order128 (i : Fin 131) (hlo : 61 ≤ i.val) (hhi : i.val < 97)
    (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode i)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) :
    Represented smallParityCensusNode H := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 36, i = ⟨j.val+61, Nat.lt_trans (Nat.add_lt_add_right j.isLt 61) (by decide)⟩ :=
    ⟨⟨i.val-61, by omega⟩, by apply Fin.ext; simp only; omega⟩
  fin_cases j
  · exact SmallParityOrder128.node61 H hmax hcent hpar
  · exact SmallParityOrder128.node62 H hmax hcent hpar
  · exact SmallParityOrder128.node63 H hmax hcent hpar
  · exact SmallParityOrder128.node64 H hmax hcent hpar
  · exact SmallParityOrder128.node65 H hmax hcent hpar
  · exact SmallParityOrder128.node66 H hmax hcent hpar
  · exact SmallParityOrder128.node67 H hmax hcent hpar
  · exact SmallParityOrder128.node68 H hmax hcent hpar
  · exact SmallParityOrder128.node69 H hmax hcent hpar
  · exact SmallParityOrder128.node70 H hmax hcent hpar
  · exact SmallParityOrder128.node71 H hmax hcent hpar
  · exact SmallParityOrder128.node72 H hmax hcent hpar
  · exact SmallParityOrder128.node73 H hmax hcent hpar
  · exact SmallParityOrder128.node74 H hmax hcent hpar
  · exact SmallParityOrder128.node75 H hmax hcent hpar
  · exact SmallParityOrder128.node76 H hmax hcent hpar
  · exact SmallParityOrder128.node77 H hmax hcent hpar
  · exact SmallParityOrder128.node78 H hmax hcent hpar
  · exact SmallParityOrder128.node79 H hmax hcent hpar
  · exact SmallParityOrder128.node80 H hmax hcent hpar
  · exact SmallParityOrder128.node81 H hmax hcent hpar
  · exact SmallParityOrder128.node82 H hmax hcent hpar
  · exact SmallParityOrder128.node83 H hmax hcent hpar
  · exact SmallParityOrder128.node84 H hmax hcent hpar
  · exact SmallParityOrder128.node85 H hmax hcent hpar
  · exact SmallParityOrder128.node86 H hmax hcent hpar
  · exact SmallParityOrder128.node87 H hmax hcent hpar
  · exact SmallParityOrder128.node88 H hmax hcent hpar
  · exact SmallParityOrder128.node89 H hmax hcent hpar
  · exact SmallParityOrder128.node90 H hmax hcent hpar
  · exact SmallParityOrder128.node91 H hmax hcent hpar
  · exact SmallParityOrder128.node92 H hmax hcent hpar
  · exact SmallParityOrder128.node93 H hmax hcent hpar
  · exact SmallParityOrder128.node94 H hmax hcent hpar
  · exact SmallParityOrder128.node95 H hmax hcent hpar
  · exact SmallParityOrder128.node96 H hmax hcent hpar
end ReeTwo.SylowModel
