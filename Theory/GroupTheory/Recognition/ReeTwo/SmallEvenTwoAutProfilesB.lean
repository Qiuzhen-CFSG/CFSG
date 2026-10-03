module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates
public import Theory.GroupTheory.PGroup.InvariantFiberAutomorphisms

/-!
# Finite profile stabilizers for seventeen small even Ree two subgroups

The intrinsic tests count elements with specified order and centralizer order
in binary Frattini cosets. Kernel reduction verifies that each displayed
rank-three or rank-four profile has a two-group stabilizer. The rank-five
certificate and the predicates below specify the remaining
realization obligations on the exact root-generated subgroups.

Source: the Shinoda (1975), (2.3), pp. 81–82 root convention, as verified in
`SmallEvenCandidates`. The tables are proposed finite data; their stabilizers
are proved here, and their realization as group-theoretic counts is kept explicit.
-/

namespace ReeTwo.SylowModel.SmallEvenAutB

/-- Binary quotient coordinates, least significant coordinate first. -/
public abbrev Binary (n : ℕ) := Multiplicative (Fin n → ZMod 2)

private def basisVector (n : ℕ) (i : Fin n) : Binary n :=
  Multiplicative.ofAdd (fun j => if j = i then 1 else 0)

set_option synthInstance.maxSize 4096
set_option maxRecDepth 32768

/-- Original candidate indices with rank 3. -/
@[expose] public def rankThreeIndex : Fin 6 → Fin 59 :=
  ![24, 25, 38, 43, 46, 51]

/-- Three intrinsic order-centralizer tests (repetitions pad shorter lists). -/
@[expose] public def rankThreeTests (i : Fin 6) : Fin 3 → ℕ × ℕ × ℕ :=
  (![![(2, 32, 0), (2, 32, 0), (2, 32, 0)],
    ![(4, 16, 0), (4, 16, 0), (4, 16, 0)],
    ![(4, 32, 0), (4, 32, 0), (4, 32, 0)],
    ![(2, 16, 0), (2, 16, 0), (2, 16, 0)],
    ![(2, 16, 0), (2, 16, 0), (2, 16, 0)],
    ![(2, 8, 0), (2, 8, 0), (2, 8, 0)]]) i

/-- Proposed counts in binary coset order. -/
@[expose] public def rankThreeProfile (i : Fin 6) (x : Binary 3) : ℕ × ℕ × ℕ :=
  ((![([(0, 0, 0), (4, 4, 4), (8, 8, 8), (8, 8, 8), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (16, 16, 16), (16, 16, 16), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (8, 8, 8), (16, 16, 16), (16, 16, 16), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (4, 4, 4), (4, 4, 4), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (2, 2, 2), (2, 2, 2), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (4, 4, 4), (4, 4, 4), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ))]) i).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val) (0, 0, 0)

private def word3 (a b c : Binary 3) (x : Binary 3) : Binary 3 :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val

set_option maxHeartbeats 16000000 in
private theorem certificate3 : ∀ i : Fin 6,
    ∀ a : Binary 3, rankThreeProfile i a = rankThreeProfile i (basisVector 3 0) →
    ∀ b : Binary 3, rankThreeProfile i b = rankThreeProfile i (basisVector 3 1) →
    rankThreeProfile i (a * b) = rankThreeProfile i (basisVector 3 0 * basisVector 3 1) →
    ∀ c : Binary 3, rankThreeProfile i c = rankThreeProfile i (basisVector 3 2) →
    rankThreeProfile i (a * c) = rankThreeProfile i (basisVector 3 0 * basisVector 3 2) →
    rankThreeProfile i (b * c) = rankThreeProfile i (basisVector 3 1 * basisVector 3 2) →
    (∀ x, word3 a b c x = 1 ↔ x = 1) →
    (∀ x, rankThreeProfile i (word3 a b c x) = rankThreeProfile i x) →
    ∀ x, (word3 a b c (word3 a b c (word3 a b c (word3 a b c x)))) = x := by decide +kernel

private theorem word3_hom (f : Binary 3 →* Binary 3) (x : Binary 3) :
    word3 (f (basisVector 3 0)) (f (basisVector 3 1)) (f (basisVector 3 2)) x = f x := by
  have hn : word3 (basisVector 3 0) (basisVector 3 1) (basisVector 3 2) x = x :=
    (by decide +kernel : ∀ x, word3 (basisVector 3 0) (basisVector 3 1) (basisVector 3 2) x = x) x
  simpa only [word3, map_mul, map_pow] using congrArg f hn

/-- Every symmetry of this profile has order dividing 4. -/
public theorem rankThreeProfile_aut_pow (i : Fin 6) (f : MulAut (Binary 3))
    (h : ∀ x, rankThreeProfile i (f x) = rankThreeProfile i x) : f ^ 4 = 1 := by
  have hc := certificate3 i
    (f (basisVector 3 0)) (h _)
    (f (basisVector 3 1)) (h _)
    (by simpa only [map_mul] using h (basisVector 3 0 * basisVector 3 1))
    (f (basisVector 3 2)) (h _)
    (by simpa only [map_mul] using h (basisVector 3 0 * basisVector 3 2))
    (by simpa only [map_mul] using h (basisVector 3 1 * basisVector 3 2))
  have hw := word3_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact f.map_eq_one_iff)
    (by intro x; rw [hw]; exact h x)
  apply MulEquiv.ext
  intro x
  change f (f (f (f x))) = x
  simpa only [hw] using hh x

/-- A surjective Frattini map realizing the displayed intrinsic counts. -/
@[expose] public def RankThreeModel (i : Fin 6) : Prop :=
  ∃ π : smallEvenCandidate (rankThreeIndex i) →* Binary 3,
    Function.Surjective π ∧ π.ker = frattini (smallEvenCandidate (rankThreeIndex i)) ∧
    ∀ v, (π.predicateFiberCard (MulAut.orderCentralizerTest (rankThreeTests i 0)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (rankThreeTests i 1)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (rankThreeTests i 2)) v) =
      rankThreeProfile i v

/-- Realizing this profile suffices to exclude odd-order automorphisms. -/
public theorem rankThree_isPGroup_mulAut_of_model (i : Fin 6) (h : RankThreeModel i) :
    IsPGroup 2 (MulAut (smallEvenCandidate (rankThreeIndex i))) := by
  obtain ⟨π, hπ, hker, hcount⟩ := h
  apply MonoidHom.isPGroup_mulAut_of_frattini_predicateFiber
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) π hπ hker
    (fun j : Fin 3 => MulAut.orderCentralizerTest (rankThreeTests i j))
    (fun f j x => MulAut.orderCentralizerTest_apply f _ x)
  intro a ha
  refine ⟨2, rankThreeProfile_aut_pow i a ?_⟩
  intro v
  rw [← hcount (a v), ← hcount v, ha 0 v, ha 1 v, ha 2 v]

/-- Original candidate indices with rank 4. -/
@[expose] public def rankFourIndex : Fin 7 → Fin 59 :=
  ![18, 19, 20, 21, 22, 26, 37]

/-- Three intrinsic order-centralizer tests (repetitions pad shorter lists). -/
@[expose] public def rankFourTests (i : Fin 7) : Fin 3 → ℕ × ℕ × ℕ :=
  (![![(4, 64, 0), (4, 64, 0), (4, 64, 0)],
    ![(4, 64, 0), (4, 64, 0), (4, 64, 0)],
    ![(4, 64, 0), (4, 64, 0), (4, 64, 0)],
    ![(2, 32, 0), (2, 128, 0), (2, 128, 0)],
    ![(4, 32, 0), (4, 32, 0), (4, 32, 0)],
    ![(2, 16, 0), (2, 32, 0), (2, 32, 0)],
    ![(4, 32, 0), (4, 32, 0), (4, 32, 0)]]) i

/-- Proposed counts in binary coset order. -/
@[expose] public def rankFourProfile (i : Fin 7) (x : Binary 4) : ℕ × ℕ × ℕ :=
  ((![([(0, 0, 0), (8, 8, 8), (8, 8, 8), (0, 0, 0), (16, 16, 16), (16, 16, 16), (16, 16, 16), (16, 16, 16), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (8, 8, 8), (8, 8, 8), (0, 0, 0), (0, 0, 0), (16, 16, 16), (16, 16, 16), (0, 0, 0), (16, 16, 16), (16, 16, 16), (16, 16, 16), (16, 16, 16), (16, 16, 16), (16, 16, 16), (16, 16, 16), (16, 16, 16)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (8, 8, 8), (8, 8, 8), (0, 0, 0), (16, 16, 16), (16, 16, 16), (16, 16, 16), (16, 16, 16), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 12, 12), (0, 16, 16), (8, 0, 0), (8, 0, 0), (8, 0, 0), (8, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (8, 8, 8), (0, 0, 0), (8, 8, 8), (0, 0, 0), (16, 16, 16), (0, 0, 0), (16, 16, 16), (8, 8, 8), (16, 16, 16), (8, 8, 8), (16, 16, 16), (16, 16, 16), (16, 16, 16), (16, 16, 16), (16, 16, 16)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (0, 4, 4), (8, 0, 0), (0, 0, 0), (8, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 0, 0), (4, 4, 4), (8, 8, 8), (0, 0, 0), (4, 4, 4), (0, 0, 0), (0, 0, 0), (8, 8, 8), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ))]) i).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val + 8 * (x.toAdd 3).val) (0, 0, 0)

private def word4 (a b c d : Binary 4) (x : Binary 4) : Binary 4 :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val * d ^ (x.toAdd 3).val

set_option maxHeartbeats 16000000 in
private theorem certificate4 : ∀ i : Fin 7,
    ∀ a : Binary 4, rankFourProfile i a = rankFourProfile i (basisVector 4 0) →
    ∀ b : Binary 4, rankFourProfile i b = rankFourProfile i (basisVector 4 1) →
    rankFourProfile i (a * b) = rankFourProfile i (basisVector 4 0 * basisVector 4 1) →
    ∀ c : Binary 4, rankFourProfile i c = rankFourProfile i (basisVector 4 2) →
    rankFourProfile i (a * c) = rankFourProfile i (basisVector 4 0 * basisVector 4 2) →
    rankFourProfile i (b * c) = rankFourProfile i (basisVector 4 1 * basisVector 4 2) →
    ∀ d : Binary 4, rankFourProfile i d = rankFourProfile i (basisVector 4 3) →
    rankFourProfile i (a * d) = rankFourProfile i (basisVector 4 0 * basisVector 4 3) →
    rankFourProfile i (b * d) = rankFourProfile i (basisVector 4 1 * basisVector 4 3) →
    rankFourProfile i (c * d) = rankFourProfile i (basisVector 4 2 * basisVector 4 3) →
    (∀ x, word4 a b c d x = 1 ↔ x = 1) →
    (∀ x, rankFourProfile i (word4 a b c d x) = rankFourProfile i x) →
    ∀ j : Fin 4, ∀ y : Binary 4,
      word4 a b c d (word4 a b c d (basisVector 4 j)) = y →
      word4 a b c d (word4 a b c d y) = basisVector 4 j := by decide +kernel

private theorem word4_hom (f : Binary 4 →* Binary 4) (x : Binary 4) :
    word4 (f (basisVector 4 0)) (f (basisVector 4 1)) (f (basisVector 4 2)) (f (basisVector 4 3)) x = f x := by
  have hn : word4 (basisVector 4 0) (basisVector 4 1) (basisVector 4 2) (basisVector 4 3) x = x :=
    (by decide +kernel : ∀ x, word4 (basisVector 4 0) (basisVector 4 1) (basisVector 4 2) (basisVector 4 3) x = x) x
  simpa only [word4, map_mul, map_pow] using congrArg f hn

/-- Every symmetry of this profile has order dividing 4. -/
public theorem rankFourProfile_aut_pow (i : Fin 7) (f : MulAut (Binary 4))
    (h : ∀ x, rankFourProfile i (f x) = rankFourProfile i x) : f ^ 4 = 1 := by
  have hc := certificate4 i
    (f (basisVector 4 0)) (h _)
    (f (basisVector 4 1)) (h _)
    (by simpa only [map_mul] using h (basisVector 4 0 * basisVector 4 1))
    (f (basisVector 4 2)) (h _)
    (by simpa only [map_mul] using h (basisVector 4 0 * basisVector 4 2))
    (by simpa only [map_mul] using h (basisVector 4 1 * basisVector 4 2))
    (f (basisVector 4 3)) (h _)
    (by simpa only [map_mul] using h (basisVector 4 0 * basisVector 4 3))
    (by simpa only [map_mul] using h (basisVector 4 1 * basisVector 4 3))
    (by simpa only [map_mul] using h (basisVector 4 2 * basisVector 4 3))
  have hw := word4_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact f.map_eq_one_iff)
    (by intro x; rw [hw]; exact h x)
  have hfix (j : Fin 4) : (f ^ 4) (basisVector 4 j) = basisVector 4 j := by
    have hj := hh j (f (f (basisVector 4 j))) (by simp only [hw])
    change f (f (f (f (basisVector 4 j)))) = basisVector 4 j
    simpa only [hw] using hj
  apply MulEquiv.ext
  intro x
  have hp := word4_hom (f ^ 4).toMonoidHom x
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hfix] at hp
  rw [← hp]
  exact (by decide +kernel : ∀ x,
    word4 (basisVector 4 0) (basisVector 4 1) (basisVector 4 2)
      (basisVector 4 3) x = x) x

/-- A surjective Frattini map realizing the displayed intrinsic counts. -/
@[expose] public def RankFourModel (i : Fin 7) : Prop :=
  ∃ π : smallEvenCandidate (rankFourIndex i) →* Binary 4,
    Function.Surjective π ∧ π.ker = frattini (smallEvenCandidate (rankFourIndex i)) ∧
    ∀ v, (π.predicateFiberCard (MulAut.orderCentralizerTest (rankFourTests i 0)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (rankFourTests i 1)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (rankFourTests i 2)) v) =
      rankFourProfile i v

/-- Realizing this profile suffices to exclude odd-order automorphisms. -/
public theorem rankFour_isPGroup_mulAut_of_model (i : Fin 7) (h : RankFourModel i) :
    IsPGroup 2 (MulAut (smallEvenCandidate (rankFourIndex i))) := by
  obtain ⟨π, hπ, hker, hcount⟩ := h
  apply MonoidHom.isPGroup_mulAut_of_frattini_predicateFiber
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) π hπ hker
    (fun j : Fin 3 => MulAut.orderCentralizerTest (rankFourTests i j))
    (fun f j x => MulAut.orderCentralizerTest_apply f _ x)
  intro a ha
  refine ⟨2, rankFourProfile_aut_pow i a ?_⟩
  intro v
  rw [← hcount (a v), ← hcount v, ha 0 v, ha 1 v, ha 2 v]

/-- Original candidate indices with rank 5. -/
@[expose] public def rankFiveIndex : Fin 4 → Fin 59 :=
  ![23, 29, 35, 40]

/-- Three intrinsic order-centralizer tests (repetitions pad shorter lists). -/
@[expose] public def rankFiveTests (i : Fin 4) : Fin 3 → ℕ × ℕ × ℕ :=
  (![![(2, 64, 0), (2, 128, 0), (4, 32, 0)],
    ![(2, 64, 0), (2, 128, 0), (2, 128, 0)],
    ![(2, 64, 0), (2, 128, 0), (2, 128, 0)],
    ![(2, 64, 0), (2, 128, 0), (2, 128, 0)]]) i

/-- Proposed counts in binary coset order. -/
@[expose] public def rankFiveProfile (i : Fin 4) (x : Binary 5) : ℕ × ℕ × ℕ :=
  ((![([(0, 0, 0), (8, 0, 0), (8, 0, 0), (0, 8, 0), (0, 8, 0), (0, 0, 0), (0, 0, 0), (0, 8, 0), (0, 0, 8), (0, 0, 8), (0, 0, 8), (0, 0, 8), (0, 0, 8), (0, 0, 8), (0, 0, 8), (0, 0, 8), (0, 0, 8), (0, 0, 0), (0, 0, 0), (0, 0, 8), (0, 0, 8), (0, 0, 0), (0, 0, 0), (0, 0, 8), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 3, 3), (0, 4, 4), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (0, 0, 0), (0, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 3, 3), (0, 4, 4), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (0, 0, 0), (0, 0, 0), (4, 0, 0), (4, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)),
    ([(0, 3, 3), (0, 4, 4), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (4, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (4, 0, 0), (4, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ))]) i).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val + 8 * (x.toAdd 3).val + 16 * (x.toAdd 4).val) (0, 0, 0)

/-- The remaining finite rank-five stabilizer certificate. This definition
states a proof obligation; it does not assert that the tables satisfy it. -/
@[expose] public def RankFiveProfileCertificate : Prop :=
  ∀ (i : Fin 4) (f : MulAut (Binary 5)),
    (∀ x, rankFiveProfile i (f x) = rankFiveProfile i x) → f ^ 8 = 1

/-- A surjective Frattini map realizing the displayed intrinsic counts. -/
@[expose] public def RankFiveModel (i : Fin 4) : Prop :=
  ∃ π : smallEvenCandidate (rankFiveIndex i) →* Binary 5,
    Function.Surjective π ∧ π.ker = frattini (smallEvenCandidate (rankFiveIndex i)) ∧
    ∀ v, (π.predicateFiberCard (MulAut.orderCentralizerTest (rankFiveTests i 0)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (rankFiveTests i 1)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (rankFiveTests i 2)) v) =
      rankFiveProfile i v

/-- Realizing this profile suffices to exclude odd-order automorphisms. -/
public theorem rankFive_isPGroup_mulAut_of_model_of_profile_certificate
    (i : Fin 4) (h : RankFiveModel i) (hcert : RankFiveProfileCertificate) :
    IsPGroup 2 (MulAut (smallEvenCandidate (rankFiveIndex i))) := by
  obtain ⟨π, hπ, hker, hcount⟩ := h
  apply MonoidHom.isPGroup_mulAut_of_frattini_predicateFiber
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) π hπ hker
    (fun j : Fin 3 => MulAut.orderCentralizerTest (rankFiveTests i j))
    (fun f j x => MulAut.orderCentralizerTest_apply f _ x)
  intro a ha
  refine ⟨3, hcert i a ?_⟩
  intro v
  rw [← hcount (a v), ← hcount v, ha 0 v, ha 1 v, ha 2 v]

end ReeTwo.SylowModel.SmallEvenAutB
