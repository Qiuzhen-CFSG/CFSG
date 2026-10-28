module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongProjection
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongWords
public import Theory.Frattini.BinarySquares

/-!
# Frattini structure of the long rank-three parity candidates

The original subgroups in global rows 0, 1, and 5 are exactly the proposed
coordinate carriers. Their coordinate maps are homomorphisms with Frattini
kernel. Explicit products of squares of the original basis words give six,
five, and four kernel directions. Ordered words in these directions reconstruct
all elements with zero quotient coordinates. The converse follows because the
quotient has exponent two; the ambient group of order 4096 supplies the
finite-two-group hypothesis for the Frattini square-generation theorem.

`structure_certificate` packages the exact inputs needed by the independent
finite-count transfer theorem, without assuming carrier or kernel assertions.

Source: Shinoda (1975), (2.3), pp. 81–82, through `SmallParityThreeGenerators`
and the verified coordinates in `SmallParityThreeLongCoordinates`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallParityLong
set_option maxRecDepth 32768

private def kernelCode (c : Fin 3) (j : Fin 6) : ℕ :=
  (![![2090,48,64,128,256,512], ![2154,48,128,256,512,0],
    ![2282,176,256,512,0,0]] : Fin 3 → Fin 6 → ℕ) c j
private def kernelGenerator (c : Fin 3) (j : Fin 6) : SylowModel :=
  let n := kernelCode c j
  ⟨⟨(n : ℕ), (n/2 : ℕ), (n/4 : ℕ), (n/8 : ℕ), (n/16 : ℕ),
     (n/32 : ℕ), (n/64 : ℕ), (n/128 : ℕ), (n/256 : ℕ), (n/512 : ℕ)⟩,
     Multiplicative.ofAdd (n/1024 : ℕ)⟩
private def squareWords (c : Fin 3) (j : Fin 6) : List (List (Fin 3)) :=
  (![![[[2,1,2]], [[0,0,2]], [[0],[0,1,2,1]], [[0],[0,1,1]], [[0,0,0,1]], [[0,0,0,0]]],
     ![[[2,1,2]], [[0],[1,0,0]], [[0],[0,0,0,2]], [[0,0,1,0]], [[0,0,0,0]], []],
     ![[[0,0,0]], [[1,1]], [[0,0,0,1]], [[0,0,0,0]], [], []]] :
     Fin 3 → Fin 6 → List (List (Fin 3))) c j
private def word {I : Type*} (g : I → SylowModel) (w : List I) : SylowModel :=
  (w.map g).prod
set_option maxHeartbeats 8000000 in
private theorem squareWords_valid : ∀ (c : Fin 3) (j : Fin 6),
    word (fun w => (word (fun j => (smallParityThreeBasisLift (index c) j).val) w) ^ 2)
      (squareWords c j) = kernelGenerator c j := by decide +kernel

private def kernelExponents (c : Fin 3) (p : Parameters c) : Fin 6 → ZMod 2 :=
  let t : ZMod 2 := (p.1.toAdd.val / 2 : ℕ)
  let b4 := bit c p 1
  let b6 := bit c p 6
  let b7 := bit c p 2
  let b8 := bit c p 3
  let b9 := bit c p 4
  (![![t, b4, b6, t*b4+b7, t*b4+t*b6+b8, b9],
    ![t, b4, t*b4+b7, t*b4+b8, b9, 0],
    ![t, b4, t*b4+b8, b9, 0, 0]] : Fin 3 → Fin 6 → ZMod 2) c
private def kernelWord (c : Fin 3) (p : Parameters c) : SylowModel :=
  (((List.finRange 6).map fun j =>
    collectedPow (kernelGenerator c j) (kernelExponents c p j).val)).foldl collectedMul 1
set_option maxHeartbeats 8000000 in
private theorem kernelWord_valid : ∀ (c : Fin 3) (p : Parameters c),
    coordinates c (element c p) = 1 → kernelWord c p = element c p := by decide +kernel

private theorem word_mem {I : Type*} (D : Subgroup SylowModel)
    (g : I → SylowModel) (hg : ∀ j, g j ∈ D) (w : List I) : word g w ∈ D := by
  induction w with
  | nil => exact D.one_mem
  | cons j w ih => exact D.mul_mem (hg j) ih
private theorem kernelGenerator_mem (c : Fin 3) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ Candidate c, x ^ 2 ∈ D) (j : Fin 6) : kernelGenerator c j ∈ D := by
  rw [← squareWords_valid c j]
  apply word_mem
  intro w
  apply hsq
  exact word_mem _ _ (fun j => (smallParityThreeBasisLift (index c) j).property) w

private theorem kernel_mem_of_squares (c : Fin 3) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ Candidate c, x ^ 2 ∈ D) (p : Parameters c)
    (hz : coordinates c (element c p) = 1) : element c p ∈ D := by
  rw [← kernelWord_valid c p hz]
  unfold kernelWord
  have hlist : ∀ a ∈ (List.finRange 6).map (fun j =>
      collectedPow (kernelGenerator c j) (kernelExponents c p j).val), a ∈ D := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    rw [collectedPow_eq]
    exact D.pow_mem (kernelGenerator_mem c D hsq j) _
  generalize (List.finRange 6).map _ = l at hlist ⊢
  have hfold : ∀ a ∈ D, l.foldl collectedMul a ∈ D := by
    induction l with
    | nil => intro a ha; exact ha
    | cons x l ih =>
      intro a ha
      apply ih (fun y hy => hlist y (List.mem_cons_of_mem _ hy))
      rw [collectedMul_eq]
      exact D.mul_mem ha (hlist x (List.mem_cons_self))
  exact hfold 1 D.one_mem

theorem projection_ker (c : Fin 3) : (projection c).ker = frattini (Candidate c) := by
  have hU : IsPGroup 2 (Candidate c) :=
    (IsPGroup.of_card (n := 12) card).to_subgroup _
  have hphi := hU.frattini_eq_closure_squares
  apply le_antisymm
  · intro x hx
    let D := (frattini (Candidate c)).map (Candidate c).subtype
    have hsq (y : SylowModel) (hy : y ∈ Candidate c) : y ^ 2 ∈ D := by
      refine ⟨(⟨y,hy⟩ : Candidate c) ^ 2, ?_, rfl⟩
      rw [hphi]
      exact Subgroup.subset_closure ⟨⟨y,hy⟩,rfl⟩
    have he := candidate_carrier c x.val x.property
    have hz : coordinates c (element c (parameters c x.val)) = 1 := by
      rw [he]
      exact hx
    have hv : x.val ∈ D := by
      rw [← he]
      exact kernel_mem_of_squares c D hsq _ hz
    obtain ⟨y,hy,heq⟩ := hv
    exact (show y = x from Subtype.ext heq) ▸ hy
  · rw [hphi]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    change projection c (x ^ 2) = 1
    rw [map_pow]
    exact (by decide +kernel : ∀ v : SmallParityThreeQuotient, v ^ 2 = 1) _

/-- Carrier identification and the prescribed Frattini projection, ready for
`SmallParityLong.model_of_certificates`. -/
theorem structure_certificate (c : Fin 3) :
    (∀ x : Candidate c, carrier c x.val) ∧
    (∀ p : Parameters c, element c p ∈ Candidate c) ∧
    ∃ π : Candidate c →* SmallParityThreeQuotient,
      (∀ x, π x = coordinates c x.val) ∧ π.ker = frattini (Candidate c) :=
  ⟨fun x => candidate_carrier c x.val x.property, element_mem c,
    projection c, fun _ => rfl, projection_ker c⟩

end ReeTwo.SylowModel.SmallParityLong
