module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024ResidualRepresentatives
public import Theory.GroupTheory.PGroup.FrattiniProfile

/-!
# Refined Frattini-profile certificates for four Ree two subgroups

The four tables retain just two counts in each binary rank-three quotient
fiber: elements of order four whose centralizers in the subgroup have order
32 or 64. The associated color stabilizers have exponent dividing four,
as proved by checking all triples of generator images in the eight-element
quotient. Normal forms and the soundness of `ProfileWordCertificate` turn
this finite check into a theorem about every profile-preserving automorphism.

`RefinedProfileModel` separates the remaining concrete mathematics from this
small certificate: a surjective map with Frattini kernel and the two stated
counts. A model then implies the full automorphism group is a two-group.
The centralizers in this contract are taken inside the candidate subgroup.

The basis lifts, in case order 1, 5, 7, 13, are respectively
(root 3, root 1, rootOne² * root 0),
(root 1 * root 3, root 0 * root 3, rootOne² * root 3),
(root 1 * root 3, root 0 * root 3, rootOne²), and
(root 3, root 2, rootOne * root 0 * root 1).
Coordinates use low-to-high binary order. The candidate groups and root
conventions come from Shinoda (1975), (2.3), pp. 81–82, as realized by
`Sylow` and `Order1024ResidualRepresentatives`. The tables alone do not
assert any counts in those groups; that assertion is the model contract.
-/

namespace ReeTwo.SylowModel

/-- The original residual-family indices, in refined-certificate order. -/
@[expose] public def refinedIndex (c : Fin 4) : Fin 15 := ![1, 5, 7, 13] c

/-- The common binary rank-three quotient. -/
public abbrev RefinedQuotient := Multiplicative (Fin 3 → ZMod 2)
/-- The ordered standard basis, in low-to-high binary order. -/
@[expose] public def refinedBasis (i : Fin 3) : RefinedQuotient :=
  Multiplicative.ofAdd (fun j => if j = i then 1 else 0)
/-- The product of the basis vectors at the nonzero coordinates. -/
@[expose] public def refinedWord (x : RefinedQuotient) : List (Fin 3) :=
  (List.finRange 3).filter (fun j => x.toAdd j = 1)
/-- Proposed counts for the labels `(4,32)` and `(4,64)` in each quotient fiber. -/
@[expose] public def refinedProfile (c : Fin 4) (x : RefinedQuotient) : ℕ × ℕ :=
  ((![[(0,80), (32,32), (0,128), (0,128), (0,0), (0,0), (0,0), (0,0)],
       [(0,48), (128,0), (64,64), (64,64), (96,32), (0,0), (0,0), (0,0)],
       [(0,48), (128,0), (64,64), (64,64), (96,0), (0,0), (0,0), (0,0)],
       [(0,0), (0,32), (32,32), (64,0), (0,0), (0,0), (0,0), (0,0)]] :
      Fin 4 → List (ℕ × ℕ)) c).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val) (0,0)
/-- Every quotient element is reconstructed by its binary word. -/
public theorem refinedWord_valid : ∀ x, Theory.GroupTheory.evalWord refinedBasis (refinedWord x) = x := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- All four selected-count stabilizers have exponent dividing four. -/
public theorem refinedProfile_certificate : ∀ c : Fin 4,
    Theory.GroupTheory.ProfileWordCertificate refinedBasis refinedWord (refinedProfile c) 4 := by
  decide +kernel

/-- The two intrinsic fiber counts used by the finite certificate. -/
@[expose] public noncomputable def refinedFiberCounts {G : Type*} [Group G]
    (π : G →* RefinedQuotient) (v : RefinedQuotient) : ℕ × ℕ :=
  (Subgroup.fiberProfile π
      (fun x => (orderOf x, Nat.card (Subgroup.centralizer ({x} : Set G)))) v (4,32),
   Subgroup.fiberProfile π
      (fun x => (orderOf x, Nat.card (Subgroup.centralizer ({x} : Set G)))) v (4,64))

/-- Concrete quotient and counting obligations, without any automorphism premise. -/
@[expose] public def RefinedProfileModel (c : Fin 4) : Prop :=
  ∃ π : residualCandidate (refinedIndex c) →* RefinedQuotient,
    Function.Surjective π ∧ π.ker = frattini (residualCandidate (refinedIndex c)) ∧
    ∀ v, refinedFiberCounts π v = refinedProfile c v

/-- A realized refined profile forces the original candidate's automorphisms
 to form a two-group. -/
public theorem RefinedProfileModel.isPGroup_mulAut {c : Fin 4}
    (h : RefinedProfileModel c) :
    IsPGroup 2 (MulAut (residualCandidate (refinedIndex c))) := by
  obtain ⟨π, hπ, hker, hcounts⟩ := h
  let G := residualCandidate (refinedIndex c)
  let e : (G ⧸ frattini G) ≃* RefinedQuotient :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he (x : G) : e (QuotientGroup.mk' (frattini G) x) = π x := rfl
  apply Subgroup.isPGroup_mulAut_of_frattini_word_profile
    ((IsPGroup.of_card (n := 12) card).to_subgroup G) e
    (fun x => (orderOf x, Nat.card (Subgroup.centralizer ({x} : Set G))))
    Subgroup.order_centralizer_label_mulAut
    refinedBasis refinedWord (refinedProfile c) refinedWord_valid
    (k := 2)
  · intro x y hxy
    rw [← hcounts x, ← hcounts y]
    apply Prod.ext
    · exact congrFun hxy (4,32)
    · exact congrFun hxy (4,64)
  · exact refinedProfile_certificate c

end ReeTwo.SylowModel
