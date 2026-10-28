module
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged.Words
/-! Exhaustive binary calculation for oriented cubics on the enlarged split
block. Six basis images reduce to 32 choices of a moving vector and eight
choices for each central basis image. The certificate checks the cubic and
factor-movement conditions and supplies a simultaneous change of coordinates.
All identities are kernel-checked. Source: Aschbacher–Smith 14.4.4, p.1007. -/
@[expose] public section
namespace BinarySixSplitPair.Census
abbrev X := Fin 64
 def bx (a b : X) : X := ⟨(a.val ^^^ b.val)%64,Nat.mod_lt _ (by decide)⟩
 def linear (a : Fin 6 → X) (x : X) : X :=
    bx (bx (bx (bx (bx
      (if x.val%2=1 then a 0 else 0)
      (if (x.val/2)%2=1 then a 1 else 0))
      (if (x.val/4)%2=1 then a 2 else 0))
      (if (x.val/8)%2=1 then a 3 else 0))
      (if (x.val/16)%2=1 then a 4 else 0))
      (if (x.val/32)%2=1 then a 5 else 0)
def r : X → X := ![0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12,16,17,18,19,21,20,23,22,26,27,24,25,31,30,29,28,32,33,34,35,37,36,39,38,42,43,40,41,47,46,45,44,48,49,50,51,53,52,55,54,58,59,56,57,63,62,61,60]
def c : X → X := ![0,3,2,1,12,15,14,13,8,11,10,9,4,7,6,5,16,19,18,17,28,31,30,29,24,27,26,25,20,23,22,21,32,35,34,33,44,47,46,45,40,43,42,41,36,39,38,37,48,51,50,49,60,63,62,61,56,59,58,57,52,55,54,53]
def fixed : Fin 8 → X := ![0,2,16,18,32,34,48,50]
def seeds : Fin 32 → X := ![4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31,36,37,38,39,44,45,46,47,52,53,54,55,60,61,62,63]
def change (i : Fin 24) : X → X := linear (![![1,2,4,8,16,32],![1,2,5,10,16,32],![3,2,12,8,16,32],![3,2,15,10,16,32],![1,2,4,8,16,48],![1,2,5,10,16,48],![3,2,12,8,16,48],![3,2,15,10,16,48],![1,2,4,8,32,16],![1,2,5,10,32,16],![3,2,12,8,32,16],![3,2,15,10,32,16],![1,2,4,8,32,48],![1,2,5,10,32,48],![3,2,12,8,32,48],![3,2,15,10,32,48],![1,2,4,8,48,16],![1,2,5,10,48,16],![3,2,12,8,48,16],![3,2,15,10,48,16],![1,2,4,8,48,32],![1,2,5,10,48,32],![3,2,12,8,48,32],![3,2,15,10,48,32]] i)
def candidate (t : X) (u v : Fin 8) : X → X :=
    linear ![bx (c t) t,2,t,bx (r (c t)) t,fixed u,fixed v]
def rep (i : Fin 3) : Equiv.Perm X :=
    ![EnlargedSwappingTable.q1,EnlargedSwappingTable.q2,EnlargedSwappingTable.q3] i
def certificate (t : X) : Prop := ∀ u v : Fin 8,
    let q := candidate t u v
    (∀ i : Fin 6, q (q (q (![1,2,4,8,16,32] i))) = ![1,2,4,8,16,32] i) →
    (t.val ≥ 16) →
    (fixed u % 16 ≠ 0 ∨ fixed v % 16 ≠ 0) →
    ∃ j : Fin 3, ∃ k : Fin 24, ∀ x : X, change k (q x) = rep j (change k x)
theorem census : ∀ t : Fin 32, certificate (seeds t) := by unfold certificate; decide +kernel
end BinarySixSplitPair.Census
