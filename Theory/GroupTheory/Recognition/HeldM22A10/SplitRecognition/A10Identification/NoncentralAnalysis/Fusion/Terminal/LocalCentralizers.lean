module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds

/-!
# The two local centralizers in Held's terminal contradiction

The centralizers of lambda and tau in the actual local group are, respectively,
S adjoined with mu-prime times xi and S adjoined with tau-prime. Both have
order 32, lie in the displayed Sylow subgroup, and have centers of orders
8 and 4. Thirty-two binary words give explicit bijections with these
centralizers; checking commutation in these coordinates computes their centers.
All finite computations are checked by kernel reduction.

Source: D. Held, "A Characterization of some multiply transitive permutation
 groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.229.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

local instance codeDecidableEq : DecidableEq Code := inferInstance
local instance modelDecidableEq : DecidableEq H := inferInstance
private abbrev CCode := BaseCode × Fin 2
local instance ccodeDecidableEq : DecidableEq CCode := inferInstance

/-- Lambda and tau, in the order used in the final comparison. -/
@[expose] public def terminalRepresentative : Fin 2 → H := ![lam, tau]
/-- The additional generators of their centralizers over S. -/
@[expose] public def terminalExtra : Fin 2 → H := ![mup * xi, taup]
private def terminalWord (i : Fin 2) (a : CCode) : H :=
  elementaryWord 1 a.1 * terminalExtra i ^ a.2.val
/-- The actual model centralizers, rather than abstract groups of order 32. -/
@[expose] public def terminalLocalCentralizer (i : Fin 2) : Subgroup H :=
  centralizer ({terminalRepresentative i} : Set H)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem terminalWord_injective : ∀ i, Function.Injective (terminalWord i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem terminalWord_commutes : ∀ i a,
    terminalWord i a * terminalRepresentative i = terminalRepresentative i * terminalWord i a := by
  decide +kernel

public theorem terminalLocalCentralizer_card (i : Fin 2) : Nat.card (terminalLocalCentralizer i) = 32 := by
  fin_cases i
  · exact involution_centralizer_cards.2.2.2.1
  · exact involution_centralizer_cards.2.2.1

private def terminalWordLift (i : Fin 2) (a : CCode) : terminalLocalCentralizer i :=
  ⟨terminalWord i a, mem_centralizer_singleton_iff.mpr (terminalWord_commutes i a)⟩

private theorem terminalWordLift_bijective (i : Fin 2) : Function.Bijective (terminalWordLift i) := by
  have hi : Function.Injective (terminalWordLift i) := by
    intro a b h
    exact terminalWord_injective i (congrArg Subtype.val h)
  apply hi.bijective_of_nat_card_le
  rw [terminalLocalCentralizer_card]
  simp [CCode, BaseCode]

public theorem terminalLocalCentralizer_eq (i : Fin 2) :
    terminalLocalCentralizer i = modelS ⊔ zpowers (terminalExtra i) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := (terminalWordLift_bijective i).surjective ⟨x, hx⟩
    have he : terminalWord i a = x := congrArg Subtype.val ha
    rw [← he]
    apply mul_mem
    · exact (le_sup_left : modelS ≤ modelS ⊔ zpowers (terminalExtra i))
        ((mem_elementary 1 _).mpr ⟨a.1, rfl⟩)
    · exact (le_sup_right : zpowers (terminalExtra i) ≤ modelS ⊔ zpowers (terminalExtra i))
        (pow_mem (mem_zpowers _) _)
  · apply sup_le
    · intro x hx
      obtain ⟨a, rfl⟩ := (mem_elementary 1 x).mp hx
      have h := (terminalWordLift i (a, 0)).property
      simpa [terminalWordLift, terminalWord] using h
    · apply zpowers_le.mpr
      have h := (terminalWordLift i (0, 1)).property
      simpa [terminalWordLift, terminalWord, elementaryWord] using h

public theorem terminalLocalCentralizer_le_modelD (i : Fin 2) :
    terminalLocalCentralizer i ≤ modelD := by
  rw [terminalLocalCentralizer_eq]
  apply sup_le (elementary_le_modelD 1)
  apply zpowers_le.mpr
  have hm : ∀ j : Fin 7, (![pi, mu, mup, tau, taup, lam, xi] : Fin 7 → H) j ∈ modelD :=
    fun j => subset_closure ⟨j, rfl⟩
  fin_cases i
  · exact modelD.mul_mem (hm 2) (hm 6)
  · exact hm 4

private theorem terminal_center_count (i : Fin 2) :
    Nat.card (center (terminalLocalCentralizer i)) =
      Nat.card {a : CCode // ∀ b : CCode, terminalWord i b * terminalWord i a =
        terminalWord i a * terminalWord i b} := by
  apply Nat.card_congr
  apply Equiv.symm
  apply Equiv.subtypeEquiv (Equiv.ofBijective (terminalWordLift i) (terminalWordLift_bijective i))
  intro a
  constructor
  · intro ha
    apply mem_center_iff.mpr
    intro b
    obtain ⟨b, rfl⟩ := (terminalWordLift_bijective i).surjective b
    exact Subtype.ext (ha b)
  · intro ha b
    exact congrArg Subtype.val (mem_center_iff.mp ha (terminalWordLift i b))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
public theorem terminalLocalCentralizer_center_card (i : Fin 2) :
    Nat.card (center (terminalLocalCentralizer i)) = (![8, 4] : Fin 2 → ℕ) i := by
  rw [terminal_center_count, Nat.card_eq_fintype_card]
  revert i
  decide +kernel

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
