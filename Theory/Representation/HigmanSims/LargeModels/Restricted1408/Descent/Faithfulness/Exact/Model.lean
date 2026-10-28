module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Context
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
import Mathlib.Tactic.FinCases

/-!
# Separating the centralizer cosets in the literal HS carrier

For every nonidentity representative in the certified 5,775-element list,
the permutation fails to commute with the first generator at point 0 or 2.
The map of representative words is proved from the actual marked generators.
Only this root separation is required for kernel centrality; no faithfulness
of the permutation quotient is used here.

Source: the centralizer route in ATLAS HSG1-P1.M. The two witness points
were found from the retained enumeration and are checked by Lean's kernel.
-/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact
open Subgroup.CosetWordCertificate
open Cover

private theorem map_tracePair {G B : Type*} [Group G] [Group B]
    (f : G →* B) (a b : G) (n : Nat) :
    f (tracePair a b n) = tracePair (f a) (f b) n := by
  unfold tracePair
  generalize (⟨n % 6, Nat.mod_lt n (by decide)⟩ : Fin 6) = i
  fin_cases i <;> simp [extendedPair]

private theorem map_repr {G B : Type*} [Group G] [Group B]
    (f : G →* B) (g : Nat → G) (n : Nat) :
    f (definitions.repr g n) = definitions.repr (fun i => f (g i)) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Definitions.repr, map_mul, Definitions.repr, ih _ (definitions.parent_lt n)]
      simp only [eval_letter]
      split <;> simp

@[expose] public def modelRep (n : Nat) : Equiv.Perm (Fin 100) :=
  definitions.repr (tracePair OrderCertificate.p0 OrderCertificate.p1) n

public theorem modelRep_eq (n : Nat) :
    inclusion (toCarrier (definitions.repr certGenerator n)) = modelRep n := by
  change (inclusion.comp toCarrier) (definitions.repr certGenerator n) = _
  rw [map_repr]
  have hg : (fun i => (inclusion.comp toCarrier) (certGenerator i)) =
      tracePair OrderCertificate.p0 OrderCertificate.p1 := by
    funext i
    rw [certGenerator, map_tracePair]
    simp only [MonoidHom.comp_apply, toCarrier_generator_false, toCarrier_generator_true]
    rw [OrderCertificate.a_eq_generator, OrderCertificate.b_eq_generator]
    rfl
  rw [hg]
  rfl

@[expose] public def modelCheck (n : Nat) : Bool :=
  n == 0 ||
    (OrderCertificate.p0 (modelRep n 0) != modelRep n (OrderCertificate.p0 0)) ||
    (OrderCertificate.p0 (modelRep n 2) != modelRep n (OrderCertificate.p0 2))

@[expose] public def modelChunk (start count : Nat) : Bool :=
  (List.range count).all fun k => modelCheck (start+k)

public theorem modelChunk_sound {start count : Nat} (h : modelChunk start count = true)
    (n : Nat) (hlo : start ≤ n) (hhi : n < start+count) : modelCheck n = true := by
  have hm : n-start ∈ List.range count := by simp only [List.mem_range]; omega
  have hs := List.all_eq_true.mp h (n-start) hm
  have he : start + (n-start) = n := by omega
  rwa [he] at hs

public theorem root_of_modelCheck (n : Nat) (hc : modelCheck n = true)
    (h : Commute (toCarrier (definitions.repr certGenerator n)) generatorAElement) : n = 0 := by
  have hmodel : Commute (modelRep n) OrderCertificate.p0 := by
    have hm := h.map inclusion
    rw [modelRep_eq] at hm
    change Commute (modelRep n) generatorA at hm
    rw [OrderCertificate.a_eq_generator]
    exact hm
  have h0 := congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hmodel.eq
  have h2 := congrArg (fun p : Equiv.Perm (Fin 100) => p 2) hmodel.eq
  simp only [Equiv.Perm.mul_apply] at h0 h2
  simpa [modelCheck, h0, h2] using hc

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact
