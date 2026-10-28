module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.CycleCheck
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Maps
/-!
# Small certificates for the Fi23 candidate tables

Disjoint support masks combine checked cycle blocks without rescanning the
entire permutation. A balanced Boolean range check turns numerical identities
into universal pointwise equalities. The consumers identify the exact ATLAS
word and its fixed letters (GLS3 Table 5.3u).
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
open AtlasCarriers
open Sporadic.Fischer.Fi22.KernelCertificate
structure Supported (xs : List (Fin 31671)) (m : Nat) : Prop where
  nodup : xs.Nodup
  mask_eq : CycleCheck.mask xs = m

theorem mask_append (xs ys : List (Fin 31671)) :
    CycleCheck.mask (xs ++ ys) = CycleCheck.mask xs ||| CycleCheck.mask ys := by
  induction xs with
  | nil => simp [CycleCheck.mask]
  | cons x xs ih => simp only [List.cons_append, CycleCheck.mask, ih, Nat.or_assoc]

theorem Supported.append {xs ys : List (Fin 31671)} {m n k : Nat}
    (hx : Supported xs m) (hy : Supported ys n)
    (hdis : m &&& n = 0) (hk : m ||| n = k) : Supported (xs ++ ys) k := by
  refine ⟨List.nodup_append'.mpr ⟨hx.nodup, hy.nodup, ?_⟩, ?_⟩
  · intro x hxs hys
    have hm : m.testBit x.val = true := hx.mask_eq ▸ (CycleCheck.mask_spec xs x).mpr hxs
    have hn : n.testBit x.val = true := hy.mask_eq ▸ (CycleCheck.mask_spec ys x).mpr hys
    have hz := congrArg (fun v : Nat => v.testBit x.val) hdis
    simp [Nat.testBit_and, hm, hn] at hz
  · rw [mask_append, hx.mask_eq, hy.mask_eq, hk]

theorem Supported.blocks_cons {p : List (List (Fin 31671))}
    {ps : List (List (List (Fin 31671)))} {m n k : Nat}
    (hx : Supported p.flatten m) (hy : Supported ps.flatten.flatten n)
    (hdis : m &&& n = 0) (hk : m ||| n = k) :
    Supported (p :: ps).flatten.flatten k := by
  simpa only [List.flatten_cons, List.flatten_append] using hx.append hy hdis hk

def checkRange (f : Nat → Bool) : Nat → Nat → Bool
  | 0, start => f start
  | d + 1, start => checkRange f d start && checkRange f d (start + 2^d)

theorem checkRange_spec (f : Nat → Bool) (d start : Nat) :
    checkRange f d start = true ↔
      ∀ i, start ≤ i → i < start + 2^d → f i = true := by
  induction d generalizing start with
  | zero =>
    simp only [checkRange, pow_zero]
    constructor
    · intro h i hi hi'
      have : i = start := by omega
      simpa [this] using h
    · intro h
      exact h start le_rfl (by omega)
  | succ d ih =>
    rw [checkRange, Bool.and_eq_true, ih, ih, pow_succ]
    constructor
    · rintro ⟨hl, hr⟩ i hi hi'
      by_cases h : i < start + 2^d
      · exact hl i hi h
      · exact hr i (by omega) (by omega)
    · intro h
      constructor
      · intro i hi hi'
        exact h i hi (by omega)
      · intro i hi hi'
        exact h i (by omega) (by omega)

def wordMap (x : Fin 31671) :=
  aMap (bMap (bMap (aMap (bMap (bMap (aMap (bMap (aMap (bMap (aMap (bMap x)))))))))))

def wordCheck (i : Nat) : Bool :=
  wordMap (Fin.ofNat 31671 i) == wMap (Fin.ofNat 31671 i)
def candidateCheck (i : Nat) : Bool :=
  (wMap^[7]) (Fin.ofNat 31671 i) == cMap (Fin.ofNat 31671 i)
def involutionCheck (i : Nat) : Bool :=
  cMap (cMap (Fin.ofNat 31671 i)) == Fin.ofNat 31671 i
def fixedCheck (i : Nat) : Bool :=
  (cMap (Fin.ofNat 31671 i) == Fin.ofNat 31671 i) ==
  (ImageData.pointIndex (ImageData.index (Fin.ofNat 31671 i)) == Fin.ofNat 31671 i)
end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
