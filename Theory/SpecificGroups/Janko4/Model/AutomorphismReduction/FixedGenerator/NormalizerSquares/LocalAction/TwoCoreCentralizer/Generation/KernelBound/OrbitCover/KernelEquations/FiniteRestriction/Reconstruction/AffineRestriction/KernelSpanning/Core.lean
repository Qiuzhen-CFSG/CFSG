module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.Equations

/-!
# Propagation along a certified elimination trace

This adapter applies Binary.trace_sound to rows indexed by natural numbers
and existentially supplied predecessor lists. Only earlier rows may occur;
no part of the elimination is trusted. See KernelSpanning/source/README.md.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
open LinearMembership GeneratorCertificates Binary

/-- Unpack an ordered predecessor list, with thirteen bits per index. -/
def decodeParents : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, c => c % 8192 :: decodeParents n (c >>> 13)

def base (i : ℕ) : ℕ := if h : i < 2373 then rawRow ⟨i, h⟩ else 0

theorem base_zero (S : RestrictionMatrix) (hS : RawEquations S) (i : ℕ) :
    ev (flat S) (base i) = 0 := by
  unfold base
  split
  · rename_i h
    simpa only [rawRows, get_ofFn] using hS ⟨i,h⟩
  · exact ev_zero _

theorem trace_of_exists {n d : ℕ} (x : Fin n → ZMod 2) (r b : ℕ → ℕ)
    (hb : ∀ i : Fin d, ev x (b i.val) = 0)
    (ht : ∀ i : Fin d, ∃ ps : List ℕ,
      (∀ j ∈ ps, j < i.val) ∧ r i.val = b i.val ^^^ xorList (ps.map r)) :
    ∀ i : Fin d, ev x (r i.val) = 0 := by
  classical
  let rows := Vector.ofFn (fun i : Fin d => r i.val)
  let bases := Vector.ofFn (fun i : Fin d => b i.val)
  let parents := Vector.ofFn (fun i : Fin d => (ht i).choose)
  have hz := trace_sound x rows bases parents
    (by intro i; simpa only [bases, get_ofFn] using hb i)
    (by
      intro i
      simp only [rows, bases, parents, get_ofFn]
      refine ⟨(ht i).choose_spec.1, ?_⟩
      refine (ht i).choose_spec.2.trans ?_
      congr 2
      apply List.map_congr_left
      intro j hj
      have hjd : j < d := ((ht i).choose_spec.1 j hj).trans i.isLt
      rw [getElem!_pos _ _ (by simpa using hjd)]
      change r j = (Vector.ofFn (fun i : Fin d => r i.val)).get ⟨j,hjd⟩
      rw [get_ofFn])
  intro i
  simpa only [rows, get_ofFn] using hz i

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
