module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.RootDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Graph


/-!
# Positive-root norms for full-support binary SL₄ vectors

For the reduced Weyl word 012010, the successive positive roots are
01, 02, 03, 12, 13, 23. Moving their differences past the Weyl prefixes
reduces the sixfold norm to the six active rank-one relations. Thus it
recovers the original highest vector. The first three differences belong
to the line radical; diagram reversal supplies the hyperplane radical.

On a nonzero full-support vector neither radical, nor any component
conjugate, can be contained in a cubic actor of the full linear normalizer.
This is an actual cubicity obstruction, without an absolute irreducibility,
module catalogue or degree assumption. The other actor configurations
remain obligations of the adjacent-support displacement argument.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455; Guralnick–Malle,
Classification of 2F-modules, II, author manuscript Proposition 4.8(3B).
The rank-one input is the concrete `FourSmallModules.RootDifferences` API.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
open CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

/-- The six positive transvections in the order associated to 012010. -/
def fullSupportPositiveRoot : Fin 6 → Group := ![
  simpleUpper 0,
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 2) (by decide) 1,
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 3) (by decide) 1,
  simpleUpper 1,
  Matrix.SpecialLinearGroup.transvection (i := 1) (j := 3) (by decide) 1,
  simpleUpper 2]

private def fullSupportWord : Fin 6 → Fin 3 := ![0, 1, 2, 0, 1, 0]

private def fullSupportWeylPrefix : Fin 7 → Group := ![
  1,
  simpleSwap 0,
  simpleSwap 0 * simpleSwap 1,
  simpleSwap 0 * simpleSwap 1 * simpleSwap 2,
  simpleSwap 0 * simpleSwap 1 * simpleSwap 2 * simpleSwap 0,
  simpleSwap 0 * simpleSwap 1 * simpleSwap 2 * simpleSwap 0 * simpleSwap 1,
  simpleSwap 0 * simpleSwap 1 * simpleSwap 2 * simpleSwap 0 * simpleSwap 1 * simpleSwap 0]

private theorem step (k : Fin 6) :
    fullSupportWeylPrefix k.succ = fullSupportWeylPrefix k.castSucc * simpleSwap (fullSupportWord k) ∧
    fullSupportPositiveRoot k * fullSupportWeylPrefix k.castSucc = fullSupportWeylPrefix k.castSucc * simpleUpper (fullSupportWord k) := by
  revert k
  decide

private theorem longest_prefix : fullSupportWeylPrefix 6 = longestExchange := by decide

attribute [local irreducible] fullSupportPositiveRoot fullSupportWord fullSupportWeylPrefix

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem move (σ : Representation (ZMod 2) Group V)
    {g k t : Group} (he : g * t = t * k) (x : V) :
    displacement σ g (σ t x) = σ t (displacement σ k x) := by
  simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  simp only [← Module.End.mul_apply, ← map_mul, he]

private theorem norm_step {σ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector σ Finset.univ v) (k : Fin 6) :
    displacement σ (fullSupportPositiveRoot k) (σ (fullSupportWeylPrefix k.succ) v) = σ (fullSupportWeylPrefix k.castSucc) v := by
  rw [(step k).1, map_mul, Module.End.mul_apply, move σ (step k).2]
  have hs := h.upperDifference_swap (Finset.mem_univ (fullSupportWord k))
  change displacement σ (simpleUpper (fullSupportWord k)) (σ (simpleSwap (fullSupportWord k)) v) = v at hs
  rw [hs]

private def fullSupportTail (σ : Representation (ZMod 2) Group V) (v : V) : V :=
  displacement σ (fullSupportPositiveRoot 3) (displacement σ (fullSupportPositiveRoot 4)
    (displacement σ (fullSupportPositiveRoot 5) (σ (fullSupportWeylPrefix 6) v)))

private theorem norm_recovery {σ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector σ Finset.univ v) :
    displacement σ (fullSupportPositiveRoot 0) (displacement σ (fullSupportPositiveRoot 1)
      (displacement σ (fullSupportPositiveRoot 2) (fullSupportTail σ v))) = v := by
  change displacement σ (fullSupportPositiveRoot 0) (displacement σ (fullSupportPositiveRoot 1)
    (displacement σ (fullSupportPositiveRoot 2) (displacement σ (fullSupportPositiveRoot 3)
      (displacement σ (fullSupportPositiveRoot 4) (displacement σ (fullSupportPositiveRoot 5) (σ (fullSupportWeylPrefix 6) v)))))) = v
  have hs5 : displacement σ (fullSupportPositiveRoot 5) (σ (fullSupportWeylPrefix 6) v) =
      σ (fullSupportWeylPrefix 5) v := by
    convert norm_step h 5 using 1 <;> rfl
  have hs4 : displacement σ (fullSupportPositiveRoot 4) (σ (fullSupportWeylPrefix 5) v) =
      σ (fullSupportWeylPrefix 4) v := by
    convert norm_step h 4 using 1 <;> rfl
  have hs3 : displacement σ (fullSupportPositiveRoot 3) (σ (fullSupportWeylPrefix 4) v) =
      σ (fullSupportWeylPrefix 3) v := by
    convert norm_step h 3 using 1 <;> rfl
  have hs2 : displacement σ (fullSupportPositiveRoot 2) (σ (fullSupportWeylPrefix 3) v) =
      σ (fullSupportWeylPrefix 2) v := by
    convert norm_step h 2 using 1 <;> rfl
  have hs1 : displacement σ (fullSupportPositiveRoot 1) (σ (fullSupportWeylPrefix 2) v) =
      σ (fullSupportWeylPrefix 1) v := by
    convert norm_step h 1 using 1 <;> rfl
  have hs0 : displacement σ (fullSupportPositiveRoot 0) (σ (fullSupportWeylPrefix 1) v) =
      σ (fullSupportWeylPrefix 0) v := by
    convert norm_step h 0 using 1 <;> rfl
  rw [hs5, hs4, hs3, hs2, hs1, hs0]
  simp [fullSupportWeylPrefix]

/-- The six positive-root differences recover a full-support highest vector
from its longest-coordinate-exchange translate. -/
theorem full_support_six_root_norm
    {σ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector σ Finset.univ v) :
    displacement σ (fullSupportPositiveRoot 0)
      (displacement σ (fullSupportPositiveRoot 1)
        (displacement σ (fullSupportPositiveRoot 2)
          (displacement σ (fullSupportPositiveRoot 3)
            (displacement σ (fullSupportPositiveRoot 4)
              (displacement σ (fullSupportPositiveRoot 5)
                (σ longestExchange v)))))) = v := by
  simpa only [fullSupportTail, longest_prefix] using norm_recovery h

/-- Three generators of the line radical, or of the hyperplane radical after
positive-root-preserving diagram reversal. -/
def fullSupportRadicalRoot (dual : Bool) (k : Fin 3) : Group :=
  if dual then diagramReversal (fullSupportPositiveRoot (k.castAdd 3))
  else fullSupportPositiveRoot (k.castAdd 3)

/-- Both end-node radicals have a nonzero third displacement on a nonzero
full-support highest vector. The original representation is retained. -/
theorem exists_full_support_radical_norm
    {σ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector σ Finset.univ v) (dual : Bool) :
    ∃ w : V, displacement σ (fullSupportRadicalRoot dual 0)
      (displacement σ (fullSupportRadicalRoot dual 1)
        (displacement σ (fullSupportRadicalRoot dual 2) w)) = v := by
  cases dual
  · refine ⟨fullSupportTail σ v, ?_⟩
    change displacement σ (fullSupportPositiveRoot 0)
      (displacement σ (fullSupportPositiveRoot 1)
        (displacement σ (fullSupportPositiveRoot 2) (fullSupportTail σ v))) = v
    exact norm_recovery h
  · have htw : LocalHighestVector (diagramTwist σ) Finset.univ v := by
      have he : (Finset.univ : Finset (Fin 3)).image Fin.rev = Finset.univ := by decide
      simpa only [he] using localHighestVector_diagramTwist h
    refine ⟨fullSupportTail (diagramTwist σ) v, ?_⟩
    change displacement (diagramTwist σ) (fullSupportPositiveRoot 0)
      (displacement (diagramTwist σ) (fullSupportPositiveRoot 1)
        (displacement (diagramTwist σ) (fullSupportPositiveRoot 2)
          (fullSupportTail (diagramTwist σ) v))) = v
    exact norm_recovery htw

attribute [local irreducible] fullSupportRadicalRoot

/-- A full-support module is not cubic for an actor containing either end-node
radical or any component conjugate. Actors may also contain outer elements. -/
theorem not_isCubic_of_full_support_radical_mem
    {σ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector σ Finset.univ v) (hv : v ≠ 0)
    (A : Subgroup (linearNormalizer σ)) (dual : Bool) (c : Group)
    (hroot : ∀ k : Fin 3,
      componentEmbedding σ (c * fullSupportRadicalRoot dual k * c⁻¹) ∈ A) :
    ¬ IsCubic (normalizerRepresentation σ) A := by
  intro hc
  obtain ⟨w, hw⟩ := exists_full_support_radical_norm h dual
  have hh := hc _ (hroot 0) _ (hroot 1) _ (hroot 2) (σ c w)
  change displacement σ (c * fullSupportRadicalRoot dual 0 * c⁻¹)
    (displacement σ (c * fullSupportRadicalRoot dual 1 * c⁻¹)
      (displacement σ (c * fullSupportRadicalRoot dual 2 * c⁻¹) (σ c w))) = 0 at hh
  have hm (g : Group) (x : V) :
      displacement σ (c * g * c⁻¹) (σ c x) = σ c (displacement σ g x) :=
    move σ (by group) x
  rw [hm, hm, hm, hw] at hh
  have hz := congrArg (σ c⁻¹) hh
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply, map_zero] at hz
  exact hv hz

/-- The full-support assembly can discard both conjugate radical configurations
using only the given cubicity assumption. -/
theorem full_support_radical_avoidance
    {σ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector σ Finset.univ v) (hv : v ≠ 0)
    (A : Subgroup (linearNormalizer σ)) (hc : IsCubic (normalizerRepresentation σ) A) :
    ∀ (dual : Bool) (c : Group), ¬ ∀ k : Fin 3,
      componentEmbedding σ (c * fullSupportRadicalRoot dual k * c⁻¹) ∈ A := by
  intro dual c hroot
  exact not_isCubic_of_full_support_radical_mem h hv A dual c hroot hc

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
