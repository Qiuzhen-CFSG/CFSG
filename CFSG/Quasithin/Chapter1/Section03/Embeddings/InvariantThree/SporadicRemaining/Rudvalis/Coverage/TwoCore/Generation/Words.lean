module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.FixedSylow
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# Word certificates for Rudvalis one-element extensions

The first fourteen letters are the preserved generators of the fixed Sylow
subgroup; the last letter is the adjoined element. Adding inverse letters
allows an externally discovered word to be checked as an equality on the
actual degree-4060 carrier. Two such equalities recovering the standard
ATLAS generators prove that the extension is the whole model.

The soundness proof is ordinary subgroup closure and uses no group-order
or maximal-coverage assertion. Concrete word equalities remain separate
proof obligations. The ATLAS sources are attributed in `SylowCertificate.Candidate`;
the source application is Aschbacher--Smith, printed p.511 (PDF p.528),
citing Aschbacher (1986), no.343.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation
open Subgroup RadicalCoverage.SylowCertificate Theory.GroupTheory
open Theory.GroupTheory.SubgroupEnumeration

/-- Fourteen fixed Sylow generators followed by the adjoined element. -/
@[expose] public def extensionGenerators (g : Model) : Fin 15 → Model :=
  Fin.lastCases g candidateGenerator

/-- The inverse-closed alphabet has its positive letters first. -/
@[expose] public def extensionWord (g : Model) (w : List (Fin 30)) : Model :=
  evalWord (symmGen (extensionGenerators g)) w

/-- Every recovery word belongs to the actual one-element extension. -/
public theorem extensionWord_mem (g : Model) (w : List (Fin 30)) :
    extensionWord g w ∈ closure (insert g (candidate : Set Model)) := by
  have hgen (j : Fin 15) : extensionGenerators g j ∈
      closure (insert g (candidate : Set Model)) := by
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact subset_closure (Set.mem_insert _ _)
    · simp only [extensionGenerators, Fin.lastCases_castSucc]
      exact subset_closure (Set.mem_insert_of_mem _ (subset_closure ⟨k, rfl⟩))
  apply evalWord_mem
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [symmGen, Fin.addCases_left] using hgen j
  · simpa only [symmGen, Fin.addCases_right] using
      (closure (insert g (candidate : Set Model))).inv_mem (hgen j)

/-- Recovering both standard generators certifies the full extension. -/
public theorem generation_of_words (g : Model) (wa wb : List (Fin 30))
    (ha : extensionWord g wa = a) (hb : extensionWord g wb = b) :
    closure (insert g (candidate : Set Model)) = ⊤ :=
  eq_top_of_a_mem_of_b_mem _ (ha ▸ extensionWord_mem g wa) (hb ▸ extensionWord_mem g wb)

end Rudvalis.SylowOvergroups.TwoCore.Generation
