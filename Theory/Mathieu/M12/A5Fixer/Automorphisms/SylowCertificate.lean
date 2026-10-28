module

public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Certificate

/-!
# Two fusion tests for the M₁₂ Sylow automorphism restrictions

Every automorphism of M₁₂ preserves conjugacy. In the checked 64-element
Sylow coordinates, elements 1 and 26 are conjugate, as are elements 4 and 5.
Their images must therefore have equal support sizes as permutations of the
Witt design. These two tests, together with the existing seven order tests,
leave at most 64 triples of generator images. Automorphisms need not preserve
individual permutation cycle types: only the equality for each conjugate pair
is used, so this calculation includes outer automorphisms.

Short words in the standard M₁₂ generators certify the conjugacies. All word
identities, support sizes, and candidate coverage are checked by Lean's kernel.
The untrusted certificate search is in `source/generate.py`; the marked
permutations and attribution are inherited from `SmallParabolicPair.Seeds`.
Source context: Aschbacher–Smith 16.1.5(4) and 16.3.5, combined manuscript
of 1 March 2004, printed pp.1171 and 1178–1179.
-/

@[expose] public section

namespace Sporadic.Mathieu.M12A5Fixer.Automorphisms.SylowCertificate
open M12SmallPair M12SmallPair.SylowAutomorphismGroup
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

def supportSize (i : Fin 64) : ℕ :=
  (#[0,12,8,10,8,8,8,8,8,8,8,12,8,10,12,10,12,12,12,10,8,12,12,8,10,8,12,8,12,8,8,8,12,12,8,8,12,8,12,8,12,8,8,8,12,10,12,12,12,12,12,10,12,12,12,10,12,12,12,8,8,12,12,12] : Array ℕ)[i.val]!

theorem supportSize_eq : ∀ i : Fin 64,
    supportSize i = ((element i : M12) : Equiv.Perm (Fin 12)).support.card := by
  decide +kernel

private noncomputable def word : List Bool → M12
  | [] => 1
  | b :: bs => (if b then (⟨m12GeneratorB, m12GeneratorB_mem⟩ : M12)
      else ⟨m12GeneratorA, m12GeneratorA_mem⟩) * word bs

theorem first_fusion : IsConj (element 1 : M12) (element 26 : M12) := by
  refine isConj_iff.mpr ⟨word [false,true,false,true,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true,false], ?_⟩
  decide +kernel

theorem second_fusion : IsConj (element 4 : M12) (element 5 : M12) := by
  refine isConj_iff.mpr ⟨word [false,true,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true,true], ?_⟩
  decide +kernel

def candidates (i : Fin 64) : Fin 64 × Fin 64 × Fin 64 :=
  (#[(1,2,3),(1,2,24),(1,2,45),(1,2,51),(1,12,3),(1,12,24),(1,12,45),(1,12,51),(2,1,14),(2,1,16),(2,1,18),(2,1,21),(2,11,14),(2,11,16),(2,11,18),(2,11,21),(11,2,13),(11,2,15),(11,2,19),(11,2,55),(11,12,13),(11,12,15),(11,12,19),(11,12,55),(12,1,44),(12,1,46),(12,1,48),(12,1,49),(12,11,44),(12,11,46),(12,11,48),(12,11,49),(20,56,16),(20,56,21),(20,56,44),(20,56,48),(20,58,16),(20,58,21),(20,58,44),(20,58,48),(23,56,14),(23,56,18),(23,56,46),(23,56,49),(23,58,14),(23,58,18),(23,58,46),(23,58,49),(56,20,3),(56,20,15),(56,20,24),(56,20,55),(56,23,3),(56,23,15),(56,23,24),(56,23,55),(58,20,13),(58,20,19),(58,20,45),(58,20,51),(58,23,13),(58,23,19),(58,23,45),(58,23,51)] : Array (Fin 64 × Fin 64 × Fin 64))[i.val]!

theorem candidate_coverage : ∀ a b c : Fin 64, admissible a b c →
    supportSize (substitute a b c 1) = supportSize (substitute a b c 26) →
    supportSize (substitute a b c 4) = supportSize (substitute a b c 5) →
    ∃ i : Fin 64, candidates i = (a,b,c) := by
  have check : ∀ a : Fin 64, powerTest a 4 →
      ∀ b : Fin 64, powerTest b 4 → powerTest (multiply a b) 2 →
      ∀ c : Fin 64, powerTest c 8 → powerTest (multiply a c) 4 →
      powerTest (multiply b c) 2 → powerTest (multiply (multiply a c) c) 2 →
      supportSize (substitute a b c 1) = supportSize (substitute a b c 26) →
      supportSize (substitute a b c 4) = supportSize (substitute a b c 5) →
      ∃ i : Fin 64, candidates i = (a,b,c) := by
    intro a
    fin_cases a <;> decide +kernel
  rintro a b c ⟨ha,hb,hc,hab,hac,hbc,hacc⟩ h₁ h₂
  exact check a ha b hb hab c hc hac hbc hacc h₁ h₂
end Sporadic.Mathieu.M12A5Fixer.Automorphisms.SylowCertificate
