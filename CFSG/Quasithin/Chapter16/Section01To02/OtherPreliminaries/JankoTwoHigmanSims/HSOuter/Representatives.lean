module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements

/-!
# Two concrete permutations for the outer HS calculation

These permutations were found in the normalizer of the exact degree-100 ATLAS
carrier by the retained GAP search. Only their involution identities are asserted
here, checked on all 100 letters in Lean's kernel. Their normalizer membership,
exhaustive class coverage, and centralizer structures are separate obligations.
The centralizers below are subgroups of the actual HS carrier, not of S₁₀₀.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m,
classes 2C and 2D. GAP supplies candidate permutations, never proof premises.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
open Sporadic.LeechRelated.HS Subgroup
set_option maxRecDepth 10000

/-- The centralizer inside the fixed carrier of a permutation of its letters. -/
def permutationCentralizer (p : Equiv.Perm (Fin 100)) : Subgroup Carrier :=
  (centralizer ({p} : Set (Equiv.Perm (Fin 100)))).comap inclusion

/-- The packed action used for kernel reduction of the specified permutation. -/
def elementaryPermutationMap (x : Fin 100) : Fin 100 :=
  ⟨(976787823308572170277511331410817528549761195830671295755357404349739231006986515679451746411966481911230671347460920690400147118739322269672917098539398447177885948854898719142450260375632862763485819759924747 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem elementaryPermutationMap_involutive :
    Function.Involutive elementaryPermutationMap := by
  change ∀ x : Fin 100, elementaryPermutationMap (elementaryPermutationMap x) = x
  decide +kernel

/-- A specified candidate representative; its normalizing property is not assumed. -/
def elementaryPermutation : Equiv.Perm (Fin 100) :=
  { toFun := elementaryPermutationMap
    invFun := elementaryPermutationMap
    left_inv := by exact elementaryPermutationMap_involutive
    right_inv := by exact elementaryPermutationMap_involutive }

theorem elementaryPermutation_sq : elementaryPermutation ^ 2 = 1 := by
  apply Equiv.ext
  exact elementaryPermutationMap_involutive

theorem elementaryPermutation_order : orderOf elementaryPermutation = 2 := by
  apply orderOf_eq_prime elementaryPermutation_sq
  intro h
  have := congrArg (fun p : Equiv.Perm (Fin 100) => p 0) h
  have hn : elementaryPermutation 0 ≠ (1 : Equiv.Perm (Fin 100)) 0 := by decide +kernel
  exact hn this

/-- The packed action used for kernel reduction of the specified permutation. -/
def symmetricPermutationMap (x : Fin 100) : Fin 100 :=
  ⟨(3756245018490595264011484072267667725449121136320061326222489316682213041244213857827923944881238625521644258390147379792203915754924922734268587093532300797727886359909066354026840647682457440815272525598625300 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem symmetricPermutationMap_involutive :
    Function.Involutive symmetricPermutationMap := by
  change ∀ x : Fin 100, symmetricPermutationMap (symmetricPermutationMap x) = x
  decide +kernel

/-- A specified candidate representative; its normalizing property is not assumed. -/
def symmetricPermutation : Equiv.Perm (Fin 100) :=
  { toFun := symmetricPermutationMap
    invFun := symmetricPermutationMap
    left_inv := by exact symmetricPermutationMap_involutive
    right_inv := by exact symmetricPermutationMap_involutive }

theorem symmetricPermutation_sq : symmetricPermutation ^ 2 = 1 := by
  apply Equiv.ext
  exact symmetricPermutationMap_involutive

theorem symmetricPermutation_order : orderOf symmetricPermutation = 2 := by
  apply orderOf_eq_prime symmetricPermutation_sq
  intro h
  have := congrArg (fun p : Equiv.Perm (Fin 100) => p 0) h
  have hn : symmetricPermutation 0 ≠ (1 : Equiv.Perm (Fin 100)) 0 := by decide +kernel
  exact hn this

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
