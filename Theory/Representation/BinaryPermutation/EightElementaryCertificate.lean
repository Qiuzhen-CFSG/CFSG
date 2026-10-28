module
public import Theory.Representation.BinaryPermutation.EightElementaryCertificate.Extensions
/-!
# Fixed-space witnesses for the elementary eight-point actors

Each nonidentity row either has a vector orbit of size two, or is one of
eight rows with three distinct stabilizers of relative index four whose
intersection has relative index eight. The witnesses are actual words in
the binary permutation core, and fixation is checked modulo its constant
line, exactly the natural six-dimensional quotient.

Source: Aschbacher--Smith,12.6.28(2), printed pp.833--834.
-/
@[expose] public section
open BinaryPermutation BinaryPermutation.EightNonsingular
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryPermutation.EightElementaryCertificate
def word (w : Fin 128) : core (Fin 8) :=
  ∑ j : Fin 7, if w.val.testBit j.val then pair ⟨j.val, by omega⟩ 7 else 0
def fixes (a : Fin 128) (v : core (Fin 8)) : Prop :=
  (coreRepresentation (Fin 8) (treeWord a) v - v).val = 0 ∨
  (coreRepresentation (Fin 8) (treeWord a) v - v).val = allOne (Fin 8)
instance (a : Fin 128) (v : core (Fin 8)) : Decidable (fixes a v) := by
  unfold fixes; infer_instance
def good : Fin 8 → Fin 241 := ![185,193,199,202,203,235,236,237]
def badCode : Array Nat := #[0,5,5,5,17,5,5,5,65,5,5,5,17,5,5,5,3,3,3,3,3,3,3,3,17,5,5,5,17,5,5,5,3,3,3,3,3,3,3,3,3,3,3,3,17,5,20,5,17,5,20,5,20,5,20,5,17,5,17,5,17,5,17,5,17,5,65,5,17,5,80,3,3,3,3,5,48,5,48,3,3,17,5,5,5,3,3,3,3,5,5,17,68,3,3,5,20,5,65,3,3,5,20,17,5,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,48,5,5,5,3,3,5,5,48,48,5,48,5,48,3,3,3,3,5,48,48,5,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,5,5,6,6,5,5,6,6,65,17,80,48,48,5,68,20,0,5,48,48,48,5,65,17,0,5,48,48,48,5,0,3,3,0,0,3,3,3,3,5,48,3,48,48,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,0,0,0,48,3,3]
def badVector (r : Fin 241) : core (Fin 8) := word ⟨badCode[r.val]! % 128, Nat.mod_lt _ (by decide)⟩
def vectors : Fin 8 → Fin 3 → core (Fin 8) := ![![word 58,word 46,word 123],![word 58,word 126,word 43],![word 126,word 46,word 43],![word 58,word 126,word 123],![word 58,word 46,word 43],![word 106,word 108,word 111],![word 105,word 111,word 108],![word 58,word 46,word 43]]
def fixed (r : Fin 241) (v : core (Fin 8)) : Finset (Fin 128) :=
  (members r).filter (fun a => fixes a v)
def common (j : Fin 8) : Finset (Fin 128) :=
  (members (good j)).filter (fun a => ∀ i : Fin 3, fixes a (vectors j i))
def obstruction (r : Fin 241) : Prop :=
  r = 0 ∨ (∃ j, good j = r) ∨
    (members r).card = 2 * (fixed r (badVector r)).card ∧ 0 < (members r).card
instance (r : Fin 241) : Decidable (obstruction r) := by unfold obstruction; infer_instance
set_option maxRecDepth 4096 in
theorem obstructions : ∀ r, obstruction r := by
  intro r
  fin_cases r <;> decide +kernel

def triple (j : Fin 8) : Prop :=
  (members (good j)).card = 8 * (common j).card ∧ 0 < (common j).card ∧
    Function.Injective (fun i => fixed (good j) (vectors j i)) ∧
    ∀ i, (fixed (good j) (vectors j i)).card = 2 * (common j).card
instance (j : Fin 8) : Decidable (triple j) := by unfold triple; infer_instance
set_option maxRecDepth 4096 in
theorem triples : ∀ j, triple j := by
  intro j
  fin_cases j <;> decide +kernel
end BinaryPermutation.EightElementaryCertificate
