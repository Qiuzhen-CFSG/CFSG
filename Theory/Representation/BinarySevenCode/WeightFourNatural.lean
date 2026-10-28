module
public import Theory.Representation.BinarySevenCode.WeightFourPointMarking
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# The three-letter natural module in a weight-four stabilizer

Extend the binary augmentation core on the three complementary letters by
zero on the four-letter support. Its image is exactly the even words
vanishing on that support. The extension intertwines the original block
marking with the permutation action. The alternating three-group acts
faithfully and transitively on its three nonzero vectors.

The terminal local-factor construction uses this marking for the whole
moved seed, not just for a vector inside it.
Source: Aschbacher--Smith, completion of 12.3.1, printed p.812.
-/

@[expose] public noncomputable section
open Subgroup
namespace BinarySevenCode.WeightFourNatural
open WeightTwoGeometry WeightFourLocal
open BinaryPermutation

def complementLetters (w : EvenWord) (hw : weight w.val = 4) : Fin 3 ↪ Fin 7 :=
  (WeightFourLocal.threeLetters w hw).symm.toEmbedding.trans
    (Function.Embedding.subtype _)

theorem complementLetters_not_support (w : EvenWord) (hw : weight w.val = 4) (k : Fin 3) :
    complementLetters w hw k ∉ support w :=
  Finset.mem_compl.mp ((WeightFourLocal.threeLetters w hw).symm k).property

theorem complementLetters_exhaust (w : EvenWord) (hw : weight w.val = 4) (i : Fin 7)
    (hi : i ∉ support w) : ∃ k, complementLetters w hw k = i := by
  let x : Complement w := ⟨i,Finset.mem_compl.mpr hi⟩
  refine ⟨WeightFourLocal.threeLetters w hw x,?_⟩
  exact congrArg Subtype.val ((WeightFourLocal.threeLetters w hw).symm_apply_apply x)

def extendThreeFull (w : EvenWord) (hw : weight w.val = 4) :
    Full (Fin 3) →ₗ[ZMod 2] Full (Fin 7) where
  toFun x := ∑ k, Pi.single (complementLetters w hw k) (x k)
  map_add' x y := by simp only [Pi.add_apply,Pi.single_add,Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply,Pi.single_smul,Finset.smul_sum,RingHom.id_apply]

theorem extendThreeFull_letter (w : EvenWord) (hw : weight w.val = 4)
    (x : Full (Fin 3)) (k : Fin 3) :
    extendThreeFull w hw x (complementLetters w hw k) = x k := by
  simp [extendThreeFull,Pi.single_apply,(complementLetters w hw).injective.eq_iff]

theorem extendThreeFull_support (w : EvenWord) (hw : weight w.val = 4)
    (x : Full (Fin 3)) (i : Fin 7) (hi : i ∈ support w) : extendThreeFull w hw x i = 0 := by
  have hn (k : Fin 3) : i ≠ complementLetters w hw k :=
    fun h => complementLetters_not_support w hw k (h ▸ hi)
  simp [extendThreeFull,hn]

theorem augmentation_extendThreeFull (w : EvenWord) (hw : weight w.val = 4)
    (x : Full (Fin 3)) :
    augmentation (Fin 7) (extendThreeFull w hw x) = augmentation (Fin 3) x := by
  simp [extendThreeFull,augmentation]

def extendThree (w : EvenWord) (hw : weight w.val = 4) :
    core (Fin 3) →ₗ[ZMod 2] EvenWord :=
  ((extendThreeFull w hw).comp (core (Fin 3)).subtype).codRestrict _ (by
    intro x
    rw [evenWords_eq_core]
    change augmentation (Fin 7) (extendThreeFull w hw x.val) = 0
    rw [augmentation_extendThreeFull]
    exact x.property)

theorem extendThree_injective (w : EvenWord) (hw : weight w.val = 4) :
    Function.Injective (extendThree w hw) := by
  intro x y h
  apply Subtype.ext
  funext k
  exact (extendThreeFull_letter w hw x.val k).symm.trans
    ((congrArg (fun z : EvenWord => z.val (complementLetters w hw k)) h).trans
      (extendThreeFull_letter w hw y.val k))

theorem range_extendThree (w : EvenWord) (hw : weight w.val = 4) (x : EvenWord) :
    x ∈ (extendThree w hw).range ↔ ∀ i ∈ support w, x.val i = 0 := by
  constructor
  · rintro ⟨y,rfl⟩ i hi
    exact extendThreeFull_support w hw y.val i hi
  · intro hx
    let y : Full (Fin 3) := fun k => x.val (complementLetters w hw k)
    have he : extendThreeFull w hw y = x.val := by
      funext i
      by_cases hi : i ∈ support w
      · exact (extendThreeFull_support w hw y i hi).trans (hx i hi).symm
      · obtain ⟨k,rfl⟩ := complementLetters_exhaust w hw i hi
        exact extendThreeFull_letter w hw y k
    have hy : y ∈ core (Fin 3) := by
      change augmentation (Fin 3) y = 0
      rw [← augmentation_extendThreeFull w hw,he]
      exact (show x.val ∈ core (Fin 7) from evenWords_eq_core ▸ x.property)
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩


theorem complementLetters_action (w : EvenWord) (hw : weight w.val = 4)
    (g : symmetricStabilizer w) (k : Fin 3) :
    complementLetters w hw ((pointEquiv w hw g).2 k) = g.val (complementLetters w hw k) := by
  let e := WeightFourLocal.threeLetters w hw
  have h := pointEquiv_second w hw g (e.symm k)
  rw [e.apply_symm_apply] at h
  have hh := congrArg (fun j => (e.symm j).val) h
  rw [e.symm_apply_apply] at hh
  exact hh

theorem extendThree_equivariant (w : EvenWord) (hw : weight w.val = 4)
    (g : symmetricStabilizer w) (x : core (Fin 3)) :
    extendThree w hw (coreRepresentation (Fin 3) (pointEquiv w hw g).2 x) =
      evenRepresentation g.val (extendThree w hw x) := by
  apply Subtype.ext
  funext i
  obtain ⟨i,rfl⟩ := g.val.surjective i
  change extendThreeFull w hw _ (g.val i) =
    extendThreeFull w hw x.val (g.val.symm (g.val i))
  rw [Equiv.symm_apply_apply]
  by_cases hi : i ∈ support w
  · rw [extendThreeFull_support w hw _ _ ((stabilizer_mem_support w g i).mpr hi),
      extendThreeFull_support w hw _ i hi]
  · obtain ⟨k,rfl⟩ := complementLetters_exhaust w hw i hi
    rw [← complementLetters_action,extendThreeFull_letter,extendThreeFull_letter]
    exact congrArg x.val ((pointEquiv w hw g).2.symm_apply_apply k)

local instance : DecidablePred (· ∈ core (Fin 3)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 3)) := Subtype.fintype _

theorem threeCore_card : Nat.card (core (Fin 3)) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem threeCore_transitive (x y : core (Fin 3)) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : alternatingGroup (Fin 3), alternatingCoreRepresentation (Fin 3) g x = y := by
  exact (by decide +kernel : ∀ x y : core (Fin 3), x ≠ 0 → y ≠ 0 →
    ∃ g : alternatingGroup (Fin 3), alternatingCoreRepresentation (Fin 3) g x = y) x y hx hy

theorem threeCore_faithful (g : alternatingGroup (Fin 3))
    (h : ∀ x, alternatingCoreRepresentation (Fin 3) g x = x) : g = 1 := by
  exact (by decide +kernel : ∀ g : alternatingGroup (Fin 3),
    (∀ x, alternatingCoreRepresentation (Fin 3) g x = x) → g = 1) g h

end BinarySevenCode.WeightFourNatural
