module
public import Theory.Representation.BinarySevenCode.WeightTwoSplitting
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# The five-letter augmentation module inside the seven-letter code

For a weight-two word, extend vectors on its five complementary letters by
zero. This identifies the binary augmentation core on five letters with the
vectors vanishing on the two-letter support. The identification intertwines
the literal pointwise stabilizer with the existing marked A₅ isomorphism.

Source application: Aschbacher--Smith, 12.3.7(2) and 12.3.12, pp.809,811.
-/

@[expose] public noncomputable section
open Subgroup
namespace BinarySevenCode.WeightTwoGeometry
open BinaryPermutation

theorem card_complement_five (w : EvenWord) (hw : weight w.val = 2) :
    Fintype.card (Complement w) = 5 := by
  rw [Fintype.card_coe, Finset.card_compl]
  change 7 - weight w.val = 5
  rw [hw]

def fiveLetters (w : EvenWord) (hw : weight w.val = 2) : Fin 5 ↪ Fin 7 :=
  (Fintype.equivFinOfCardEq (card_complement_five w hw)).symm.toEmbedding.trans
    (Function.Embedding.subtype _)

theorem fiveLetters_not_support (w : EvenWord) (hw : weight w.val = 2) (k : Fin 5) :
    fiveLetters w hw k ∉ support w :=
  Finset.mem_compl.mp ((Fintype.equivFinOfCardEq (card_complement_five w hw)).symm k).property

theorem fiveLetters_exhaust (w : EvenWord) (hw : weight w.val = 2) (i : Fin 7)
    (hi : i ∉ support w) : ∃ k, fiveLetters w hw k = i := by
  let x : Complement w := ⟨i,Finset.mem_compl.mpr hi⟩
  refine ⟨Fintype.equivFinOfCardEq (card_complement_five w hw) x,?_⟩
  exact congrArg Subtype.val ((Fintype.equivFinOfCardEq (card_complement_five w hw)).symm_apply_apply x)

def extendFiveFull (w : EvenWord) (hw : weight w.val = 2) :
    Full (Fin 5) →ₗ[ZMod 2] Full (Fin 7) where
  toFun x := ∑ k, Pi.single (fiveLetters w hw k) (x k)
  map_add' x y := by simp only [Pi.add_apply,Pi.single_add,Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply,Pi.single_smul,Finset.smul_sum,RingHom.id_apply]

theorem extendFiveFull_letter (w : EvenWord) (hw : weight w.val = 2)
    (x : Full (Fin 5)) (k : Fin 5) :
    extendFiveFull w hw x (fiveLetters w hw k) = x k := by
  simp [extendFiveFull,Pi.single_apply,(fiveLetters w hw).injective.eq_iff]

theorem extendFiveFull_support (w : EvenWord) (hw : weight w.val = 2)
    (x : Full (Fin 5)) (i : Fin 7) (hi : i ∈ support w) : extendFiveFull w hw x i = 0 := by
  have hn (k : Fin 5) : i ≠ fiveLetters w hw k :=
    fun h => fiveLetters_not_support w hw k (h ▸ hi)
  simp [extendFiveFull,hn]

theorem augmentation_extendFiveFull (w : EvenWord) (hw : weight w.val = 2)
    (x : Full (Fin 5)) :
    augmentation (Fin 7) (extendFiveFull w hw x) = augmentation (Fin 5) x := by
  simp [extendFiveFull,augmentation]

def extendFive (w : EvenWord) (hw : weight w.val = 2) :
    core (Fin 5) →ₗ[ZMod 2] EvenWord :=
  ((extendFiveFull w hw).comp (core (Fin 5)).subtype).codRestrict _ (by
    intro x
    rw [evenWords_eq_core]
    change augmentation (Fin 7) (extendFiveFull w hw x.val) = 0
    rw [augmentation_extendFiveFull]
    exact x.property)

theorem extendFive_injective (w : EvenWord) (hw : weight w.val = 2) :
    Function.Injective (extendFive w hw) := by
  intro x y h
  apply Subtype.ext
  funext k
  exact (extendFiveFull_letter w hw x.val k).symm.trans
    ((congrArg (fun z : EvenWord => z.val (fiveLetters w hw k)) h).trans
      (extendFiveFull_letter w hw y.val k))

theorem range_extendFive (w : EvenWord) (hw : weight w.val = 2) (x : EvenWord) :
    x ∈ (extendFive w hw).range ↔ ∀ i ∈ support w, x.val i = 0 := by
  constructor
  · rintro ⟨y,rfl⟩ i hi
    exact extendFiveFull_support w hw y.val i hi
  · intro hx
    let y : Full (Fin 5) := fun k => x.val (fiveLetters w hw k)
    have he : extendFiveFull w hw y = x.val := by
      funext i
      by_cases hi : i ∈ support w
      · exact (extendFiveFull_support w hw y i hi).trans (hx i hi).symm
      · obtain ⟨k,rfl⟩ := fiveLetters_exhaust w hw i hi
        exact extendFiveFull_letter w hw y k
    have hy : y ∈ core (Fin 5) := by
      change augmentation (Fin 5) y = 0
      rw [← augmentation_extendFiveFull w hw,he]
      exact (show x.val ∈ core (Fin 7) from evenWords_eq_core ▸ x.property)
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩

theorem fiveLetters_action (w : EvenWord) (hw : weight w.val = 2)
    (g : five w) (k : Fin 5) :
    fiveLetters w hw ((fiveEquiv w hw g).val k) = g.val.val (fiveLetters w hw k) := by
  let e := Fintype.equivFinOfCardEq (card_complement_five w hw)
  change (e.symm ((Atlas.Families.Alternating.relabel e
    (Atlas.Families.Alternating.stabilizerComplementEquiv (support w) g)).val k)).val = _
  rw [Atlas.Families.Alternating.relabel_apply,e.symm_apply_apply]
  exact Atlas.Families.Alternating.stabilizerComplementEquiv_apply (support w) g (e.symm k)

theorem extendFive_equivariant (w : EvenWord) (hw : weight w.val = 2)
    (g : five w) (x : core (Fin 5)) :
    extendFive w hw (alternatingCoreRepresentation (Fin 5) (fiveEquiv w hw g) x) =
      evenRepresentation g.val.val (extendFive w hw x) := by
  apply Subtype.ext
  funext i
  obtain ⟨i,rfl⟩ := g.val.val.surjective i
  change extendFiveFull w hw _ (g.val.val i) =
    extendFiveFull w hw x.val (g.val.val.symm (g.val.val i))
  rw [Equiv.symm_apply_apply]
  by_cases hi : i ∈ support w
  · have hgi : g.val.val i = i := g.property ⟨i,hi⟩
    rw [hgi,extendFiveFull_support w hw _ i hi,extendFiveFull_support w hw _ i hi]
  · obtain ⟨k,rfl⟩ := fiveLetters_exhaust w hw i hi
    rw [← fiveLetters_action,extendFiveFull_letter,extendFiveFull_letter]
    exact congrArg x.val ((fiveEquiv w hw g).val.symm_apply_apply k)

end BinarySevenCode.WeightTwoGeometry
