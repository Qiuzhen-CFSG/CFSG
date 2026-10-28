module
public import Theory.Representation.BinarySevenCode.PermutationAction
public import Theory.GroupTheory.SolvableResidual
public import Theory.AtlasPort.OtherSporadic.Families.Alternating.Stabilizers
/-!
# The perfect residual of a weight-two stabilizer in the binary A₇ module

The stabilizer of a weight-two word permutes its two support letters.
This action has solvable image, so the perfect residual fixes those letters
pointwise. Conversely, their pointwise fixer is the alternating group on
the five complementary letters and is perfect. The two subgroups coincide.

The complement equivalence is the existing attributed ATLAS port, with
its original embedding. Source application: Aschbacher--Smith, Lemma
12.3.7(2), printed p.809, for C_L(e(2))∞.
-/
@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace BinarySevenCode
namespace WeightTwoGeometry
abbrev A7 := alternatingGroup (Fin 7)

def support (w : EvenWord) : Finset (Fin 7) := Finset.univ.filter (fun i => w.val i ≠ 0)
abbrev stabilizer (w : EvenWord) := MulAction.stabilizer A7 (support w : Set (Fin 7))
abbrev five (w : EvenWord) := fixingSubgroup A7 (support w : Set (Fin 7))

theorem mem_stabilizer (a : A7) (w : EvenWord) :
    a ∈ stabilizer w ↔ evenRepresentation a.val w = w := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff]
  constructor
  · intro h
    apply Subtype.ext
    funext i
    apply (by decide : ∀ x y : ZMod 2, (x ≠ 0 ↔ y ≠ 0) → x = y)
    have hi := h i
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hi
    simp only [support, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    change w.val (a.val.symm i) ≠ 0 ↔ w.val i ≠ 0 at hi
    exact hi
  · intro h i
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have hi := congrArg (fun v : EvenWord => v.val i) h
    change w.val (a.val.symm i) = w.val i at hi
    simp only [support, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    change w.val (a.val.symm i) ≠ 0 ↔ w.val i ≠ 0
    rw [hi]

noncomputable def fiveEquiv (w : EvenWord) (hw : weight w.val = 2) :
    five w ≃* alternatingGroup (Fin 5) :=
  (Atlas.Families.Alternating.stabilizerComplementEquiv (support w)).trans
    (Atlas.Families.Alternating.relabel (Fintype.equivFinOfCardEq (by
      rw [Fintype.card_coe, Finset.card_compl]
      change 7 - weight w.val = 5
      rw [hw])))

theorem five_perfect (w : EvenWord) (hw : weight w.val = 2) : Group.IsPerfect (five w) := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := (fiveEquiv w hw).symm.toMonoidHom)
    (fiveEquiv w hw).symm.surjective

theorem five_le_stabilizer (w : EvenWord) : five w ≤ stabilizer w := by
  intro a ha
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨i,hi,rfl⟩
    have he := ha ⟨i,hi⟩
    change a.val i ∈ (support w : Set (Fin 7))
    change a.val i = i at he
    rw [he]
    exact hi
  · intro i hi
    exact ⟨i,hi,ha ⟨i,hi⟩⟩

theorem residual_stabilizer_eq_five (w : EvenWord) (hw : weight w.val = 2) :
    (solvableResidual (stabilizer w)).map (stabilizer w).subtype = five w := by
  classical
  let F := five w
  let C := stabilizer w
  let f : C →* Equiv.Perm (support w : Set (Fin 7)) := MulAction.toPermHom C _
  have hcard : Nat.card (Equiv.Perm (support w : Set (Fin 7))) = 2 := by
    rw [Nat.card_perm, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    change (weight w.val).factorial = 2
    rw [hw]
    rfl
  let : IsCyclic (Equiv.Perm (support w : Set (Fin 7))) := isCyclic_of_prime_card hcard
  let : Group.IsSolvable (Equiv.Perm (support w : Set (Fin 7))) := inferInstance
  have hker : solvableResidual C ≤ f.ker := by
    have hm := map_solvableResidual_le f
    rw [solvableResidual_eq_bot (G := Equiv.Perm (support w : Set (Fin 7)))] at hm
    exact (map_eq_bot_iff (solvableResidual C)).mp (show (solvableResidual C).map f = ⊥ from bot_unique hm)
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩ i
    have hf : f a = 1 := hker ha
    exact congrArg Subtype.val (DFunLike.congr_fun hf i)
  · let := five_perfect w hw
    exact le_map_solvableResidual_of_isPerfect F C (five_le_stabilizer w)

/-- A fixed word vanishing on the two support letters is zero: otherwise its
weight would be five, which is odd. -/
theorem fixed_eq_zero_of_support_zero (w x : EvenWord) (hw : weight w.val = 2)
    (hz : ∀ i ∈ support w, x.val i = 0)
    (hf : ∀ a ∈ five w, evenRepresentation a.val x = x) : x = 0 := by
  classical
  by_contra hx
  have hx' : x.val ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨i,hi⟩ : ∃ i, x.val i ≠ 0 := Function.ne_iff.mp hx'
  have hiw : i ∈ (support w)ᶜ := Finset.mem_compl.mpr (fun h => hi (hz i h))
  have hc : Nat.card ((support w)ᶜ : Finset (Fin 7)) = 5 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_compl]
    change 7 - weight w.val = 5
    rw [hw]
  let : MulAction.IsPretransitive (alternatingGroup ((support w)ᶜ : Finset (Fin 7)))
      ((support w)ᶜ : Finset (Fin 7)) :=
    alternatingGroup.isPretransitive_of_three_le_card _ (by rw [hc]; decide)
  have hconst (j : Fin 7) (hj : j ∈ (support w)ᶜ) : x.val i = x.val j := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq
      (alternatingGroup ((support w)ᶜ : Finset (Fin 7)))
      (⟨i,hiw⟩ : ((support w)ᶜ : Finset (Fin 7))) ⟨j,hj⟩
    let e := Atlas.Families.Alternating.stabilizerComplementEquiv (support w)
    let a := e.symm g
    have he := Atlas.Families.Alternating.stabilizerComplementEquiv_apply (support w) a ⟨i,hiw⟩
    change ((e a).val ⟨i,hiw⟩).val = a.val.val i at he
    rw [e.apply_symm_apply] at he
    have hgi : (g.val ⟨i,hiw⟩).val = j := congrArg Subtype.val hg
    have ha : a.val.val i = j := he.symm.trans hgi
    have hh := congrArg (fun y : EvenWord => y.val (a.val.val i)) (hf a.val a.property)
    simp only [evenRepresentation_apply,Equiv.symm_apply_apply] at hh
    exact hh.trans (congrArg x.val ha)
  have hs : Finset.univ.filter (fun j => x.val j ≠ 0) = (support w)ᶜ := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
    constructor
    · intro hj hwj
      exact hj (hz j hwj)
    · intro hj
      exact fun hxj => hi ((hconst j (Finset.mem_compl.mpr hj)).trans hxj)
  have hwx : weight x.val = 5 := by
    rw [weight,hs,Finset.card_compl]
    change 7 - weight w.val = 5
    rw [hw]
  have hh := weight_of_mem_evenWords x.property hx'
  omega

end WeightTwoGeometry
end BinarySevenCode
