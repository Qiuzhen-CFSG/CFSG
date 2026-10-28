module

public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.Representation.BinaryNaturalDual.Action
public import Theory.Representation.BinaryNaturalDual.GeneratedCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.SymmetricEight.InvolutionActions

public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Marked degree-four actors and their eight-point comparison

The genuine projective/linear and exceptional PSL₄(2)/A₈ equivalences identify
Aut(GL₄(2)) with S₈. The comparison records the inner embedding and conjugation
on the original natural linear group. Thus odd involutions form exactly the
transposition and triple-transposition classes, with actual representatives.

Three subgroups are defined by generators on the eight points and pulled back
to the automorphism group. Their elementary orders, exhaustive conjugacy
classification, centralizer structures and transvection markings are separate
mathematical obligations; these definitions assert none of those conclusions.
The natural fixed space and generated core use the specified coordinate action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(1,3),
printed pp.391–392, PDF pp.402–403. The exceptional comparison is the attributed
ATLAS port in `Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8`.
-/

@[expose] public section

namespace BinaryNaturalDual.FourActors
open BinaryLinear.OuterCyclic Equiv Subgroup
open Theory.SpecificGroups.SymmetricEight.Involutions
abbrev X := BinaryLinear.OuterCyclic.Space 4
abbrev V := CoordinateSpace 4
abbrev G := LinearGroup 4
abbrev M := MulAut G
abbrev S := Perm (Fin 8)

/-- The exceptional comparison anchored to the usual natural matrix action. -/
noncomputable def linearAlternatingEquiv : G ≃* alternatingGroup (Fin 8) :=
  (projectiveEquivLinear (by decide : 0 < 4)).symm.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
/-- The induced eight-point action of the full automorphism group. -/
noncomputable def permutationEquiv : M ≃* S :=
  automorphismPermutationEquiv linearAlternatingEquiv
abbrev inner : Subgroup M := MulAut.innerSubgroup G

theorem permutationEquiv_inner (g : G) :
    permutationEquiv (MulAut.conj g) = (linearAlternatingEquiv g).val :=
  automorphismPermutationEquiv_inner linearAlternatingEquiv g

theorem permutationEquiv_mem_alternating (a : M) :
    permutationEquiv a ∈ alternatingGroup (Fin 8) ↔ a ∈ inner :=
  automorphismPermutationEquiv_mem_alternating linearAlternatingEquiv a

theorem inner_index : inner.index = 2 := by
  have he : inner = (alternatingGroup (Fin 8)).comap permutationEquiv.toMonoidHom := by
    ext a
    exact (permutationEquiv_mem_alternating a).symm
  rw [he, Subgroup.index_comap_of_surjective _ permutationEquiv.surjective,
    alternatingGroup.index_eq_two]

theorem permutationEquiv_action (a : M) (g : G) :
    (linearAlternatingEquiv (a g)).val =
      permutationEquiv a * (linearAlternatingEquiv g).val * (permutationEquiv a)⁻¹ :=
  automorphismPermutationEquiv_action linearAlternatingEquiv a g

/-- The natural linear group has trivial center over the binary field. -/
theorem center_linear_eq_bot : Subgroup.center G = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have h := ((Subgroup.centerCongr (slEquivLinear 4)).symm ⟨x, hx⟩).property
  change (slEquivLinear 4).symm x ∈ Subgroup.center _ at h
  rw [binary_center_eq_bot (by decide : 0 < 4), Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr ((slEquivLinear 4).symm.map_eq_one_iff.mp h)

/-- The genuine linear group identified with its inner automorphism image. -/
noncomputable def linearInnerEquiv : G ≃* inner :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot center_linear_eq_bot)

/-- Commutation in the ambient automorphism group is the fixed-group condition
on the marked natural linear group. -/
theorem conj_commute_iff_fixed (a : M) (g : G) : Commute (MulAut.conj g) a ↔ a g = g := by
  constructor
  · intro h
    apply MulAut.conj_injective_of_center_eq_bot center_linear_eq_bot
    have he : MulAut.conj (a g) = a * MulAut.conj g * a⁻¹ := by
      ext z : 1
      simp
    rw [he, h.eq.symm, mul_inv_cancel_right]
  · intro hg
    ext z : 1
    change g * a z * g⁻¹ = a (g * z * g⁻¹)
    rw [map_mul, map_mul, map_inv, hg]

/-- The centralizer inside the actual inner subgroup of `M`. -/
def innerCentralizer (a : M) : Subgroup M := inner ⊓ centralizer ({a} : Set M)

/-- The fixed group in the marked natural model and the relative centralizer
inside the inner automorphisms are genuinely isomorphic. -/
noncomputable def fixedInnerEquiv (a : M) : a.fixedSubgroup ≃* innerCentralizer a := by
  let f : a.fixedSubgroup →* innerCentralizer a := {
    toFun g := ⟨MulAut.conj g.val, ⟨⟨g.val, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((conj_commute_iff_fixed a g.val).mpr ((MulAut.mem_fixedSubgroup a g.val).mp g.property)).eq⟩⟩
    map_one' := Subtype.ext (MulAut.conj.map_one)
    map_mul' g h := Subtype.ext (MulAut.conj.map_mul g.val h.val) }
  apply MulEquiv.ofBijective f
  constructor
  · intro g h he
    apply Subtype.ext
    exact MulAut.conj_injective_of_center_eq_bot center_linear_eq_bot (congrArg Subtype.val he)
  · intro b
    obtain ⟨g, hg⟩ := b.property.1
    have hc : Commute (MulAut.conj g) a :=
      Subgroup.mem_centralizer_singleton_iff.mp (hg.symm ▸ b.property.2)
    exact ⟨⟨g, (MulAut.mem_fixedSubgroup a g).mpr ((conj_commute_iff_fixed a g).mp hc)⟩, Subtype.ext hg⟩

noncomputable def transposition : M := permutationEquiv.symm onePair
noncomputable def tripleTransposition : M := permutationEquiv.symm threePairs

@[simp] theorem permutationEquiv_transposition : permutationEquiv transposition = onePair :=
  permutationEquiv.apply_symm_apply _
@[simp] theorem permutationEquiv_tripleTransposition :
    permutationEquiv tripleTransposition = threePairs := permutationEquiv.apply_symm_apply _


@[simp] theorem transposition_order : orderOf transposition = 2 := by
  rw [← permutationEquiv.orderOf_eq, permutationEquiv_transposition]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
@[simp] theorem tripleTransposition_order : orderOf tripleTransposition = 2 := by
  rw [← permutationEquiv.orderOf_eq, permutationEquiv_tripleTransposition]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem transposition_outer : transposition ∉ inner := by
  rw [← permutationEquiv_mem_alternating, permutationEquiv_transposition, Perm.mem_alternatingGroup]
  decide +kernel

theorem tripleTransposition_outer : tripleTransposition ∉ inner := by
  rw [← permutationEquiv_mem_alternating, permutationEquiv_tripleTransposition, Perm.mem_alternatingGroup]
  decide +kernel

theorem outer_involution_cycleType (a : M) (ha : orderOf a = 2) (hout : a ∉ inner) :
    (permutationEquiv a).cycleType = {2} ∨
      (permutationEquiv a).cycleType = {2, 2, 2} := by
  have ho : orderOf (permutationEquiv a) = 2 := (permutationEquiv.orderOf_eq a).trans ha
  have hn : permutationEquiv a ∉ alternatingGroup (Fin 8) :=
    fun h => hout ((permutationEquiv_mem_alternating a).mp h)
  rcases involution_cycleType ho with h | h | h | h
  · exact Or.inl h
  · exfalso
    apply hn
    rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, h]
    decide
  · exact Or.inr h
  · exfalso
    apply hn
    rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, h]
    decide

theorem outer_involution_conjugacy (a : M) (ha : orderOf a = 2) (hout : a ∉ inner) :
    IsConj a transposition ∨ IsConj a tripleTransposition := by
  rcases outer_involution_cycleType a ha hout with h | h
  · left
    have hc : IsConj (permutationEquiv a) onePair :=
      Perm.isConj_iff_cycleType_eq.mpr (h.trans onePair_cycleType.symm)
    simpa [transposition] using permutationEquiv.symm.toMonoidHom.map_isConj hc
  · right
    have hc : IsConj (permutationEquiv a) threePairs :=
      Perm.isConj_iff_cycleType_eq.mpr (h.trans threePairs_cycleType.symm)
    simpa [tripleTransposition] using permutationEquiv.symm.toMonoidHom.map_isConj hc

theorem not_isConj_representatives : ¬ IsConj transposition tripleTransposition := by
  intro h
  have he := Perm.isConj_iff_cycleType_eq.mp (permutationEquiv.toMonoidHom.map_isConj h)
  change (permutationEquiv transposition).cycleType =
    (permutationEquiv tripleTransposition).cycleType at he
  rw [permutationEquiv_transposition, permutationEquiv_tripleTransposition,
    onePair_cycleType, threePairs_cycleType] at he
  have := congrArg Multiset.card he
  simp at this

/-- Independent Klein groups on two four-point blocks. -/
def permutationA0 : Subgroup S := closure
  ({swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
    swap 4 5 * swap 6 7, swap 4 6 * swap 5 7} : Set S)
/-- Independent transpositions on four two-point blocks. -/
def permutationA1 : Subgroup S := closure
  ({swap 0 1, swap 2 3, swap 4 5, swap 6 7} : Set S)
/-- Two transpositions and an independent regular Klein group. -/
def permutationA2 : Subgroup S := closure
  ({swap 0 1, swap 2 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7} : Set S)
/-- The two-Klein-block representative, in the actual automorphism group. -/
noncomputable def A0 : Subgroup M := permutationA0.comap permutationEquiv.toMonoidHom
/-- The four-pair representative, in the actual automorphism group. -/
noncomputable def A1 : Subgroup M := permutationA1.comap permutationEquiv.toMonoidHom
/-- The mixed pair/four-block representative, in the actual automorphism group. -/
noncomputable def A2 : Subgroup M := permutationA2.comap permutationEquiv.toMonoidHom
noncomputable def B1 : Subgroup M := A1 ⊓ inner
noncomputable def B2 : Subgroup M := A2 ⊓ inner
/-- The fixed-point-free permutation involution in the four-pair representative.
Its natural transvection marking is a further theorem, not part of this definition. -/
noncomputable def r : M := permutationEquiv.symm fourPairs

@[simp] theorem permutationEquiv_r : permutationEquiv r = fourPairs :=
  permutationEquiv.apply_symm_apply _

theorem transposition_mem_A1 : transposition ∈ A1 := by
  change permutationEquiv transposition ∈ permutationA1
  rw [permutationEquiv_transposition]
  apply Subgroup.subset_closure
  exact Set.mem_insert _ _

theorem transposition_mem_A2 : transposition ∈ A2 := by
  change permutationEquiv transposition ∈ permutationA2
  rw [permutationEquiv_transposition]
  apply Subgroup.subset_closure
  exact Set.mem_insert _ _

theorem A1_not_le_inner : ¬ A1 ≤ inner :=
  fun h => transposition_outer (h transposition_mem_A1)

theorem A2_not_le_inner : ¬ A2 ≤ inner :=
  fun h => transposition_outer (h transposition_mem_A2)

theorem A0_le_inner : A0 ≤ inner := by
  have he : permutationA0 ≤ alternatingGroup (Fin 8) := by
    apply (Subgroup.closure_le _).mpr
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      apply Perm.mem_alternatingGroup.mpr <;> decide +kernel
  intro a ha
  exact (permutationEquiv_mem_alternating a).mp (he ha)

theorem r_mem_B1 : r ∈ B1 := by
  constructor
  · change permutationEquiv r ∈ permutationA1
    rw [permutationEquiv_r]
    unfold fourPairs
    apply permutationA1.mul_mem
    · apply permutationA1.mul_mem
      · apply permutationA1.mul_mem
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · change r ∈ inner
    rw [← permutationEquiv_mem_alternating, permutationEquiv_r, Perm.mem_alternatingGroup]
    decide +kernel

noncomputable def innerPreimage (A : Subgroup M) : Subgroup G := A.comap (MulAut.conj : G →* M)
noncomputable def actorFixed (d : CoordinateAction 4) (A : Subgroup M) : Submodule (ZMod 2) V :=
  Representation.BinaryOffender.fixedSpace d.representation A
noncomputable def actorCore (d : CoordinateAction 4) (A : Subgroup M) (k : ℕ) :
    Submodule (ZMod 2) V := generatedCore (d.representation.comp A.subtype) k

/-- The marked natural action, before adjoining the dual summand. -/
def naturalRepresentation : Representation (ZMod 2) G X :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

/-- Natural vectors fixed by the actual inner actors in `A`. -/
noncomputable def naturalFixed (A : Subgroup M) : Submodule (ZMod 2) X :=
  Representation.BinaryOffender.fixedSpace naturalRepresentation (innerPreimage A)

@[simp] theorem mem_actorFixed (d : CoordinateAction 4) (A : Subgroup M) (v : V) :
    v ∈ actorFixed d A ↔ ∀ a ∈ A, d.representation a v = v := by
  constructor
  · intro h a ha
    exact h ⟨a, ha⟩
  · intro h a
    exact h a.val a.property

@[simp] theorem mem_naturalFixed (A : Subgroup M) (x : X) :
    x ∈ naturalFixed A ↔ ∀ g : G, MulAut.conj g ∈ A → g x = x := by
  constructor
  · intro h g hg
    exact h ⟨g, hg⟩
  · intro h g
    exact h g.val g.property

theorem naturalFixed_inf_inner (A : Subgroup M) : naturalFixed (A ⊓ inner) = naturalFixed A := by
  ext x
  simp only [mem_naturalFixed, Subgroup.mem_inf]
  constructor
  · intro h g hg
    exact h g ⟨hg, ⟨g, rfl⟩⟩
  · intro h g hg
    exact h g hg.1

end BinaryNaturalDual.FourActors
