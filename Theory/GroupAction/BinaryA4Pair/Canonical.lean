module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Mathlib.Tactic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# A canonical pair of binary A₄ subgroups generates A₆

The displayed fixed-free A₄ and the displayed A₄ fixing one nonzero vector
share their marked involution. An explicit binary basis change intertwines
their three generators with the faithful six-letter polar representation.
Forty short words give all three-cycles, proving that the generated group is
the actual alternating group on six letters.

This is the representative calculation for the automizer identification in
Aschbacher–Smith, *The Classification of Quasithin Groups*, 14.3.19(4).
The companion normal-form theorem transports arbitrary marked pairs to this
representative; the source hypotheses remain with their original consumers.
-/

open Theory.SpecificGroups.SymmetricSix
open Subgroup
@[expose] public section
namespace BinaryA4Pair
set_option maxRecDepth 4096
abbrev V := Fin 4 → Multiplicative (ZMod 2)
abbrev Aut := MulAut V

def reflectionAut : Aut where
  toFun v := ![v 0*v 2,v 1*v 3,v 2,v 3]
  invFun v := ![v 0*v 2,v 1*v 3,v 2,v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

def cubicAut : Aut where
  toFun v := ![v 1,v 0*v 1,v 2*v 3,v 2]
  invFun v := ![v 0*v 1,v 0,v 3,v 2*v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

def pointCubicAut : Aut where
  toFun v := ![v 3,v 1*v 3,v 2,v 0*v 3]
  invFun v := ![v 0*v 3,v 0*v 1,v 2,v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

def toPolar : V ≃* Multiplicative NaturalModule where
  toFun v := Multiplicative.ofAdd (Sum.elim
    ![(v 0).toAdd+(v 3).toAdd,(v 1).toAdd]
    ![(v 2).toAdd+(v 3).toAdd,(v 2).toAdd])
  invFun v := ![Multiplicative.ofAdd (v.toAdd (.inl 0)+v.toAdd (.inr 0)+v.toAdd (.inr 1)),
    Multiplicative.ofAdd (v.toAdd (.inl 1)), Multiplicative.ofAdd (v.toAdd (.inr 1)),
    Multiplicative.ofAdd (v.toAdd (.inr 0)+v.toAdd (.inr 1))]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

noncomputable def polarAut : S6 →* MulAut (Multiplicative NaturalModule) where
  toFun g :=
    { toFun v := Multiplicative.ofAdd (polarAction g v.toAdd)
      invFun v := Multiplicative.ofAdd (polarAction g⁻¹ v.toAdd)
      left_inv v := by
        change Multiplicative.ofAdd (polarAction g⁻¹ (polarAction g v.toAdd)) = v
        rw [← polarAction_mul, inv_mul_cancel, polarAction_one]
        rfl
      right_inv v := by
        change Multiplicative.ofAdd (polarAction g (polarAction g⁻¹ v.toAdd)) = v
        rw [← polarAction_mul, mul_inv_cancel, polarAction_one]
        rfl
      map_mul' v w := congrArg Multiplicative.ofAdd (polarAction_add g v.toAdd w.toAdd) }
  map_one' := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd (polarAction_one v.toAdd)
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd (polarAction_mul g h v.toAdd)

noncomputable def modelAction : S6 →* Aut :=
  (MulAut.congr toPolar.symm).toMonoidHom.comp polarAut

theorem polarAut_injective : Function.Injective polarAut := by
  intro g h he
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Duad)
  intro d
  apply polarVector_injective
  apply Subtype.ext
  have hv := congrArg (fun f : MulAut (Multiplicative NaturalModule) =>
    (f (Multiplicative.ofAdd (polarVector d).val)).toAdd) he
  change polarAction g (polarVector d).val = polarAction h (polarVector d).val at hv
  simpa only [polarAction_vector] using hv

theorem modelAction_injective : Function.Injective modelAction :=
  (MulAut.congr toPolar.symm).injective.comp polarAut_injective

def generator : Fin 3 → S6 := ![
  Equiv.swap 1 4 * Equiv.swap 3 5,
  (Equiv.swap 0 1 * Equiv.swap 1 5) * (Equiv.swap 2 4 * Equiv.swap 4 3),
  Equiv.swap 1 5 * Equiv.swap 5 4]
def binaryGenerator : Fin 3 → Aut := ![reflectionAut,cubicAut,pointCubicAut]
def permutedDuad : Fin 3 → Duad → Duad := ![
![3,1,4,0,2,10,14,7,12,11,5,9,8,13,6],
![8,7,5,6,0,14,11,13,4,10,12,3,9,1,2],
![4,1,2,0,3,11,13,8,14,9,5,10,6,12,7]]

theorem generator_smul (k : Fin 3) (d : Duad) : generator k • d = permutedDuad k d := by
  apply duadSet_injective
  rw [duadSet_smul]
  exact (show ∀ (k : Fin 3) (d : Duad),
    (duadSet d).image (generator k) = duadSet (permutedDuad k d) from by decide +kernel) k d

theorem binary_on_duad : ∀ (k : Fin 3) (d : Duad),
    toPolar (binaryGenerator k (toPolar.symm (Multiplicative.ofAdd (polarVector d).val))) =
      Multiplicative.ofAdd (polarVector (permutedDuad k d)).val := by decide +kernel

theorem modelAction_generator (k : Fin 3) : modelAction (generator k) = binaryGenerator k := by
  apply MulEquiv.ext
  intro v
  apply toPolar.injective
  change toPolar (toPolar.symm (polarAut (generator k) (toPolar v))) = _
  rw [toPolar.apply_symm_apply]
  by_cases hv : v = 1
  · subst v
    simp only [map_one]
  · have hn : (toPolar v).toAdd ≠ 0 := by
      intro h
      apply hv
      apply toPolar.injective
      exact h.trans toPolar.map_one.symm
    obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨(toPolar v).toAdd, hn⟩
    have hd' : Multiplicative.ofAdd (polarVector d).val = toPolar v := congrArg
      (fun x : BinaryPoint => Multiplicative.ofAdd x.val) hd
    have h := binary_on_duad k d
    rw [hd', toPolar.symm_apply_apply] at h
    rw [h, ← hd']
    change Multiplicative.ofAdd (polarAction (generator k) (polarVector d).val) = _
    rw [polarAction_vector,generator_smul]

def threeWords : Fin 40 → List (Fin 3) := ![
[2],
[2, 0],
[0, 2],
[2, 2],
[0, 2, 0],
[2, 2, 0],
[2, 0, 2],
[0, 2, 2],
[1, 2, 1, 1],
[1, 1, 2, 1],
[1, 1, 2, 0, 1],
[1, 2, 0, 1, 1],
[1, 0, 2, 1, 1],
[1, 2, 2, 1, 1],
[1, 1, 0, 2, 1],
[1, 1, 2, 2, 1],
[1, 0, 1, 2, 1, 0],
[2, 0, 1, 2, 1, 0],
[0, 1, 1, 2, 1, 0],
[1, 2, 1, 0, 2, 0],
[1, 2, 1, 1, 2, 0],
[1, 2, 1, 2, 2, 0],
[0, 1, 2, 1, 0, 1],
[1, 1, 0, 2, 0, 1],
[2, 1, 0, 2, 0, 1],
[1, 0, 2, 0, 1, 1],
[1, 2, 0, 2, 1, 1],
[2, 0, 1, 2, 1, 1],
[1, 0, 2, 2, 1, 1],
[1, 2, 0, 1, 2, 1],
[2, 2, 0, 1, 2, 1],
[1, 1, 0, 2, 2, 1],
[1, 1, 2, 0, 1, 2],
[0, 1, 2, 1, 1, 2],
[1, 2, 1, 0, 2, 1, 0],
[2, 1, 0, 1, 2, 1, 0],
[2, 2, 1, 2, 1, 2, 0],
[2, 1, 0, 2, 1, 0, 1],
[2, 2, 0, 1, 2, 1, 1],
[0, 1, 2, 1, 1, 2, 1]]

theorem threeCycles_words : ∀ p : S6, p.support.card = 3 →
    ∃ k : Fin 40, ((threeWords k).map generator).prod = p := by decide +kernel

theorem generator_even : ∀ k : Fin 3, generator k ∈ alternatingGroup (Fin 6) := by
  decide +kernel

theorem closure_generator : closure (Set.range generator) = alternatingGroup (Fin 6) := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨k,rfl⟩
    exact generator_even k
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating,closure_le]
    intro p hp
    obtain ⟨k,rfl⟩ := threeCycles_words p hp.card_support
    apply list_prod_mem
    intro x hx
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
    exact subset_closure ⟨k,rfl⟩

theorem modelAction_range :
    (alternatingGroup (Fin 6)).map modelAction = closure (Set.range binaryGenerator) := by
  rw [← closure_generator,MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_,⟨k,rfl⟩,rfl⟩
    exact ⟨k,(modelAction_generator k).symm⟩
  · rintro ⟨k,rfl⟩
    exact ⟨generator k,⟨k,rfl⟩,modelAction_generator k⟩
theorem canonical_recognition :
    Nonempty (closure (Set.range binaryGenerator) ≃* alternatingGroup (Fin 6)) := by
  exact ⟨((alternatingGroup (Fin 6)).equivMapOfInjective modelAction
    modelAction_injective).trans (MulEquiv.subgroupCongr modelAction_range) |>.symm⟩

/-- Coordinates identify the actual actor with the canonical binary A₆ action. -/
def HasCanonicalModel {W : Type*} [Group W] (P : Subgroup (MulAut W)) : Prop :=
  ∃ e : W ≃* V, P.map (MulAut.congr e).toMonoidHom = closure (Set.range binaryGenerator)

/-- Forgetting the coordinates recovers abstract group recognition. -/
theorem HasCanonicalModel.recognition {W : Type*} [Group W]
    {P : Subgroup (MulAut W)} (h : HasCanonicalModel P) :
    Nonempty (P ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e,he⟩ := h
  obtain ⟨f⟩ := canonical_recognition
  exact ⟨((P.equivMapOfInjective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective).trans (MulEquiv.subgroupCongr he)).trans f⟩
end BinaryA4Pair
