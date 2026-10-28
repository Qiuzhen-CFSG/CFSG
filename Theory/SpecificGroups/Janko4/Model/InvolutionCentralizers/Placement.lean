module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.Reduction
public import Theory.GroupTheory.EvenCentralizerFixedInvolution
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
/-!
# Involution-centralizer placement preserving a normalizer Sylow

The two certified involution centralizers of the actual J₄ matrix model have
self-centralizing normal two-subgroups. Actual involution fusion transports
this characteristic-two property to every involution centralizer. If a marked
subgroup has even centralizer, a Sylow two-subgroup of its normalizer fixes an
involution there. Thus both the subgroup and that same Sylow actor lie in a
characteristic-two overgroup, with an explicit equivalence to one of the two
native centralizers.

Source application: Aschbacher--Smith 2.4.25, printed p.543. The evenness input
comes from the opposite source block; the local-component obstruction in the
selected centralizer is separate. No full ambient Sylow bound is asserted.
-/
public section
namespace Janko4.InvolutionCentralizers
open Subgroup Theory.GroupTheory
attribute [local irreducible] modelGroup matrixA matrixB

theorem first_characteristic_two :
    centralizer (pCore 2 First.centralizer : Set First.centralizer) ≤
      pCore 2 First.centralizer :=
  (@Theory.Quasithin.centralizer_pCore_le_iff First.centralizer
    OuterReduction.FixedGenerator.NormalizerSquares.involutionCentralizer
    inferInstance inferInstance 2 First.centralizerEquiv).mpr
    OuterReduction.FixedGenerator.NormalizerSquares.localTwoCoreCentralizerControl.1

theorem second_characteristic_two :
    centralizer (pCore 2 Second.ambientCentralizer : Set Second.ambientCentralizer) ≤
      pCore 2 Second.ambientCentralizer := by
  let := Second.ambientKernel_elementary
  have hp : IsPGroup 2 Second.ambientKernel := IsElementaryAbelian.isPGroup 2 _
  have hle : Second.ambientKernel ≤ pCore 2 Second.ambientCentralizer :=
    le_sSup ⟨inferInstance, hp⟩
  exact (centralizer_le hle).trans (Second.ambientKernel_selfCentralizing.le.trans hle)

private theorem seed_isConj_second : IsConj (Second.seed : Model) ((a * b * a * b * b) ^ 5) := by
  obtain ⟨g, hg⟩ := Simplicity.Max1Fusion.seed_fuses_second matrixA_mul_self matrixB_pow_four
  have ha : Simplicity.a matrixA_mul_self = a := by apply toMatrix_injective; rfl
  have hb : Simplicity.b matrixB_pow_four = b := by apply toMatrix_injective; rfl
  rw [ha, hb] at hg
  have hw : Simplicity.word a b "ababb" = a * b * a * b * b := by
    simp [Simplicity.word, mul_assoc]
  rw [hw] at hg
  exact isConj_iff.mpr ⟨g, hg.symm⟩

private theorem centralizer_equiv_of_isConj {x y : Model} (h : IsConj x y) :
    Nonempty (centralizer ({x} : Set Model) ≃* centralizer ({y} : Set Model)) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  have he : (centralizer ({x} : Set Model)).map e.toMonoidHom =
      centralizer ({y} : Set Model) := by
    rw [map_centralizer_equiv, Set.image_singleton]
    exact congrArg (fun z => centralizer ({z} : Set Model)) hg
  exact ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr he)⟩

theorem centralizer_equiv_first_or_second (z : Model) (hz : orderOf z = 2) :
    Nonempty (centralizer ({z} : Set Model) ≃* First.centralizer) ∨
    Nonempty (centralizer ({z} : Set Model) ≃* Second.ambientCentralizer) := by
  rcases OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hz with h | h
  · exact Or.inl (centralizer_equiv_of_isConj h.symm)
  · exact Or.inr (centralizer_equiv_of_isConj (seed_isConj_second.trans h).symm)

theorem centralizer_characteristic_two (z : Model) (hz : orderOf z = 2) :
    centralizer (pCore 2 (centralizer ({z} : Set Model)) :
      Set (centralizer ({z} : Set Model))) ≤ pCore 2 (centralizer ({z} : Set Model)) := by
  rcases centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr first_characteristic_two
  · obtain ⟨e⟩ := h
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr second_characteristic_two

/-- Preserve the marked block and its actual normalizer Sylow when choosing
an involution centralizer. Evenness is supplied by the opposite source block. -/
theorem even_centralizer_normalizer_sylow_placement
    (A : Subgroup Model) (P : Sylow 2 (normalizer (A : Set Model)))
    (heven : 2 ∣ Nat.card (centralizer (A : Set Model))) :
    ∃ z : Model, orderOf z = 2 ∧
      A ≤ centralizer ({z} : Set Model) ∧
      (P : Subgroup (normalizer (A : Set Model))).map
        (normalizer (A : Set Model)).subtype ≤ centralizer ({z} : Set Model) ∧
      centralizer (pCore 2 (centralizer ({z} : Set Model)) :
        Set (centralizer ({z} : Set Model))) ≤ pCore 2 (centralizer ({z} : Set Model)) ∧
      (Nonempty (centralizer ({z} : Set Model) ≃* First.centralizer) ∨
        Nonempty (centralizer ({z} : Set Model) ≃* Second.ambientCentralizer)) := by
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizer_sylow A P heven
  exact ⟨z,hz,le_sup_left.trans h,le_sup_right.trans h,
    centralizer_characteristic_two z hz,centralizer_equiv_first_or_second z hz⟩
end Janko4.InvolutionCentralizers
