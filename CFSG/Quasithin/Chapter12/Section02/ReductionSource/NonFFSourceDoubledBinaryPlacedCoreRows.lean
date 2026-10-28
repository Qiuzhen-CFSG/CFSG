module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedCoreCenter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.BinaryThreeModules.CoreRows
public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.CoreRows

/-!
# Excluding the small-core native rows on the original doubled witnesses

The original selected J₄ component cannot have native residual normalizer
isomorphic to the literal max2 or max4 subgroup. The original Ru component
cannot have normalizer isomorphic to max4 or max6. The same native equivalence
and residual embedding supply these exclusions: the whole orbit forces a
core centre of order at least 64, and the original binary-three quotient forces
a factor seven in the local order.

These applications discharge the named rows only. Coverage of every applicable
maximal two-local remains necessary before the native alternative in
`sourceOrbit_binary_native_oddLocal_obstruction` can be removed.
Source: Aschbacher–Smith 4.4.3, printed pp.622–623 of `refs/quasithin.pdf`.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The J₄ small-core rows are impossible on the original native residual normalizer. -/
theorem sourceOrbit_binary_janko4_core_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Janko4.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      let M := normalizer (r.range : Set Janko4.Model)
      _root_.Group.IsPerfect r.range ∧ 64 ≤ Nat.card (center (pCore 2 M)) ∧
      ¬ Nonempty (M ≃* Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.sourceSubgroup) ∧
      ¬ Nonempty (M ≃* Janko4.LocalStructure.SymmetricLinear.max4Subgroup) := by
  have hg := D.sourceOrbit_binary_oddNormalizer_native_placement
    h hd F hF hmodel A hAC ho hu K hK hcore hr .j4 (Or.inl rfl) e
  obtain ⟨m,hm,hp,_,_,_,hz,_⟩ := D.native_geometry_core_center A K hr e hg
  let r := m.toMonoidHom.comp (inclusion hr)
  let M := normalizer (r.range : Set Janko4.Model)
  exact ⟨m,hm,hp,hz,
    @Janko4.LocalStructure.BinaryThreeModules.not_max2_of_core_center_large M
      inferInstance hz,
    @Janko4.LocalStructure.BinaryThreeModules.not_max4_of_core_center_large M
      inferInstance hz⟩

/-- Both existing Ru rows are excluded using the original marking and full cores. -/
theorem sourceOrbit_binary_rudvalis_core_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Rudvalis.Model) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Rudvalis.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      let M := normalizer (r.range : Set Rudvalis.Model)
      _root_.Group.IsPerfect r.range ∧ 64 ≤ Nat.card (center (pCore 2 M)) ∧
      ¬ Nonempty (M ≃* Rudvalis.SylowOvergroups.max4) ∧
      ¬ Nonempty (M ≃* Rudvalis.SylowOvergroups.max6) := by
  have hg := D.sourceOrbit_binary_oddNormalizer_native_placement
    h hd F hF hmodel A hAC ho hu K hK hcore hr .ru (Or.inr rfl) e
  obtain ⟨m,hm,hp,_,_,_,hz,eR,_,_⟩ := D.native_geometry_core_center A K hr e hg
  let r := m.toMonoidHom.comp (inclusion hr)
  let M := normalizer (r.range : Set Rudvalis.Model)
  let rM : oddActorResidual L A →* M :=
    r.codRestrict M (fun x => r.range.le_normalizer ⟨x,rfl⟩)
  have hi : Function.Injective rM := by
    intro x y hxy
    exact (m.injective.comp (inclusion_injective hr)) (congrArg Subtype.val hxy)
  exact ⟨m,hm,hp,hz,Rudvalis.BinaryThreeModules.not_max4_of_core_center_large hz,
    Rudvalis.BinaryThreeModules.not_max6_of_marked_residual rM hi eR⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
