module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedCoreRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.BinaryThreeModules.MathieuRow

/-!
# Inspected native rows in every containing two-local

The original native geometry makes the same residual and whole doubled orbit
normal in every two-local containing that residual. Applying the normal-core
commutant argument inside each such local places the order-64 orbit in the
centre of its full two-core. All maps and the natural-dual action marking
come from that one native equivalence.

For J₄, relative residual normality also excludes the literal Mathieu max1
row via its genuine M₂₄ quotient. The core-centre bounds exclude max2 and
max4. For Ru, the core-centre and factor-seven arguments exclude max4 and
max6. These statements concern every containing two-local, so subsequent
coverage may supply containment without proving equality with the residual
normalizer. The original chosen-module applications retain the selected
component, original quotient projection and native marking.

Source: the final inspection in Aschbacher–Smith 4.4.3, printed pp.622–623
of `refs/quasithin.pdf`. Specialized coverage and the remaining rows are
still required to eliminate `BinaryPlacedNativeCase`; these results do not
remove the native disjunct or the separate maximal pushing-up alternative.
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

/-- The same marked orbit forces a large core centre in every containing two-local. -/
theorem native_geometry_containing_core_centers
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    {Q : Type*} [_root_.Group Q]
    (e : (K ⧸ center K) ≃* Q) (hg : D.BinaryPlacedNativeGeometry A K hr e) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Q,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      _root_.Group.IsPerfect r.range ∧
      ∃ hWK : D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype,
      let w := m.toMonoidHom.comp (inclusion hWK)
      Nat.card w.range = 64 ∧
      ∃ eR : (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) ≃*
        BinaryLinearThree.Group,
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ x v, r x * w (E.symm v).toMul * (r x)⁻¹ =
          w (E.symm (NaturalDual.action (eR (QuotientGroup.mk' _ x)) v)).toMul) ∧
        ∀ B : Subgroup Q, IsTwoLocal B → r.range ≤ B →
          (r.range.subgroupOf B).Normal ∧ w.range ≤ B ∧
          (w.range.subgroupOf B).Normal ∧
          w.range ≤ (center (B.pCoreIn 2)).map (B.pCoreIn 2).subtype ∧
          64 ≤ Nat.card (center (pCore 2 B)) := by
  let : Finite Q := Finite.of_surjective e e.surjective
  obtain ⟨_,_,m,hm,_,_,hWK,hcard,_,_,_,_,hnormal,
    _,_,_,eR,E,ha,_,_⟩ := hg
  let r := m.toMonoidHom.comp (inclusion hr)
  let w := m.toMonoidHom.comp (inclusion hWK)
  have hir : Function.Injective r := m.injective.comp (inclusion_injective hr)
  have hiw : Function.Injective w := m.injective.comp (inclusion_injective hWK)
  let : _root_.Group.IsPerfect (oddActorResidual L A) := oddActorResidual_isPerfect L A
  have hp : _root_.Group.IsPerfect r.range :=
    _root_.Group.IsPerfect.ofSurjective r.rangeRestrict_surjective
  refine ⟨m,hm,hp,hWK,hcard,eR,E,ha,?_⟩
  intro B hB hRB
  have hn := hnormal B hB hRB
  have hz := NaturalDual.mapped_module_in_core_center B r w hir hiw hRB hn.2.1
    ((normal_subgroupOf_iff_le_normalizer hRB).mp hn.1)
    ((normal_subgroupOf_iff_le_normalizer hn.2.1).mp hn.2.2) eR E ha
  exact ⟨hn.1,hn.2.1,hn.2.2,hz.1,hcard ▸ hz.2⟩

/-- The J₄ max1, max2 and max4 rows cannot even contain the native residual. -/
theorem native_geometry_janko4_containing_rows
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Janko4.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      ∀ B : Subgroup Janko4.Model, IsTwoLocal B → r.range ≤ B →
        64 ≤ Nat.card (center (pCore 2 B)) ∧
        ¬ Nonempty (B ≃* Janko4.Cardinality.max1Subgroup
          Janko4.matrixA_mul_self Janko4.matrixB_pow_four) ∧
        ¬ Nonempty (B ≃* Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.sourceSubgroup) ∧
        ¬ Nonempty (B ≃* Janko4.LocalStructure.SymmetricLinear.max4Subgroup) := by
  obtain ⟨m,hm,_,_,_,eR,_,_,hB⟩ := D.native_geometry_containing_core_centers A K hr e hg
  let r := m.toMonoidHom.comp (inclusion hr)
  refine ⟨m,hm,?_⟩
  dsimp only
  intro B hlocal hRB
  obtain ⟨hn,_,_,_,hz⟩ := hB B hlocal hRB
  let rB : oddActorResidual L A →* B := r.codRestrict B (fun x => hRB ⟨x,rfl⟩)
  have hi : Function.Injective rB := by
    intro x y hxy
    exact (m.injective.comp (inclusion_injective hr)) (congrArg Subtype.val hxy)
  have heq : rB.range = r.range.subgroupOf B := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,rfl⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  have hnB : rB.range.Normal := heq.symm ▸ hn
  exact ⟨hz,
    @Janko4.LocalStructure.BinaryThreeModules.not_max1_of_normal_marked_residual B
      (oddActorResidual L A) inferInstance inferInstance inferInstance rB hi hnB eR,
    @Janko4.LocalStructure.BinaryThreeModules.not_max2_of_core_center_large B inferInstance hz,
    @Janko4.LocalStructure.BinaryThreeModules.not_max4_of_core_center_large B inferInstance hz⟩

/-- Both Ru core rows are excluded in every containing two-local, using the same marking. -/
theorem native_geometry_rudvalis_containing_rows
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Rudvalis.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Rudvalis.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      ∀ B : Subgroup Rudvalis.Model, IsTwoLocal B → r.range ≤ B →
        64 ≤ Nat.card (center (pCore 2 B)) ∧
        ¬ Nonempty (B ≃* Rudvalis.SylowOvergroups.max4) ∧
        ¬ Nonempty (B ≃* Rudvalis.SylowOvergroups.max6) := by
  obtain ⟨m,hm,_,_,_,eR,_,_,hB⟩ := D.native_geometry_containing_core_centers A K hr e hg
  let r := m.toMonoidHom.comp (inclusion hr)
  refine ⟨m,hm,?_⟩
  dsimp only
  intro B hlocal hRB
  obtain ⟨_,_,_,_,hz⟩ := hB B hlocal hRB
  let rB : oddActorResidual L A →* B := r.codRestrict B (fun x => hRB ⟨x,rfl⟩)
  have hi : Function.Injective rB := by
    intro x y hxy
    exact (m.injective.comp (inclusion_injective hr)) (congrArg Subtype.val hxy)
  exact ⟨hz,Rudvalis.BinaryThreeModules.not_max4_of_core_center_large hz,
    Rudvalis.BinaryThreeModules.not_max6_of_marked_residual rB hi eR⟩

/-- Original chosen-module inputs exclude the inspected J₄ rows in every
containing two-local, with the selected component and native marking retained. -/
theorem sourceOrbit_binary_janko4_containing_rows
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
      ∀ B : Subgroup Janko4.Model, IsTwoLocal B → r.range ≤ B →
        64 ≤ Nat.card (center (pCore 2 B)) ∧
        ¬ Nonempty (B ≃* Janko4.Cardinality.max1Subgroup
          Janko4.matrixA_mul_self Janko4.matrixB_pow_four) ∧
        ¬ Nonempty (B ≃* Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.sourceSubgroup) ∧
        ¬ Nonempty (B ≃* Janko4.LocalStructure.SymmetricLinear.max4Subgroup) := by
  exact D.native_geometry_janko4_containing_rows A K hr e
    (D.sourceOrbit_binary_oddNormalizer_native_placement
      h hd F hF hmodel A hAC ho hu K hK hcore hr .j4 (Or.inl rfl) e)

/-- Original chosen-module inputs exclude the inspected Ru rows in every
containing two-local, with the selected component and native marking retained. -/
theorem sourceOrbit_binary_rudvalis_containing_rows
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
      ∀ B : Subgroup Rudvalis.Model, IsTwoLocal B → r.range ≤ B →
        64 ≤ Nat.card (center (pCore 2 B)) ∧
        ¬ Nonempty (B ≃* Rudvalis.SylowOvergroups.max4) ∧
        ¬ Nonempty (B ≃* Rudvalis.SylowOvergroups.max6) := by
  exact D.native_geometry_rudvalis_containing_rows A K hr e
    (D.sourceOrbit_binary_oddNormalizer_native_placement
      h hd F hF hmodel A hAC ho hu K hK hcore hr .ru (Or.inr rfl) e)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
