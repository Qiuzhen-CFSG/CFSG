module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedNative
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore
public import Theory.Representation.PSL3Two.NaturalDualNormalCore

/-!
# The full normalizer core centralizes the original native doubled orbit

Transport perfectness through the same injective native residual map. Relative
normality and the original quotient-action marking then make the normalizer's
full two-core centralize the whole orbit. Since that orbit is a normal two-group
of order 64, the core centre has at least 64 elements. The output keeps the
original native equivalence, residual map, orbit map and linear marking.

This supplies the core-centre obstruction for the J₄/Ru inspection at the end
of Aschbacher–Smith 4.4.3, printed pp.622–623. It does not classify maximal
locals or eliminate the independent maximal pushing-up alternative.
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

/-- The existing native geometry forces a large centre in the full normalizer core,
using exactly its native, residual, orbit, quotient and linear maps. -/
theorem native_geometry_core_center
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
        let M := normalizer (r.range : Set Q)
        w.range ≤ (center (M.pCoreIn 2)).map (M.pCoreIn 2).subtype ∧
        Nat.card w.range = 64 ∧ 64 ≤ Nat.card (center (pCore 2 M)) ∧
        ∃ eR : (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) ≃*
            BinaryLinearThree.Group,
        ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
          ∀ x v, r x * w (E.symm v).toMul * (r x)⁻¹ =
            w (E.symm (NaturalDual.action (eR (QuotientGroup.mk' _ x)) v)).toMul := by
  let : Finite Q := Finite.of_surjective e e.surjective
  obtain ⟨_,_,m,hm,hu,_,hWK,hcard,_,_,_,_,hnormal,
    _,_,_,eR,E,ha,_,_⟩ := hg
  let r := m.toMonoidHom.comp (inclusion hr)
  let w := m.toMonoidHom.comp (inclusion hWK)
  let M := normalizer (r.range : Set Q)
  have hir : Function.Injective r := m.injective.comp (inclusion_injective hr)
  have hiw : Function.Injective w := m.injective.comp (inclusion_injective hWK)
  have hn := hnormal M hu.1.1 r.range.le_normalizer
  have hnW : M ≤ normalizer (w.range : Set Q) :=
    (normal_subgroupOf_iff_le_normalizer hn.2.1).mp hn.2.2
  have hz := NaturalDual.mapped_module_in_core_center M r w hir hiw
    r.range.le_normalizer hn.2.1 le_rfl hnW eR E ha
  let : _root_.Group.IsPerfect (oddActorResidual L A) := oddActorResidual_isPerfect L A
  have hp : _root_.Group.IsPerfect r.range :=
    _root_.Group.IsPerfect.ofSurjective r.rangeRestrict_surjective
  exact ⟨m,hm,hp,hWK,hz.1,hcard,hcard ▸ hz.2,eR,E,ha⟩

/-- Original chosen-module inputs supply the native core-centre obstruction,
on the very component and marking selected by the odd-local reduction. -/
theorem sourceOrbit_binary_oddNormalizer_native_core_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (name : ClassificationModels.SporadicName) (hn : name = .j4 ∨ name = .ru)
    (e : (K ⧸ center K) ≃* name.Carrier) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* name.Carrier,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      _root_.Group.IsPerfect r.range ∧
      64 ≤ Nat.card (center (pCore 2 (normalizer (r.range : Set name.Carrier)))) := by
  have hg := D.sourceOrbit_binary_oddNormalizer_native_placement
    h hd F hF hmodel A hAC ho hu K hK hcore hr name hn e
  obtain ⟨m,hm,hp,_,_,_,hz,_⟩ := D.native_geometry_core_center A K hr e hg
  exact ⟨m,hm,hp,hz⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
