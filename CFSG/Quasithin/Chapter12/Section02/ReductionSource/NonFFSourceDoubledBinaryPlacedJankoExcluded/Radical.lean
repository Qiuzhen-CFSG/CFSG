module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedCoreCenter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.Reductions

/-!
# The radical supplied by the original binary doubled J₄ geometry

Use the existing whole-module core-center bound on the same native map. Its
maximal two-local is the full normalizer of its ambient two-core, which is
therefore radical. The original normal residual and its SL₃(2) quotient marking
transfer through the same injective residual map and literal relative subgroup.

Source: the J₄ inspection in Aschbacher--Smith 4.4.3, pp.622--623, and the
radical strategy in An--O'Brien--Wilson (2003), Section 4, p.122. This constructs
the inputs for the native radical exclusion; it does not exclude the J₄ case.
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

/-- The same native geometry supplies a large-center radical, its whole
normalizer and the actual normal binary-three residual quotient. -/
theorem native_janko_geometry_radical
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Janko4.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      let M := normalizer (r.range : Set Janko4.Model)
      let P := M.pCoreIn 2
      IsPRadical 2 P ∧ normalizer (P : Set Janko4.Model) = M ∧
        64 ≤ Nat.card (center P) ∧
        (r.range.subgroupOf M).Normal ∧
        Nonempty (((r.range.subgroupOf M) ⧸ pCore 2 (r.range.subgroupOf M)) ≃*
          BinaryLinearThree.Group) := by
  obtain ⟨m,hm,_,hWK,_,_,hz,eR,E,ha⟩ := D.native_geometry_core_center A K hr e hg
  obtain ⟨_,_,m',hm',hu,_,_,_,_,_,_,_,hnormal,_⟩ := hg
  have hmeq : m' = m := by
    ext x
    exact (hm' x).trans (hm x).symm
  subst m'
  let r := m.toMonoidHom.comp (inclusion hr)
  let M := normalizer (r.range : Set Janko4.Model)
  have hn := (hnormal M hu.1.1 r.range.le_normalizer).1
  obtain ⟨hP,hN,hlarge⟩ :=
    Janko4.LocalStructure.LargeCenterRadicals.maximal_local_core_radical M hu.1 hz
  have hir : Function.Injective r := m.injective.comp (inclusion_injective hr)
  let b : r.range.subgroupOf M ≃* oddActorResidual L A :=
    (subgroupOfEquivOfLe r.range.le_normalizer).trans (MonoidHom.ofInjective hir).symm
  have hbcore : (pCore 2 (r.range.subgroupOf M)).map b.toMonoidHom =
      pCore 2 (oddActorResidual L A) :=
    @pCore_map_iso (r.range.subgroupOf M) (oddActorResidual L A)
      inferInstance inferInstance 2 b
  let bq := QuotientGroup.congr (pCore 2 (r.range.subgroupOf M))
    (pCore 2 (oddActorResidual L A)) b hbcore
  exact ⟨m,hm,hP,hN,hlarge,hn,⟨bq.trans eR⟩⟩

/-- The original chosen-module inputs discharge every premise of the radical
construction, retaining the chosen component and its quotient equivalence. -/
theorem sourceOrbit_binary_oddNormalizer_janko_radical
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
      let P := M.pCoreIn 2
      IsPRadical 2 P ∧ normalizer (P : Set Janko4.Model) = M ∧
        64 ≤ Nat.card (center P) ∧
        (r.range.subgroupOf M).Normal ∧
        Nonempty (((r.range.subgroupOf M) ⧸ pCore 2 (r.range.subgroupOf M)) ≃*
          BinaryLinearThree.Group) := by
  apply D.native_janko_geometry_radical A K hr e
  exact D.sourceOrbit_binary_oddNormalizer_native_placement h hd F hF hmodel A hAC ho hu
    K hK hcore hr .j4 (Or.inl rfl) e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
