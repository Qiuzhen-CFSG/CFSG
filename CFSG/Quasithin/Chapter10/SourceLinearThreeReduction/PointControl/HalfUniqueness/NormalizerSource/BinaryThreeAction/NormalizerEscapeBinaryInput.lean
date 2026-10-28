module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeMS
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin

/-!
# Binary MS input on the original component and half-Sylow

The original component has self-centralizing two-core. Adjoining its actual
normalizing half-Sylow preserves characteristic two. Together with the
proved original Sylow and characteristic-subgroup conditions, this constructs
the literal binary MS input on L T₁ and preserves the chosen quotient marking.

Neither a model for the whole commutator core nor a critical distance is
asserted. Those are subsequent source duties of the binary MS analysis.
Source: Aschbacher--Smith 10.2.5 and C.1.31, pp.747--748 and135.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

private theorem uniquenessBinary : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The actual component product has characteristic two, with its full core. -/
theorem halfSylow_join_fitting :
    generalizedFitting (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)) : Subgroup G) =
      pCore 2 (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)) : Subgroup G) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply centralizer_pCore_sup_le 2 L _ ?_ (T.isPGroup'.to_le inf_le_left) inf_le_right
  simpa only [(uniquenessBinary D).generalizedFitting_eq_pCore] using
    (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := L))

/-- All binary MS fields hold on the original L and T₁ under the actual
normalizer escape. The quotient equivalence is transported by inclusion. -/
def normalizerEscapeBinaryInput
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := L ⊔ R
  have hJM : J ≤ D.maximalLocal := sup_le
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer)
    (inf_le_left.trans (le_normalizer_componentOrbit L T))
  have hs : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJM)).mp
      ((D.simpleQTKE.twoLocal_sqtk (uniquenessBinary D).normalizer_maximal.1).subgroup
        (J.subgroupOf D.maximalLocal))
  have hc : (L.subgroupOf J).IsCComponent :=
    D.maximal.1.1.subgroupOf_of_le le_sup_left
      (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  let : (L.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le L.le_normalizer inf_le_right)
  have hsup : L.subgroupOf J ⊔ R.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ J from le_sup_left) (show R ≤ J from le_sup_right),
      subgroupOf_self]
  let a : L.subgroupOf J ≃* L := subgroupOfEquivOfLe le_sup_left
  refine ⟨hs,halfSylow_join_fitting D,?_,hc,
    halfSylow_msOddIndexRadical D hn,
    halfSylow_msCharacteristic_of_normalizer_escape D hn hout,
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e⟩
  intro j
  exact mem_sup_of_normal_left.mp (hsup.symm ▸ mem_top j)

/-- The supplied quotient marking evaluates on the same original element
of L; no arbitrary isomorphism replaces the original quotient map. -/
theorem normalizerEscapeBinaryInput_quotient_mk
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (x : L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))) :
    (normalizerEscapeBinaryInput D hn hout e).quotientEquiv
      (QuotientGroup.mk' _ x) =
        e (QuotientGroup.mk' (pCore 2 L) ⟨(x : G),x.property⟩) := by
  rfl

/-- The full binary MS commutator core maps to the original intrinsic
commutator core of L, through the actual subgroup inclusions. -/
theorem normalizerEscape_commutatorCore_map
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    (ChapterC.BinaryMS.commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype =
      (⁅pCore 2 L,(⊤ : Subgroup L)⁆).map L.subtype := by
  let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
  let A := L.subgroupOf J
  let a : A ≃* L := subgroupOfEquivOfLe le_sup_left
  have he : ((⁅pCore 2 A,(⊤ : Subgroup A)⁆).map A.subtype).map J.subtype =
      ((⁅pCore 2 A,(⊤ : Subgroup A)⁆).map a.toMonoidHom).map L.subtype := by
    rw [map_map,map_map]
    rfl
  rw [(normalizerEscapeBinaryInput D hn hout e).commutatorCore_eq_internal]
  rw [he,map_commutator,pCore_map_iso 2 a,map_top_of_surjective _ a.surjective]

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
