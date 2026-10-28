module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.ReducedSubmoduleClassification
public import Theory.GroupTheory.SimpleSectionSolvableReduction
/-!
# The original simple component quotient on a reduced C.2.7 submodule

Reducedness kills the image of the two-core. Noncentrality makes the component
image nontrivial, so the induced map from its simple two-core quotient is an
isomorphism. The comparison retains the literal projection on every element.

Source: Aschbacher--Smith B.2.10 and 15.1.27, pp.77,1102.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass} {H K R M : Subgroup G}
/-- The same two-core quotient acts on the chosen noncentral reduced submodule. -/
@[expose] noncomputable def coreQuotientEquiv_reducedSubmodule
    (hi : Input κ H R M K)
    (W : Subgroup (K ⊔ R : Subgroup G)) [W.Normal] [IsElementaryAbelian 2 W]
    (hr : IsPReduced 2 W) (hm : ⁅W,K.subgroupOf (K ⊔ R)⁆ ≠ ⊥)
    [IsSimpleGroup (K ⧸ pCore 2 K)] :
    (K ⧸ pCore 2 K) ≃* (K.subgroupOf (K ⊔ R)).map
      (QuotientGroup.mk' (centralizer (W : Set (K ⊔ R : Subgroup G)))) := by
  let J := K ⊔ R
  let K0 := K.subgroupOf J
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hi.normalizes)
  let e : K0 ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eQ : (K0 ⧸ pCore 2 K0) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsSimpleGroup (K0 ⧸ pCore 2 K0) := eQ.isSimpleGroup
  have hcore : pCore 2 J ≤ C := by
    have hh : (pCore 2 J).map q ≤ pCore 2 (J ⧸ C) :=
      le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective _),pCore_isPGroup.map q⟩
    have he := (map_eq_bot_iff (pCore 2 J)).mp (bot_unique (hh.trans hr.quotient_pCore_eq_bot.le))
    simpa only [q,QuotientGroup.ker_mk'] using he
  let f := q.subgroupMap K0
  have hker : pCore 2 K0 ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := C) (x : J)).mpr
      (hcore (pCoreIn_le_of_subnormal 2 (inferInstance : K0.Normal).isSubnormal
        (mem_map_of_mem K0.subtype hx)))
  have hne : K0.map q ≠ ⊥ := by
    intro hb
    have hh := (map_eq_bot_iff K0).mp hb
    have hc : K0 ≤ C := by simpa only [q,QuotientGroup.ker_mk'] using hh
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  let : Nontrivial (K0.map q) := (nontrivial_iff_ne_bot _).mpr hne
  let fQ := QuotientGroup.lift (pCore 2 K0) f hker
  have hfQ : Function.Surjective fQ := QuotientGroup.lift_surjective_of_surjective _ f
    (q.subgroupMap_surjective K0) _
  exact eQ.symm.trans (MulEquiv.ofBijective fQ
    ⟨fQ.injective_of_surjective_of_simple hfQ,hfQ⟩)
/-- The quotient identification preserves every original component element. -/
@[simp] theorem coreQuotientEquiv_reducedSubmodule_mk
    (hi : Input κ H R M K)
    (W : Subgroup (K ⊔ R : Subgroup G)) [W.Normal] [IsElementaryAbelian 2 W]
    (hr : IsPReduced 2 W) (hm : ⁅W,K.subgroupOf (K ⊔ R)⁆ ≠ ⊥)
    [IsSimpleGroup (K ⧸ pCore 2 K)] (x : K) :
    coreQuotientEquiv_reducedSubmodule hi W hr hm (QuotientGroup.mk' (pCore 2 K) x) =
      (QuotientGroup.mk' (centralizer (W : Set (K ⊔ R : Subgroup G)))).subgroupMap
        (K.subgroupOf (K ⊔ R))
        ((subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)).symm x) := by
  rfl
end CFSG.Quasithin.ChapterC.C27Source
