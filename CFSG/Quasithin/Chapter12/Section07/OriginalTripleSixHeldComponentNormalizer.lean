module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldCentralizerConsequences
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPointTI
import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The full normalizer of the original ordinary point component

The full ambient centralizer of B is its original center Vt. Restrict the
actual component to C_G(Vt). Every other component would centralize B and
lie in the elementary Vt, which is impossible. Thus B is the characteristic
layer of C_G(Vt), and N_G(B)=N_G(Vt). In particular the original scalar
residual X really acts on the same B.

Source: Aschbacher--Smith12.7.7, printed pp.840--841. No uniqueness or
normalizer conclusion is retained as a source premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The full centralizer, characteristic-layer placement and actual scalar
normalization of the unchanged original B. -/
theorem original_tripleSix_held_component_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let Vt := tripleSixPoint D a t
    centralizer (B : Set G) = Vt ∧
      (componentLayer (centralizer (Vt : Set G))).map
        (centralizer (Vt : Set G)).subtype = B ∧
      normalizer (B : Set G) = normalizer (Vt : Set G) ∧
      tripleSixScalarResidual K ≤ normalizer (B : Set G) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let Vt := tripleSixPoint D a t
  let C := centralizer (Vt : Set G)
  have hLtH : Lt ≤ H := (map_subtype_le _).trans inf_le_right
  have hBH : B ≤ H := conjugateSpanBy_le_self hLtH
  have hz : centerIn B = Vt := hcenter
  have hLB : Lt ≤ B := le_conjugateSpanBy Lt H
  have hfixed := (original_tripleSix_held_centralizer_consequences
    h structural D a t ht heven hB hcenter e).2.1
  have hCB : centralizer (B : Set G) = Vt := by
    apply le_antisymm
    · exact (centralizer_le hLB).trans_eq hfixed
    · rw [←hz]
      exact inf_le_right
  have hBC : B ≤ C := by
    apply le_centralizer_iff.mpr
    rw [←hz]
    exact inf_le_right
  have hCH : C ≤ H := centralizer_le
    (Set.singleton_subset_iff.mpr (tripleSixPoint_properties D a t ht).1)
  have hcomp : IsComponentIn B C := (show IsComponentIn B H from ⟨hBH,hB⟩).restrict hBC hCH
  have hu (J : Subgroup C) (hJ : IsComponent C J) : J = B.subgroupOf C := by
    by_contra hn
    have hJC : J ≤ centralizer (B.subgroupOf C : Set C) :=
      commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne hcomp.2 hn)
    have hJV : J.map C.subtype ≤ Vt := by
      rw [←hCB]
      rintro _ ⟨j,hj,rfl⟩ b hb
      exact congrArg Subtype.val (hJC hj ⟨b,hBC hb⟩ hb)
    have hVU : Vt ≤ U := (tripleSixPoint_properties D a t ht).2.1
    let := D.elementary
    let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective
      (show Function.Injective ((C.subtype.comp J.subtype).codRestrict U
        (fun j => hVU (hJV (mem_map_of_mem C.subtype j.property)))) from
        fun x y he => Subtype.ext (Subtype.ext (congrArg (fun u : U => (u : G)) he)))
    let := hJ.2
    let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
    let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
    exact Group.IsPerfect.not_isSolvable J inferInstance
  have hlayer : componentLayer C = B.subgroupOf C := by
    apply le_antisymm
    · exact sSup_le (fun J hJ => (hu J hJ).le)
    · exact le_sSup hcomp.2
  have hm : (componentLayer C).map C.subtype = B := by
    rw [hlayer,map_subgroupOf_eq_of_le hBC]
  have hn : normalizer (B : Set G) = normalizer (Vt : Set G) := by
    apply le_antisymm
    · rw [←hz]
      exact normalizes_centerIn le_rfl
    · have hh := (normalizer_le_normalizer_centralizer Vt).trans
        (normalizer_le_normalizer_characteristic_image C (componentLayer C))
      rwa [hm] at hh
  exact ⟨hCB,hm,hn,hn.symm ▸ (tripleSixScalarResidual_point_transitive D a t).1⟩

end CFSG.Quasithin.Chapter12.Section07
