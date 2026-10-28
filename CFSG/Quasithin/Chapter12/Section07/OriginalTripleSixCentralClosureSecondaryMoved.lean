module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarFixedModule
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedSylowCentralizer
public import Theory.Representation.ConjugateSpanFixedFree
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Full component movement of the actual secondary module

The secondary subgroup is the literal K-span of its original Sylow-central
seed. Restrict the ambient Sylow to K inside KT. Odd coset averaging then
puts each seed vector into the K-commutator because C_G(K)=1. The resulting
movement equality concerns the entire original subgroup, with no quotient.

Source: Aschbacher--Smith12.7.20, printed p.846, using12.7.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original Sylow-central seed spans a fully moved secondary K-module. -/
theorem original_tripleSix_central_closure_secondary_moved
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let M := K ⊔ (T : Subgroup G)
    let X := tripleSixScalarResidual K
    let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
    let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
    ⁅V,K⁆ = V := by
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
  let Z := C ⊓ omegaCenterIn (T : Subgroup G)
  let V := conjugateSpanBy Z K
  have hs := original_tripleSix_central_closure_scalar_fixed_module
    h structural D a z hz hzT hnot houter
  have hVM : V ≤ M := hs.2.2.1.trans (inf_le_left.trans (pCoreIn_le 2 M))
  let := hs.2.2.2.2.1.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hVM).symm.toMonoidHom (subgroupOfEquivOfLe hVM).symm.injective
  have hKM : K ≤ M := le_sup_left
  let : (K.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer D.sylow_normalizes_component)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)).exists_subgroupOf_eq_of_normal
    (K.subgroupOf M)
  let e := subgroupOfEquivOfLe hKM
  let S : Sylow 2 K := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
    rintro _ ⟨k,hk,rfl⟩
    change k ∈ (P : Subgroup (K.subgroupOf M)).map e.toMonoidHom at hk
    obtain ⟨p,hp,rfl⟩ := hk
    rw [hP] at hp
    exact hp
  have hcentral : centralizer (K : Set G) = ⊥ :=
    original_tripleSix_contained_component_centralizer h structural modules D a
      t ht heven contained hmany seven exits
  apply conjugateSpan_commutator_eq_of_fixed_free Z K S
  · intro x hx
    exact centralizer_le hST ((mem_omegaCenterIn_iff T x).mp hx.2).2.1
  · rw [hcentral,inf_bot_eq]

end CFSG.Quasithin.Chapter12.Section07
