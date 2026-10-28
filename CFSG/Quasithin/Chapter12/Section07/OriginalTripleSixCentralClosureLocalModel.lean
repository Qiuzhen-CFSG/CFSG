module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureCoreRecovery

/-!
# The full original central-closure quotient and its scalar kernel

The original normalizer is KT and its entire two-core is U. The same
six-space chart identifies its full action quotient with the full hexacode
group. The six-letter quotient keeps the complete scalar residual X as
its kernel, and the original K action and every U vector remain marked.

Source: Aschbacher--Smith12.7.20 and12.7.18, printed pp.845--846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The whole original local action has exactly kernel U, its literal
six-letter quotient has exactly the full scalar kernel X, and both are onto. -/
theorem original_tripleSix_central_closure_local_model
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
    let M := normalizer (K : Set G)
    let X := tripleSixScalarResidual K
    ∃ (_hMU : M ≤ normalizer (U : Set G)) (f : M →* HexAutomorphisms),
      Function.Surjective f ∧ f.ker = pCore 2 M ∧ f.ker = U.subgroupOf M ∧
      (∀ k : K, f (inclusion K.le_normalizer k) =
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
      (∀ (m : M) (u : U),
        ((tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
          (Hexacode.action (f m) (tripleSixPointCoordinates D a u).toAdd)) : G) =
          (m : G) * (u : G) * (m : G)⁻¹) ∧
      Function.Surjective (hexCoordinateSixHom.comp f) ∧
      (hexCoordinateSixHom.comp f).ker = X.subgroupOf M ∧
      ∃ e : (M ⧸ pCore 2 M) ≃* HexAutomorphisms,
        ∀ m : M, e (QuotientGroup.mk' (pCore 2 M) m) = f m := by
  obtain ⟨hK,hQ,hM,hN,hC,hjoin⟩ := original_tripleSix_central_closure_core_recovery
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let M := normalizer (K : Set G)
  let H := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  obtain ⟨hHU,f0,hf0,hfk,hchart,hπ,hker,hqker,_⟩ :=
    original_tripleSix_central_closure_secondary_kernel h structural D a z hz hzT hnot houter
  let π := f0.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hHU))
  let eH : M ≃* H := MulEquiv.subgroupCongr hjoin
  let f := π.comp eH.toMonoidHom
  have hf : Function.Surjective f := hπ.comp eH.surjective
  have hUM : U ≤ M := D.le_component.trans K.le_normalizer
  have hk : f.ker = U.subgroupOf M := by
    ext m
    change π (eH m) = 1 ↔ (m : G) ∈ U
    change eH m ∈ π.ker ↔ _
    rw [hker]
    have hh : pCore 2 H = U.subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [map_subgroupOf_eq_of_le (D.le_component.trans (show K ≤ H from le_sup_left))]
      exact hQ
    rw [hh]
    rfl
  have hcore : f.ker = pCore 2 M := by
    rw [hk]
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hUM]
    exact hM.symm
  have hUX : U ≤ X := (original_tripleSix_scalar_residual_contains_module
    h structural D a z hz hzT hnot houter).1
  have hq : (hexCoordinateSixHom.comp f).ker = X.subgroupOf M := by
    ext m
    change (hexCoordinateSixHom.comp π) (eH m) = 1 ↔ (m : G) ∈ X
    change eH m ∈ (hexCoordinateSixHom.comp π).ker ↔ _
    rw [hqker]
    have hh : pCore 2 H ≤ X.subgroupOf H := by
      intro x hx
      exact hUX (hQ ▸ mem_map_of_mem H.subtype hx)
    rw [sup_eq_left.mpr hh]
    rfl
  let e := (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨hN.symm ▸ le_rfl,f,hf,hcore,hk,?_,?_,hexCoordinateSix_surjective.comp hf,hq,e,?_⟩
  · intro k
    exact hfk k
  · intro m u
    have hh := hchart (U.normalizerMonoidHom.rangeRestrict
      ⟨m,hHU (eH m).property⟩) u
    have he : (tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
        (Hexacode.action (f m) (tripleSixPointCoordinates D a u).toAdd)) =
        U.normalizerMonoidHom ⟨m,hHU (eH m).property⟩ u := by
      apply (tripleSixPointCoordinates D a).injective
      rw [(tripleSixPointCoordinates D a).apply_symm_apply]
      exact (congrArg Multiplicative.ofAdd hh).symm
    exact congrArg Subtype.val he
  · intro m
    rfl

end CFSG.Quasithin.Chapter12.Section07
