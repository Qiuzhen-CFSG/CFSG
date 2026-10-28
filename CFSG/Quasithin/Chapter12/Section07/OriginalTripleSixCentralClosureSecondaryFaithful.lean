module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryProduct
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedSylowCentralizer
public import Theory.Representation.HexacodeAction.SecondaryEquality

/-!
# Faithfulness of the actual secondary action

In the contrary branch O₂(KT)≠U the original secondary module is nonzero.
The proved contained-point source12.7.12 centralizer theorem, with all its
original earlier inputs retained, excludes a nontrivial S6 action kernel:
such a normal kernel contains A6 and would centralize the whole secondary
module under K. The original full product, coordinate chart, and scalar
kernel remain unchanged. The whole-product bound now produces an actual
cubic actor in the exact even-equality or odd-strong-offender case.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine original centralizer source makes the constructed secondary
representation faithful whenever the whole core exceeds U. All earlier source
hypotheses and the unchanged product coordinates are retained. -/
theorem original_tripleSix_central_closure_secondary_faithful_product
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
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K)
    (hQ : (K ⊔ (T : Subgroup G)).pCoreIn 2 ≠ U) :
    let M := K ⊔ (T : Subgroup G)
    let X := tripleSixScalarResidual K
    let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
    let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
    let J := (U ⊔ V).subgroupOf M
    ∃ (hr : IsPReduced 2 (V.subgroupOf M)) (hj : IsPReduced 2 J),
      letI := hr.elementary
      letI := hj.elementary
      ∃ (hMU : M ≤ normalizer (U : Set G)) (f : Automizer U →* HexAutomorphisms),
        Function.Bijective f ∧
        (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k,D.normalizes k.property⟩) =
          (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
        (∀ (b : Automizer U) (u : U),
          (tripleSixPointCoordinates D a (b.val u)).toAdd =
            Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) ∧
        (let π := f.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU))
         let q := hexCoordinateSixHom.comp π
         Function.Surjective π ∧ π.ker = pCore 2 M ∧ Function.Surjective q ∧
         q.ker = (X.subgroupOf M) ⊔ pCore 2 M ∧
         ∃ σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive (V.subgroupOf M)),
           Function.Injective σ ∧
           (∀ (m : M) (v : Additive (V.subgroupOf M)),
             ((σ (q m) v).toMul : M) = m * (v.toMul : M) * m⁻¹) ∧
           (∃ e : (hexacode × Additive (V.subgroupOf M)) ≃ₗ[ZMod 2] Additive J,
             ∀ (u : U) (v : V.subgroupOf M),
               (((e ((tripleSixPointCoordinates D a u).toAdd,Additive.ofMul v)).toMul : M) : G) =
                 (u : G) * (v : M)) ∧
           cubicRatio (Hexacode.action.prod (σ.comp hexCoordinateSixHom)) ≤ 2 ∧
           ∃ E : Subgroup HexAutomorphisms, IsElementaryTwo E ∧
             IsCubic (Hexacode.action.prod (σ.comp hexCoordinateSixHom)) E ∧
             ((E ≤ hexSign.ker ∧ rank E = 2 ∧ fixedCodim Hexacode.action E = 2 ∧
               fixedCodim σ (E.map hexCoordinateSixHom) = 2 ∧
               IsOffender σ (E.map hexCoordinateSixHom)) ∨
             (¬ E ≤ hexSign.ker ∧ rank E = 3 ∧ fixedCodim Hexacode.action E = 4 ∧
               fixedCodim σ (E.map hexCoordinateSixHom) = 2 ∧
               IsStrongOffender σ (E.map hexCoordinateSixHom)))) := by
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
  let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
  let J := (U ⊔ V).subgroupOf M
  obtain ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,hσ,he,hbound⟩ :=
    original_tripleSix_central_closure_secondary_product h structural D a z hz hzT hnot houter
  let := hr.elementary
  let := hj.elementary
  let π := f.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU))
  let q := hexCoordinateSixHom.comp π
  have hs := original_tripleSix_central_closure_scalar_fixed_module
    h structural D a z hz hzT hnot houter
  have hVM : V ≤ M := hs.2.2.1.trans (inf_le_left.trans (pCoreIn_le 2 M))
  have hVne : V ≠ ⊥ := (hs.2.1 hQ).2
  have hcentral : centralizer (K : Set G) = ⊥ :=
    original_tripleSix_contained_component_centralizer h structural modules D a
      t ht heven contained hmany seven exits
  have hfaith : Function.Injective σ := by
    apply σ.ker_eq_bot_iff.mp
    by_contra hn
    have hA : alternatingGroup (Fin 6) ≤ σ.ker :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6))
        ((Subgroup.nontrivial_iff_ne_bot _).mpr hn)
    have hVK : V ≤ centralizer (K : Set G) := by
      intro v hv k hk
      let m : M := ⟨k,(show K ≤ M from le_sup_left) hk⟩
      let w : Additive (V.subgroupOf M) := Additive.ofMul ⟨⟨v,hVM hv⟩,hv⟩
      have hm : q m ∈ alternatingGroup (Fin 6) := by
        change Equiv.Perm.sign (hexCoordinateSixHom
          (f (U.normalizerMonoidHom.rangeRestrict ⟨k,D.normalizes hk⟩))) = 1
        rw [hfk ⟨k,hk⟩]
        exact (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨k,hk⟩)).property
      have ha : σ (q m) = 1 := hA hm
      have hconj := congrArg M.subtype (hσ m w)
      change (((σ (q m) w).toMul : M) : G) = k * v * k⁻¹ at hconj
      rw [ha] at hconj
      exact mul_inv_eq_iff_eq_mul.mp hconj.symm
    exact hVne (bot_unique (hVK.trans_eq hcentral))
  exact ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,hfaith,hσ,he,hbound,
    Hexacode.SecondaryEquality.cubic_product_cases σ hfaith hbound⟩

end CFSG.Quasithin.Chapter12.Section07
