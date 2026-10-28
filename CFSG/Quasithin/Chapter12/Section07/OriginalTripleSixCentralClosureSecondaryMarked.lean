module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryEight
public import Theory.Representation.HexacodeAction.SecondaryMarkedNatural

/-!
# The actual secondary module in the original point marking

The whole-product bound selects the first literal natural S6 representation.
The even rank-two equality actor is retained; in the odd rank-three branch
its actual even intersection supplies that same equality actor. The second
natural model costs three dimensions there, contradicting the bound two.
Thus the original duad point marking is preserved, together with the exact
W-eight image, the whole module and product, and all original kernels.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual whole secondary module is the first natural module with no
change of the six-letter marking, and the actual W-eight remains quadratic. -/
theorem original_tripleSix_central_closure_secondary_marked_product
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
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
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
           (∃ r : alternatingGroup (Fin 6),
             (W.subgroupOf M).map ((MulAut.conj r.val).toMonoidHom.comp q) =
               DuadCalculation.productCore.map duadProductHom) ∧
           IsQuadratic σ ((W.subgroupOf M).map q) ∧
           Nonempty (σ.Equiv BinaryAlternatingSix.firstNatural) ∧
           Function.Injective σ ∧
           fixedSpace σ (alternatingGroup (Fin 6)) = ⊥ ∧
           subspaceCommutator σ ⊤ (alternatingGroup (Fin 6)) = ⊤ ∧
           IsIrreducible (σ.comp (alternatingGroup (Fin 6)).subtype) ∧
           Module.finrank (ZMod 2) (Additive (V.subgroupOf M)) = 4 ∧
           (Nonempty (σ.Equiv BinaryAlternatingSix.firstNatural) ∨
             Nonempty (σ.Equiv BinaryAlternatingSix.secondNatural)) ∧
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
  obtain ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,hrW,hquad,hfaith,hfixed,hm,
      hirr,hdim,hmodels,hσ,he,hbound,hcases⟩ :=
    original_tripleSix_central_closure_secondary_eight_product
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter hQ
  let := hr.elementary
  let := hj.elementary
  have hmarked := Hexacode.SecondaryMarkedNatural.natural_of_cubic_product
    σ hfaith hfixed hm hbound
  exact ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,hrW,hquad,hmarked,hfaith,hfixed,hm,
    hirr,hdim,hmodels,hσ,he,hbound,hcases⟩

end CFSG.Quasithin.Chapter12.Section07
