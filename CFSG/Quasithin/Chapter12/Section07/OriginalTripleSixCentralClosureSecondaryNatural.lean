module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryFixed
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryMoved
public import Theory.Representation.AlternatingSixSecondaryRecognition

/-!
# Four-dimensionality of the actual secondary module

The original central-seed span is fully moved by K and has no A6 fixed
vectors. The literal cubic actor in either equality case contains an even
involution with displacement at most two. The section displacement budget
forces A6 irreducibility, and the small-degree theorem gives dimension four.
All whole-product coordinates and kernels remain unchanged.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine source produces a four-dimensional irreducible whole
secondary A6 module, including the even equality-offender branch. -/
theorem original_tripleSix_central_closure_secondary_natural_product
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
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
  let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
  obtain ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,hfaith,hfixed,hσ,he,hbound,hcases⟩ :=
    original_tripleSix_central_closure_secondary_fixed_product
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter hQ
  let := hr.elementary
  let := hj.elementary
  let π := f.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU))
  let q := hexCoordinateSixHom.comp π
  have hs := original_tripleSix_central_closure_scalar_fixed_module
    h structural D a z hz hzT hnot houter
  have hVM : V ≤ M := hs.2.2.1.trans (inf_le_left.trans (pCoreIn_le 2 M))
  have hKM : K ≤ M := le_sup_left
  let j := q.comp (inclusion hKM)
  have hjA : j.range ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨k,rfl⟩
    change Equiv.Perm.sign (hexCoordinateSixHom
      (f (U.normalizerMonoidHom.rangeRestrict ⟨k,D.normalizes k.property⟩))) = 1
    rw [hfk k]
    exact (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).property
  let c := (subgroupOfEquivOfLe hVM).symm
  have hact (k : K) (v : V) :
      σ (j k) (Additive.ofMul (c v)) =
        Additive.ofMul (c ⟨(k:G) * v * (k:G)⁻¹,
          le_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ K) k k.property v v.property⟩) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg M.subtype (hσ (inclusion hKM k) (Additive.ofMul (c v)))
  have hgen : ⁅K,V⁆ = V := by
    rw [commutator_comm]
    exact original_tripleSix_central_closure_secondary_moved
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  have hfull := commutator_eq_top_of_conjugation σ V K
    (le_normalizer_conjugateSpanBy _ K) j c.toMonoidHom c.surjective hact hgen
  have hm : subspaceCommutator σ ⊤ (alternatingGroup (Fin 6)) = ⊤ := by
    apply top_unique
    apply hfull.ge.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact Submodule.subset_span ⟨g,hjA hg,v,hv,rfl⟩
  obtain ⟨E,hE,hc,hcase⟩ := hcases
  let A := E.map hexCoordinateSixHom
  have hAE : IsElementaryTwo A := by
    rcases hcase with hc | hc
    · exact hc.2.2.2.2.1
    · exact hc.2.2.2.2.1
  have hcod : fixedCodim σ A = 2 := by
    rcases hcase with hc | hc <;> exact hc.2.2.2.1
  have hrat : fixedCodim σ A ≤ rank A := by
    rcases hcase with hc | hc
    · exact hc.2.2.2.2.2
    · exact hc.2.2.2.2.2.le
  have hcard : 2 < Nat.card A := by
    rw [hAE.card_eq_two_pow_rank]
    have hb : 2^2 ≤ 2^rank A := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨b,hbA,hbe,hbne⟩ := AlternatingSixInvolutionDisplacement.even_element_of_card_gt_two A hcard
  let : IsElementaryAbelian 2 A := hAE.2
  have hbo : orderOf b = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian b hbA) hbne
  obtain ⟨hirr,hdim⟩ := AlternatingSixSecondaryRecognition.irreducible_finrank_four_of_even_actor
    σ hfaith hfixed hm A b hbo hbe hbA (by omega)
  have hmodels := AlternatingSixSecondaryRecognition.natural_models_of_even_actor
    σ hfaith hfixed hm A b hbo hbe hbA (by omega)
  exact ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,hfaith,hfixed,hm,hirr,hdim,hmodels,
    hσ,he,hbound,E,hE,hc,hcase⟩

end CFSG.Quasithin.Chapter12.Section07
