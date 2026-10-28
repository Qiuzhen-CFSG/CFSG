module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureConfiguration
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixAutomizer
public import Theory.Representation.HexacodeAction.FullWeightFourNormalTwo
import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedCubicResidual
import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Maximal
import Theory.GroupTheory.SylowNormalizedResidual

/-!
# The actual central point closure in the full automizer

The original closure W is a two-subgroup of the unchanged Sylow subgroup.
Its nontrivial image fixes the original weight-four vector and is normalized
by its entire even vector stabilizer. The same coordinate marking therefore
gives the Klein four, central involution, or elementary eight alternatives.
If W is abelian, its contained scalar point is fixed pointwise and the
Klein four alternative follows.

Source: Aschbacher--Smith, 12.7.15(2--3), printed p.843.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix DuadCalculation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original closure has the three literal automizer possibilities;
abelianity selects the Klein four in the same marked coordinate action. -/
theorem original_tripleSix_central_closure_automizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2) :
    let C := centralizer ({(z : G)} : Set G)
    let R := conjugateSpanBy U C
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    let v := (tripleSixPointCoordinates D a z).toAdd
    W ≤ (T : Subgroup G) ∧
    ∃ f : Automizer U →* HexAutomorphisms, Function.Injective f ∧
      (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k, D.normalizes k.property⟩) =
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
      (inducedAutomizer U K).map f = hexSign.ker ∧
      (∀ (b : Automizer U) (u : U),
        (tripleSixPointCoordinates D a (b.val u)).toAdd =
          Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) ∧
      (let N := (inducedAutomizer U W).map f
       N ≤ Hexacode.fullVectorStabilizer v ∧ IsPGroup 2 N ∧ N ≠ ⊥ ∧
       ∃ e : Hexacode.fullVectorStabilizer v ≃* DuadProduct,
         ∃ r : alternatingGroup (Fin 6),
           (∀ g : Hexacode.fullVectorStabilizer v,
             duadProductHom (e g) = r.val * hexCoordinateSixHom g.val * r.val⁻¹) ∧
           (∀ g : Hexacode.fullVectorStabilizer v,
             hexSign g.val = 1 ↔ (e g).1 = signPermTwo (e g).2) ∧
           (let B := (N.subgroupOf (Hexacode.fullVectorStabilizer v)).map e.toMonoidHom
            (B = (⊥ : Subgroup Two).prod core ∨ B = centralFactor ∨ B = productCore) ∧
            (IsMulCommutative W → B = (⊥ : Subgroup Two).prod core))) := by
  let C := centralizer ({(z : G)} : Set G)
  let J := (pResidual 2 (K ⊓ C : Subgroup G)).map (K ⊓ C).subtype
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let c := tripleSixPointCoordinates D a
  let v := (c z).toAdd
  obtain ⟨hHC, hW, hWcore, _, _, _, hnontrivial⟩ :=
    original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  change W = conjugateSpanBy V1 H at hW
  have hs := original_tripleSix_central_point_g21_at h D a z hz hzT H
    (show (T : Subgroup G) ≤ H from le_sup_right) hHC
  have hWT : W ≤ (T : Subgroup G) := by
    rw [hW]
    exact hs.U_normal_in_T.1
  have hTN : (T : Subgroup G) ≤ normalizer (U : Set G) := ((structural K h).2.2 U D).1
  have hWN : W ≤ normalizer (U : Set G) := hWT.trans hTN
  have hWC : W ≤ C := hWT.trans hzT
  have hHW : H ≤ normalizer (W : Set G) := by
    rw [hW]
    exact le_normalizer_conjugateSpanBy V1 H
  have hCK : K ⊓ C ≤ H :=
    (le_embedded_pResidual_sup_sylow_of_normalizes T (K ⊓ C)
      ((le_inf D.sylow_normalizes_component (hzT.trans C.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf)).trans
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  obtain ⟨f, hf, hfk, hK, hchart⟩ := original_tripleSix_full_automizer h structural D a
  let N := (inducedAutomizer U W).map f
  have hN : N ≤ Hexacode.fullVectorStabilizer v := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hfix : (U.normalizerMonoidHom.rangeRestrict w).val z = z := by
      apply Subtype.ext
      change (w : G) * (z : G) * (w : G)⁻¹ = z
      exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp (hWC hw))
    have hh := hchart (U.normalizerMonoidHom.rangeRestrict w) z
    rw [hfix] at hh
    exact hh.symm
  have hp : IsPGroup 2 N :=
    ((T.isPGroup'.to_le hWT).comap_subtype.map U.normalizerMonoidHom.rangeRestrict).map f
  have hne : N ≠ ⊥ := by
    intro hb
    have hbot : inducedAutomizer U W = ⊥ :=
      (map_eq_bot_iff_of_injective _ hf).mp hb
    have hc := (inducedAutomizer_eq_bot_iff hWN).mp hbot
    apply hnontrivial
    rw [commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)]
    exact bot_le
  have hCKimage : (inducedAutomizer U (K ⊓ C)).map f =
      (Hexacode.fullWeightVectorStabilizer v).map hexSign.ker.subtype := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      rw [hfk ⟨k, hk.1⟩]
      exact ⟨(tripleSixPointCentralizerProjection D a z ⟨k, hk⟩).val,
        (tripleSixPointCentralizerProjection D a z ⟨k, hk⟩).property, rfl⟩
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨k, hk⟩ := tripleSixPointCentralizerProjection_surjective D a z ⟨g, hg⟩
      refine ⟨U.normalizerMonoidHom.rangeRestrict ⟨k, D.normalizes k.property.1⟩,
        ⟨⟨k, D.normalizes k.property.1⟩, k.property, rfl⟩, ?_⟩
      rw [hfk ⟨k, k.property.1⟩]
      exact congrArg (fun q => q.val.val) hk
  have hn : (Hexacode.fullWeightVectorStabilizer v).map hexSign.ker.subtype ≤
      normalizer (N : Set HexAutomorphisms) := by
    rw [← hCKimage]
    exact (map_mono (ChapterE.Section06.inducedAutomizer_normalized hWN
      (hCK.trans hHW))).trans (le_normalizer_map f)
  have hv := tripleSix_sylow_fixed_weightFour D a z hz hzT
  obtain ⟨e, r, he, heven, hcases, hab⟩ :=
    Hexacode.fullWeightFour_normal_two_cases v hv N hN hp hne hn
  refine ⟨hWT, f, hf, hfk, hK, hchart, hN, hp, hne, e, r, he, heven, hcases, ?_⟩
  intro habel
  apply hab
  have hWV : W ≤ centralizer (V1 : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr habel).trans
      (Subgroup.centralizer_le (le_conjugateSpanBy V1 R))
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  refine ⟨mem_top _, ?_⟩
  intro x hx
  change x ∈ Submodule.span Hexacode.F {v} at hx
  let u := c.symm (Multiplicative.ofAdd x)
  have huV : (u : G) ∈ V1 := by
    refine ⟨u, ?_, rfl⟩
    change (c u).toAdd ∈ Submodule.span Hexacode.F {v}
    simpa only [u, c.apply_symm_apply, toAdd_ofAdd] using hx
  have hfix : (U.normalizerMonoidHom.rangeRestrict w).val u = u := by
    apply Subtype.ext
    change (w : G) * (u : G) * (w : G)⁻¹ = u
    exact mul_inv_eq_of_eq_mul ((mem_centralizer_iff.mp (hWV hw) u huV).symm)
  have hh := hchart (U.normalizerMonoidHom.rangeRestrict w) u
  rw [hfix] at hh
  change (c u).toAdd = Hexacode.action (f (U.normalizerMonoidHom.rangeRestrict w))
    (c u).toAdd at hh
  simpa only [u, c.apply_symm_apply, toAdd_ofAdd] using hh.symm

end CFSG.Quasithin.Chapter12.Section07
