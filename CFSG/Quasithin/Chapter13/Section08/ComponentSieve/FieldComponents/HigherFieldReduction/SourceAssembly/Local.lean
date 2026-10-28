module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.FullProduct.External
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Envelope

/-!
# Source Borel alignment and external centralization

The ordinary full product J = BL₁ and the actual Sylow-centralizer inverter
put B in B_C O₂(J); the separate two-perfectness of B then gives B ≤ B_C.
The covered branch uses the published full-product theorem with X = L₁,+.
Both arguments keep the genuine intersection O₂(H) ∩ J.

The ordinary and covered natural actions construct the adequate earlier
local data at the exact Sylow used to define B. The Fitting-envelope argument
derives 13.8.14 from 13.8.12(2) and universal 13.8.13. These adapters use
neither the obsolete covered formula and index nor a trivial O₂(H)-action.

Source: Aschbacher–Smith, 13.8.12–14 and the proof of 13.8.20(a),
printed pp.950–951 and 954–955 (combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SourceAssembly
open LocalBorel LocalBorel.CentralizingCalculation
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open ExternalModules
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
local notation "D" => one L (T : Subgroup G) V₁

/-- The ordinary full product gives B-centralization using the actual
Sylow-centralizer inverter, with its genuine two-core intersection. -/
theorem ordinary_borel_centralizes (a : NaturalSetup L (T : Subgroup G) V V₁)
    (h : SylowExternalXAlternative H K (T : Subgroup G) D) :
    d.B ≤ centralizer (V : Set G) := by
  obtain ⟨s, ⟨hsT, hsC⟩, hinv⟩ := h.2
  obtain ⟨sH, hsH, rfl⟩ := hsT
  let C := centralizingResidual d.B D L
  let J := d.B ⊔ D
  have hCJ : C ≤ J := centralizingResidual_le _ _ _
  have hJH : J ≤ H := sup_le ((borel_le_component _ _ _ _ _).trans d.component_le) d.one_le_H
  have hsCnorm : sH.val ∈ normalizer (C : Set G) :=
    centralizingResidual_normalized _ _ _ (T : Subgroup G) d.product_normalizes_L
      d.T_normalizes_product d.standing.normalizes_L hsH
  have hBP : d.B ≤ C ⊔ J.pCoreIn 2 :=
    le_sup_twoCore_of_fixed_inverted_cubic d.B C D J
      (Ordinary.LocalCalculation.factorization d a).symm
      (Ordinary.TwoKernels.product_normalizes_centralizingResidual d) le_sup_left
      (Ordinary.TwoKernels.one_core_le_product_core d)
      (Ordinary.LocalCalculation.cubic_index d a)
      ⟨sH.val, d.T_normalizes_product hsH⟩ hsCnorm
      (Covered.ZeroPlacement.FullProduct.External.inversion_of_star_inversion H D
        d.one_le_H h.1.2.2.2.1 sH hinv).2
      ((Covered.ZeroPlacement.FullProduct.External.source_commutator_le_core_intersection
        d sH hsH hsC).trans
        (Covered.ZeroPlacement.FullProduct.External.ambient_core_intersection_le H J hJH))
  have hBC : d.B ≤ C :=
    le_normal_of_twoPerfect_le_sup_twoCore d.B C J hCJ le_sup_left
      (Ordinary.TwoKernels.product_normalizes_centralizingResidual d)
      (Ordinary.TwoKernels.borel_isPPerfect d) hBP
  exact hBC.trans ((Ordinary.Assembly.centralizingResidual_le_centralizer d).trans inf_le_right)

include d in
/-- The source Fitting alternative follows from 13.8.12(2) and the
universal solvable-overgroup clause 13.8.13, via the actual Fitting envelope. -/
theorem fitting_alternative (hs : Group.IsSolvable (D ⊔ (T : Subgroup G) : Subgroup G))
    (hex : ∀ J : Subgroup G, D ⊔ (T : Subgroup G) ≤ J →
      J ≤ G₁ → Group.IsSolvable J → J ≤ M)
    (h12 : SolvableExclusion.ResidualAlternative L D (plus L (T : Subgroup G) V₁)
      (SolvableExclusion.residualInM H M)) :
    SolvableExclusion.ResidualAlternative L D (plus L (T : Subgroup G) V₁)
      (Components.Fitting.twoFittingResidual H) := by
  have hFM : SolvableExclusion.twoFitting H ≤ M := le_sup_left.trans
    (hex (SolvableExclusion.twoFitting H ⊔ (D ⊔ (T : Subgroup G))) le_sup_right
      ((sup_le (SolvableExclusion.twoFitting_le H) d.member.1.2).trans d.member.2.1)
      (SolvableExclusion.twoFitting_sup_solvable d.member.1.2 hs))
  rw [SolvableExclusion.residualInM_eq_of_twoFitting_le hFM] at h12
  have he : SolvableExclusion.residualWhole H = Components.Fitting.twoFittingResidual H := by
    unfold SolvableExclusion.residualWhole SolvableExclusion.twoResidual
      SolvableExclusion.twoFitting Components.Fitting.twoFittingResidual
      Components.Fitting.twoFittingResidualIn
    exact (map_embedded_pResidual 2 (SolvableExclusion.twoFittingIn H) H.subtype).symm
  rwa [he] at h12


private theorem hex_not_alternating :
    ¬ Nonempty (Atlas.Codes.HexEvenAutomorphisms ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr (centerCongr e).toEquiv
  rw [Representation.Hexacode.even_center_card,
    alternatingGroup.center_eq_bot (by simp), card_bot] at hc
  omega

omit [Finite G] in
/-- Transport the actual hexacode cover, including its central quotient. -/
theorem tripleCover_of_hex_mark (e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) :
    SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) := by
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Representation.Hexacode.even_isQuasisimple
  refine ⟨IsQuasisimple.of_mulEquiv e.symm, ?_, ?_⟩
  · exact (Nat.card_congr (centerCongr e).toEquiv).trans Representation.Hexacode.even_center_card
  · have hm : (center (L ⧸ pCore 2 L)).map e.toMonoidHom =
        center Atlas.Codes.HexEvenAutomorphisms := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (centerCongr e ⟨y, hy⟩).property
      · intro hx
        exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
    exact ⟨(QuotientGroup.congr _ _ e hm).trans
      Representation.Hexacode.even_quotient_center_equiv⟩

/-- The ordinary natural action supplies every local field of the adequate
external interface, at precisely the Sylow that defines the source Borel. -/
theorem ordinaryEarlierLocalData (a : NaturalSetup L (T : Subgroup G) V V₁)
    (hseed : V₃ = ⁅V₃, D⁆)
    (hex : ∀ J : Subgroup G, D ⊔ (T : Subgroup G) ≤ J →
      J ≤ G₁ → Group.IsSolvable J → J ≤ M) :
    SourceCalculation.EarlierLocalData H K D L (T : Subgroup G) V V₃ V₁ M
      (sourceSylow H K (T : Subgroup G) d.sylow_H) where
  local_cases := Or.inl ⟨⟨a.model⟩, rfl⟩
  ordinary_card := fun _ => source_residual_quotient_card a D rfl
  covered_action := fun ⟨e⟩ => (hex_not_alternating ⟨e.symm.trans a.model⟩).elim
  covered_factor := fun ⟨e⟩ => (hex_not_alternating ⟨e.symm.trans a.model⟩).elim
  seed_commutator := hseed
  theta := d.theta
  solvable_overgroups := by
    intro J hJ hJG hs
    exact hex J hJ (by simpa only [d.standing.first_normalizer] using hJG) hs
  sylow := d.sylow_H
  sylow_inter := sourceSylow_image H K (T : Subgroup G) d.sylow_H


/-- The covered natural action supplies the actual triple cover, the marked
plus direction, and the same source Sylow and Borel as the local calculation. -/
theorem coveredEarlierLocalData (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = plus L (T : Subgroup G) V₁ ⊔ zero L)
    (hseed : V₃ = ⁅V₃, D⁆)
    (hex : ∀ J : Subgroup G, D ⊔ (T : Subgroup G) ≤ J →
      J ≤ G₁ → Group.IsSolvable J → J ≤ M) :
    SourceCalculation.EarlierLocalData H K (plus L (T : Subgroup G) V₁) L
      (T : Subgroup G) V V₃ V₁ M (sourceSylow H K (T : Subgroup G) d.sylow_H) where
  local_cases := Or.inr ⟨tripleCover_of_hex_mark a.cover, ⟨a.cover⟩, rfl⟩
  ordinary_card := fun ⟨e⟩ => (hex_not_alternating ⟨a.cover.symm.trans e⟩).elim
  covered_action := fun _ => ⟨a⟩
  covered_factor := fun _ => hfactor
  seed_commutator := hseed
  theta := d.theta
  solvable_overgroups := by
    intro J hJ hJG hs
    exact hex J hJ (by simpa only [d.standing.first_normalizer] using hJG) hs
  sylow := d.sylow_H
  sylow_inter := sourceSylow_image H K (T : Subgroup G) d.sylow_H

/-- The external interface uses the identical Borel lift, not a conjugate
or a Borel selected independently of the source Sylow. -/
theorem borel_eq_external (hKH : K ≤ H) : d.B =
    borelResidual (borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K)
      (sourceSylow H K (T : Subgroup G) d.sylow_H))) := rfl


include d in
/-- The source module lies in the actual Sylow and hence in H. This uses
its elementary abelian natural carrier and relative normality in LT. -/
theorem module_le_H : V ≤ H := by
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.standing.span_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (le_conjugateSpanBy V G₁)
  have hVLT : V ≤ L ⊔ (T : Subgroup G) := d.standing.module_in_reduced.trans
    (sSup_le fun _ h => h.1)
  have hcore := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    hVLT d.standing.normalizes_V
  have hT : (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact hcore.trans (hT.trans d.T_le_H)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SourceAssembly
end
