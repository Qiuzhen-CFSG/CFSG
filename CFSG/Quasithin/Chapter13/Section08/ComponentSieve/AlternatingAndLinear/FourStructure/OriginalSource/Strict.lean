module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource.B4Classification
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Original
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Factorization.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Pair

/-!
# The Original Strict-Case Module in 13.8.25

The marked B.4 alternatives, source flag, upper section, critical-pair bounds,
and two-factor splitting are constructed on the literal `U_H/V₁` action. The
selected pair and the covered `L₁` factorization come from the original source
setup; only the preceding component and quotient identifications remain
inputs. This proves the whole-module natural conclusion of Aschbacher--Smith
13.8.25, printed pp.960--962 (PDF pp.977--979).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource
open ChiefFactors ChiefFactors.Alignment CriticalTransfer CriticalGeometry CriticalGeometry.Reorientation
open CriticalTransfer.PairConsequences
open TransvectionRecognition.Component.ModelExtension SourceCompletion
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FieldComponents.HigherFieldReduction.ExternalModules
open Chapter2.ComponentRefinement.LieType.Binary
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The actual point residual is normal in H∩M. It equals the embedded
residual of N_L(V₁), so the source normalizers preserve it. -/
theorem point_residual_normal_source (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHG : H ≤ G₁) : ((one L T V₁).subgroupOf (H ⊓ M)).Normal := by
  have he : one L T V₁ = residual (L ⊓ normalizer (V₁ : Set G)) :=
    TransvectionQuotients.FiveSeed.BarMarking.normalizer_residual_eq L V₁ T
      T.isPGroup' d.normalizes_L
  apply normal_subgroupOf_of_le_normalizer
  rw [he]
  apply le_trans _ (normalizer_le_residual_normalizer _)
  apply le_trans _ (inf_normalizer_le_normalizer_inf (H := L) (K := normalizer (V₁ : Set G)))
  apply le_inf
  · exact inf_le_right.trans d.local_normalizer.le
  · exact (inf_le_left.trans (hHG.trans d.first_normalizer.le)).trans
      (normalizer (V₁ : Set G)).le_normalizer

/-- Whole-module recognition in the original strict case of 13.8.25.
The covered quotient and component conclusions are the preceding group inputs;
the source flag, all module geometry, B.4 classification and splitting inputs
are constructed here. The conclusion uses the literal action on U_H/V₁. -/
theorem natural_module_of_strict_source
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hLK : one L T V₁ ≤ K) (hKT : K ⊔ (T : Subgroup G) = H)
    (eK : (K ⧸ pCore 2 K) ≃* PSL 4) (hHG : H = G₁)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hno : ∀ a : Source.Hstar H, fixedCodim ρ (zpowers a) ≠ 1)
    (hD : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hp : 0 < rank (Source.starImage H (c.Ugamma V₃)))
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃))) :
    ∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
      (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
      (∀ a v, eU (ρ a v) = eH a (eU v)) ∧
      Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4 := by
  let : IsElementaryAbelian 2 (Source.VH H V) := vh_elementary_source d hHz.2.1
  let : IsElementaryAbelian 2 V := local_elementary d
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  have hKH : K ≤ H := hKT ▸ le_sup_left
  have hL₁H : one L T V₁ ≤ H := hLK.trans hKH
  have hTH : (T : Subgroup G) ≤ H := hKT ▸ le_sup_right
  have hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
    rw [← hKT, ← sup_assoc, sup_eq_left.mpr hLK]
  obtain ⟨dc⟩ : Nonempty (LocalAction.NaturalSetup L T V V₁ V₃) := by
    rcases local_quotient_alternatives d with ⟨e, _⟩ | ⟨e, he⟩
    · obtain ⟨f⟩ := hcovered
      have hh := Nat.card_congr (centerCongr (f.symm.trans e)).toEquiv
      rw [Representation.Hexacode.even_center_card,
        alternatingGroup.center_eq_bot (by simp), card_bot] at hh
      omega
    · exact local_covered_flag_model d e he
  have hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) := by
    refine ⟨local_quotient_quasisimple d, ?_, ⟨local_central_quotient d⟩⟩
    rw [Nat.card_congr (centerCongr dc.cover).toEquiv, Representation.Hexacode.even_center_card]
  have e := CriticalSource.earlier_inputs d hHz hF9 hcentral hcomm ρ hρ
  have hcγ := Comparison.component_conjugate H K hKH hN hqs (MulAut.conj (c.gb : G))
  have hnγ : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)).Normal := by
    rw [c.vertexGroup_gamma]
    exact hcγ.1
  have hrγ : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)) = ⊤ := by
    rw [c.vertexGroup_gamma]
    exact hcγ.2.1
  have hqγ : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
      (K.map (MulAut.conj (c.gb : G)).toMonoidHom)) := by
    rw [c.vertexGroup_gamma]
    exact hcγ.2.2
  let act : FieldComponents.LinearThree.SourceAction H V₃ V₁ := {
    line_le := d.line_le_uh H
    seed_le := hF9.plus_le_H
    representation := ρ
    conjugation := hρ }
  have hrV := c.rank_gt_one_of_component_no_uStar_transvection
    (sourceOne L T V₁) K V₃ V₁ hgen (Comparison.local_edge d hF9)
    hnγ hrγ hqγ (e.terminal_core c) d.seed_le hF9.V_le_H
    ((d.line_le_plane.trans d.plane_le_seed).trans hF9.plus_le_H)
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point (e.geometry c) d.line_card
    e.centralizer (e.failure c) e.noncentral
    (c.edge_commutator_le_of_flag V₃ d.seed_le e.flag_index e.noncentral e.edge_normalizes)
    (e.endpoint_core c) (e.proper_edge c) hcomp
    (Comparison.no_source_transvection act _ _ hno)
  have hinter : V ⊓ Source.UH H V₃ = V₃ :=
    (flag_intersection_of_index_two V V₃ (Source.UH H V₃)
      (le_inf d.seed_le (le_conjugateSpanBy V₃ H)) e.flag_index
      (seed_not_le_UH_of_noncentral H V V₃ e.noncentral)).symm
  have hidx : V₁.relIndex V₂ = 2 := by
    have hh := card_mul_index (V₁.subgroupOf V₂)
    rw [Nat.card_congr (subgroupOfEquivOfLe d.line_le_plane).toEquiv,
      d.line_card, d.plane_card] at hh
    change 2 * V₁.relIndex V₂ = 4 at hh
    omega
  obtain ⟨τ, ⟨upper⟩⟩ := exists_upperSection_source d hF9 hHz.2.1 hcomm
  exact source_natural_module_of_strict_critical_pair H K M L V V₁ V₂ V₃ T dc c ρ hρ
    hKH hLK ((CoverFactorization.source_one_le dc).trans (d.local_normalizer ▸ L.le_normalizer))
    (d.local_normalizer ▸ d.normalizes_L) hK hN
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩ hKT hc
    (CoverFactorization.source_factorization dc) (point_residual_normal_source d hHz.2.1)
    (SolvableSource.covered_normalizer_source d hmax hcovered) eK
    (seed_index_source d) (seed_irreducible_source d hL₁H ρ hρ)
    hF9.V_le_H hF9.H_centralizes d.line_card (Comparison.local_edge d hF9)
    hnγ hrγ hqγ (e.terminal_core c) hF9.commutator_UH_QH_le_point
    e.noncentral e.flag_index e.edge_normalizes e.geometry e.initial_core e.estimate
    hD hp hcomp hrV linearB4_source (hHG.trans d.first_normalizer)
    (by rw [commutator_comm]; exact e.centralizer)
    d.plane_le_seed hidx d.plane_stable hinter
    (fun b => Terminal.component_generation d hF9 b hgen hK hN hqs)
    twoFactorSplitting_source τ upper

/-- The complete no-transvection branch, with the strict critical pair selected
from the original source geometry. Final group-quotient assembly is retained by
`qt-d-138-linear-source`. -/
theorem natural_module_of_no_transvections_source
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hLK : one L T V₁ ≤ K) (hKT : K ⊔ (T : Subgroup G) = H)
    (eK : (K ⧸ pCore 2 K) ≃* PSL 4) (hHG : H = G₁)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hno : ∀ a : Source.Hstar H, fixedCodim ρ (zpowers a) ≠ 1) :
    ∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
      (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
      (∀ a v, eU (ρ a v) = eH a (eU v)) ∧
      Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4 := by
  have hKH : K ≤ H := hKT ▸ le_sup_left
  have hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
    rw [← hKT, ← sup_assoc, sup_eq_left.mpr hLK]
  have hno' : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1 := by
    intro g
    simpa only [fixedCodim_zpowers_eq_displacement_rank] using hno g
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness d hHz hF9 hgen hK hN hqs
    hcentral hcomm ρ hρ hno'
  exact natural_module_of_strict_source d hmax hHz hF9 hcentral hcomm hcovered
    hK hN hqs hLK hKT eK hHG w.pair ρ hρ hno w.strict_base w.positive w.comparison
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource
