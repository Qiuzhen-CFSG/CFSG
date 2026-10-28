module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Critical
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Factorization.Source
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualRecognition

/-!
# The literal covered-A6 containment in 13.8.21(1)

The original covered quotient selects the compatible natural flag. Construct
the actual quotient action, prove faithfulness by F.9.2, and compute its seed
dimension. The previously proved source factorization supplies L1=L1,+ L0.
In the contrary branch the existing component reduction gives K*=L3(2), so its
quasisimplicity is a conclusion. The natural tensor section excludes
transvections; only then apply the constructed critical record and its rank
contradiction to obtain the original L1<=K.

The remaining inputs are precisely the preceding component setup, component
list 13.8.21(2), Fitting alternative 13.8.14/16, normalizer bound 13.2.2(9),
F.9 applicability 13.5.7 and noncentrality 13.7.7. This branch uses no additional
G.6.4 classification, representation, factorization, critical-pair or rank premise.
Source: Aschbacher--Smith, 13.8.21(1), printed pp.956--957.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree
open Geometry Geometry.ExternalComponentAction Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  {κ : GroupClass}

theorem L₁_le_of_covered
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (components : RankReduction.SourceSetup κ H K (one L T V₁) M G₁ T)
    (models : RankReduction.SmallQuotient (K ⧸ pCore 2 K))
    (hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hNM : normalizer (zero L : Set G) ≤ M)
    (hfit : fittingPreimageResidual H = ⊥ ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        fittingPreimageResidual H = one L T V₁) ∨
      fittingPreimageResidual H = plus L T V₁)
    (hnoncentral : ¬ ⁅Source.VH H V,H⁆ ≤ Source.UH H V₃) : one L T V₁ ≤ K := by
  by_cases hcontained : one L T V₁ ≤ K
  · exact hcontained
  let : Group.IsPerfect (K.subgroupOf H) := components.component.perfect
  obtain ⟨_,⟨eK⟩⟩ := RankReduction.rank_one_and_model components hcontained models
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F:=ZMod 2) 3 (by decide)
  let : IsSimpleGroup (Source.starImage H K) := eK.isSimpleGroup
  let : Group.IsPerfect (Source.starImage H K) :=
    show Group.IsPerfect ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) from
      Group.IsPerfect.map _
  have hcenter : center (Source.starImage H K) = ⊥ := by
    rcases (inferInstance : (center (Source.starImage H K)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  have hqs : IsQuasisimple (Source.starImage H K) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hNMeq : normalizer (zero L : Set G) = M := by
    apply le_antisymm hNM
    rw [d.local_normalizer]
    exact normalizer_le_zero_normalizer L
  have hn : Nonempty (LocalAction.NaturalSetup L (T:Subgroup G) V V₁ V₃) := by
    rcases local_quotient_alternatives d with ⟨e,he⟩ | ⟨e,he⟩
    · obtain ⟨ec⟩ := hcovered
      have hc := Nat.card_congr (e.symm.trans ec).toEquiv
      rw [Atlas.Codes.hexEven_card] at hc
      have ha : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      omega
    · exact local_covered_flag_model d e he
  obtain ⟨natural⟩ := hn
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary components.local_overgroup
  let act := conjugationAction (d.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hF9.commutator_UH_QH_le_point
  have hfaith : Function.Injective act.representation := f9_section_faithful _ hF9 (sourceSection act hF9.H_centralizes)
  have hk : ∀ h : H,
      (∀ u : Source.UH H V₃,
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (conjugateUH H V₃ h u) =
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) → h ∈ pCore 2 H := by
    intro h hh
    have he : act.representation (QuotientGroup.mk' (pCore 2 H) h) = 1 := by
      ext v
      obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
      change act.representation _ (Additive.ofMul (QuotientGroup.mk' _ u)) = Additive.ofMul (QuotientGroup.mk' _ u)
      rw [act.conjugation]
      exact congrArg Additive.ofMul (hh u)
    exact (QuotientGroup.eq_one_iff h).mp (hfaith (he.trans (map_one act.representation).symm))
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le (show V₃ ≤ Source.UH H V₃ from le_conjugateSpanBy V₃ H)
  have hd : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2 := by
    have hc := ParabolicMarking.seed_card_of_source_orders H V₃ V₁
      (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),show Nat.card (ZMod 2)=2 from by simp] at hc
    exact Nat.pow_right_injective (by decide : 1<2) (show 2^Module.finrank (ZMod 2) (seedSpace H V₃ V₁)=2^2 from hc)
  exact L₁_le_of_covered_source (κ:=κ) (H:=H) (K:=K) (L:=L) (M:=M) (G₁:=G₁)
    (V:=V) (V₃:=V₃) (V₁:=V₁) (S:=T) components models natural
    (CoverFactorization.source_factorization natural) hNMeq hfit hqs act hk hd
    (fun hno => critical_earlier d components.local_overgroup hF9
      (by rw [←components.generated,sup_assoc]) components.normal hqs hnoncentral act hno)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
