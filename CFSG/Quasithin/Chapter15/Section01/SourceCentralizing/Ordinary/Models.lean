module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.Centralizer
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OrdinarySource.Marking
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceCubicExclusion
public import Theory.Mathieu.M11.Properties.ElementarySylowFixers
public import Theory.Mathieu.M11.Properties.RankLower
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.Mathieu.M12.Properties.ThreeRank
public import Theory.Mathieu.M12.ValueBoundParabolics.Supplement
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.Mathieu.M23.Properties.PointStabilizer
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockGeometry
public import Theory.Mathieu.M12.Properties.SylowFixedActions
public import Theory.Mathieu.M22.Properties.ElementarySylowFixers
public import Theory.Mathieu.M23.Properties.ElementarySylowFixers
public import Theory.Mathieu.M24.Properties.ElementarySylowFixers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementarySylowFixers
/-!
# Ordinary Mathieu and J2 component centralizer comparisons

The earlier cubic residual theorem makes the actual component characteristic
in G1, supplying normalization by all original central involutions. The
literal Sylow intersection and the marked quotient then transport the
intrinsic elementary Sylow-fixer bounds for M11, M12, M22, M23, M24 and J2.
Together with actual residual escape, this proves C_S(Y)=C_S(L) for these
ordinary components. Nontrivial central two-covers remain throughout.

Source: Aschbacher--Smith15.1.22(**),15.1.25(1),15.1.26,
printed pp.1099,1102. The quotient recognition and cubic Facts are separate
source inputs; the final consumer constructs residual escape for its marker.
-/
public section
namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Original cubic source inputs remove the independent star-image hypotheses. -/
theorem ordinary_source_centralizer_of_model (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hodd : pPrimeCore 2 d.G1 = ⊥) (hSL : Chapter1.IsSylowIn 2 d.SL d.L)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)] (hf : Facts (d.L ⧸ pCore 2 d.L))
    {X : Type*} [Group X] (e : (d.L ⧸ pCore 2 d.L) ≃* X)
    (hfix : ∀ (Q : Sylow 2 X) (B : Subgroup (MulAut X)),
      IsElementaryAbelian 2 B → (∀ b ∈ B, ∀ x ∈ Q, b x = x) → Nat.card B ≤ 2)
    (hout : ¬ (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype ≤ d.MZ) :
    d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
      (M ⊓ d.L).subtype) : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
  obtain ⟨hLc,hY⟩ := d.source_cubic_component hG h hf
  obtain ⟨hcenter,hcenterTwo⟩ := d.ordinary_center hL hodd
  let := h.elementary
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hTM)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh
  have hZ1T := (d.Z1_le_fixed.trans inf_le_left).trans hVT
  have hZN : centralInvolutions T ≤ normalizer (d.L : Set G) := by
    have hn := d.G1.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.G1 (primeToResidual 3 d.G1))
    rw [←hLc] at hn
    exact ((centralInvolutions_le_centralizer_sylow T).trans (centralizer_le hZ1T)).trans hn
  apply d.ordinary_residual_centralizer_of_model hTM hu hL hcenter hcenterTwo hZN hSL hZ1T e hfix
  rwa [←hY]

/-- The five Mathieu models and J2 have the required intrinsic Sylow-fixer bounds. -/
@[expose] def SmallOrdinaryModel (Q : Type*) [Group Q] : Prop :=
  Nonempty (Q ≃* Sporadic.Mathieu.M11) ∨
  Nonempty (Q ≃* Sporadic.Mathieu.M12) ∨
  Nonempty (Q ≃* Sporadic.Mathieu.M22) ∨
  Nonempty (Q ≃* Sporadic.Mathieu.M23) ∨
  Nonempty (Q ≃* Sporadic.Mathieu.M24) ∨
  Nonempty (Q ≃* Sporadic.LeechRelated.J2.Carrier)

private theorem m22_outer_two : IsPGroup 2 (MulAut.Outer Sporadic.Mathieu.M22) := by
  apply IsPGroup.of_card_dvd_pow (n := 1)
  exact dvd_trans Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two (by norm_num)

private theorem m23_rank_ge_two : 2 ≤ primeRank 3 Sporadic.Mathieu.M23 := by
  exact (Sporadic.Mathieu.m22_primeRank_three.ge).trans
    ((primeRank_equiv 3 Sporadic.Mathieu.m23EquivM22PointStabilizer).le.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 _
        (MulAction.stabilizer Sporadic.Mathieu.M23 (9 : Fin 23)).subtype_injective))

private theorem m24_rank_ge_two : 2 ≤ primeRank 3 Sporadic.Mathieu.M24 := by
  exact m23_rank_ge_two.trans
    ((primeRank_equiv 3 Sporadic.Mathieu.m23EquivM24PointStabilizer).le.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 _
        (MulAction.stabilizer Sporadic.Mathieu.M24 (24 : Fin 24)).subtype_injective))

private theorem facts_m11 : Facts Sporadic.Mathieu.M11 :=
  ⟨Sporadic.Mathieu.m11_center_eq_bot, Sporadic.Mathieu.m11_primeRank_three_ge_two,
    Sporadic.Mathieu.m11_outer_isPGroup_two⟩
private theorem facts_m12 : Facts Sporadic.Mathieu.M12 :=
  ⟨Sporadic.Mathieu.m12_center_eq_bot, Sporadic.Mathieu.m12_three_rank_ge_two,
    Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.outer_isPGroup_two⟩
private theorem facts_m22 : Facts Sporadic.Mathieu.M22 :=
  ⟨Sporadic.Mathieu.m22_center_eq_bot, Sporadic.Mathieu.m22_primeRank_three.ge, m22_outer_two⟩
private theorem facts_m23 : Facts Sporadic.Mathieu.M23 :=
  ⟨Sporadic.Mathieu.M23Geometry.m23_center_eq_bot, m23_rank_ge_two,
    Sporadic.Mathieu.m23_outer_isTwoGroup⟩
private theorem facts_m24 : Facts Sporadic.Mathieu.M24 :=
  ⟨Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot, m24_rank_ge_two,
    Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two⟩
private theorem facts_j2 : Facts Sporadic.LeechRelated.J2.Carrier :=
  ⟨Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockGeometry.center_eq_bot,
    Sporadic.LeechRelated.J2.three_rank_ge_two,
    Sporadic.LeechRelated.J2.outer_isTwoGroup⟩

/-- Every recognized ordinary model supplies the cubic Facts used by the source. -/
theorem facts_of_small_model {Q : Type*} [Group Q] [Finite Q]
    (he : SmallOrdinaryModel Q) : Facts Q := by
  unfold SmallOrdinaryModel at he
  rcases he with he | he | he | he | he | he <;> obtain ⟨e⟩ := he
  · exact Facts.of_equiv e facts_m11
  · exact Facts.of_equiv e facts_m12
  · exact Facts.of_equiv e facts_m22
  · exact Facts.of_equiv e facts_m23
  · exact Facts.of_equiv e facts_m24
  · exact Facts.of_equiv e facts_j2

/-- Each listed actual ordinary component satisfies the original equal-centralizer conclusion. -/
theorem ordinary_small_model_centralizer (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hodd : pPrimeCore 2 d.G1 = ⊥) (hSL : Chapter1.IsSylowIn 2 d.SL d.L)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)] (hf : Facts (d.L ⧸ pCore 2 d.L))
    (he : SmallOrdinaryModel (d.L ⧸ pCore 2 d.L))
    (hout : ¬ (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype ≤ d.MZ) :
    d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
      (M ⊓ d.L).subtype) : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
  have centerModel {X : Type} [Group X] (e : (d.L ⧸ pCore 2 d.L) ≃* X) : center X = ⊥ := by
    apply bot_unique
    intro x hx
    apply e.symm.map_eq_one_iff.mp
    exact hf.1.le ((centerCongr e.symm) ⟨x,hx⟩).property
  unfold SmallOrdinaryModel at he
  rcases he with he | he | he | he | he | he <;> obtain ⟨e⟩ := he
  · exact d.ordinary_source_centralizer_of_model hG hTM hu h hL hodd hSL hf e
      (fun P A hA hfix => @Sporadic.Mathieu.m11_elementary_sylow_fixer_card_le_two P A hA hfix) hout
  · exact d.ordinary_source_centralizer_of_model hG hTM hu h hL hodd hSL hf e
      (fun P A _ hfix => Sporadic.Mathieu.m12_faithful_sylow_fixed_action_card_le_two
        P A.subtype A.subtype_injective (fun a x => hfix a a.property x x.property)) hout
  · exact d.ordinary_source_centralizer_of_model hG hTM hu h hL hodd hSL hf e
      (fun P A hA hfix => @Sporadic.Mathieu.m22_elementary_sylow_fixer_card_le_two
        (centerModel e) P A hA hfix) hout
  · exact d.ordinary_source_centralizer_of_model hG hTM hu h hL hodd hSL hf e
      (fun P A hA hfix => @Sporadic.Mathieu.m23_elementary_sylow_fixer_card_le_two
        (centerModel e) P A hA hfix) hout
  · exact d.ordinary_source_centralizer_of_model hG hTM hu h hL hodd hSL hf e
      (fun P A hA hfix => @Sporadic.Mathieu.m24_elementary_sylow_fixer_card_le_two
        (centerModel e) P A hA hfix) hout
  · exact d.ordinary_source_centralizer_of_model hG hTM hu h hL hodd hSL hf e
      (fun P A hA hfix => @Sporadic.LeechRelated.J2.elementary_sylow_fixer_card_le_two
        (centerModel e) P A hA hfix) hout
end CaseIComponentData

end CFSG.Quasithin.Chapter15.Section01
