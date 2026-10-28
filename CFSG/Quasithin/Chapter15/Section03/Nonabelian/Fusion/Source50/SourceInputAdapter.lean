module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OriginalInitial
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.SourceDisplacement
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Assembly

/-!
# Original scalar and fusion inputs for the source 57 reduction

The source 56 geometry supplies its literal paired subgroup, the quotient
fixed line, common multiplicity and extraspecial actor product. Every other
field of the normal reduction comes from the original local hypotheses,
source 9, the source 46 singularity theorem and the proved source 48–53
calculations. The original quotient maps and quadratic form are retained.

Source: Aschbacher–Smith, 15.3.53–57, printed pp.1146–1148.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

noncomputable def original_earlierSourceInputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient d.Z d.ZS)] [IsElementaryAbelian 2 d.V]
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (v : ActorQuotient d.Z) (hv : zpowers v =
      CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.actorImage d.Z d.V)
    (s : ℕ) (J : Subgroup (centralizerH d.Z))
    (hJT : J ≤ (d.T : Subgroup G).subgroupOf (centralizerH d.Z))
    (hJfix : letI := MulDistribMulAction.compHom (VectorQuotient d.Z d.ZS) (quotientAction d.Z d.ZS)
      FixedPoints.subgroup J (VectorQuotient d.Z d.ZS) = distinguishedLine d.Z d.ZS)
    (hdim : Module.finrank (ZMod 2) (Space d.Z d.ZS) = 2 * (s + 2))
    (g : G) (hI : pairI d.Z d.ZS g = d.Y ⊔ closureU d.Z d.ZS)
    (hcentral : d.V ≤ centralizer (pairP d.Z d.ZS g : Set G))
    (hdec : letI := LocalRestrictions.pair_denominator_normal d.Z d.ZS d.V g hcentral
      Nonempty ((pairP d.Z d.ZS g ⧸ d.V.subgroupOf (pairP d.Z d.ZS g)) ≃*
        (Fin 2 → Fin s → Multiplicative (Fin 2 → ZMod 2))))
    (hexprod : 0 < s → ∃ P : Subgroup (ActorQuotient d.Z),
      IsExtraspecial 2 P ∧ ∃ X : Subgroup P, IsElementaryAbelian 2 X ∧
        Nat.card X = 2 ^ (s + 1) ∧
        (center P).map P.subtype =
          CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.actorImage d.Z d.V) :
    EarlierSourceInputs d.Z d.ZS d.V d.M KnownSimple.IsKnownSimple v s := by
  let h := original_hypothesis hG d hempty hM hu hmany hfixed
  have hconj := original_conjugates_centralize hG d hM hfixed
  have hUnon := original_U_nonabelian hG d hempty hM hu hmany hfixed hnon
  have hkernel := AbelianExclusion.source_kernel d.T d.Y d.V d.ZS d.Z h
  have hdis := source_displacement_fields d h hconj hnon hUnon hkernel v hv
  have hinter := nonabelian_intersections d (centralizerH d.Z) h hconj hnon hUnon
  have h8 : Nat.card (d.V ⊓ closureU d.Z d.ZS : Subgroup G) = 8 := by
    rw [hinter.2.1]
    exact commutator_card_eight d (centralizerH d.Z) h hUnon
  have hne := (InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany h.point_card).1
  let q := FusionCore.OriginalCoordinates.quadraticAction d.action
  have hf := FusionCore.CosetSetup.OriginalSource.source_fusion_inputs hG d hM hfixed
  have h46 := FusionCore.lemma_15_3_46_of_earlier_inputs q hf
    (FusionCore.OriginalCoordinates.plane_definite d.action 1)
  exact {
    sqtk := AbelianExclusion.centralizer_sqtk hG d.Z h.point_card
    T := d.T
    T_le_H := h.T_le_H
    Z_le_ZS := h.point_lt.le
    Z_card := h.point_card
    ZS_card := d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1
    ZS_commutator_T := FusionCore.CosetSetup.OriginalSource.source_seed_commutator d
    kernel := hkernel
    J := J
    J_le_T := hJT
    fixed_line := hJfix
    V_le_H := h.V_le_H
    T_normalizes_V := h.T_normalizes_V
    Vstar_card := hinter.2.2
    marking := hv
    ZS_le_V := inf_le_left
    displacement := hdis.1
    displacement_rank := hdis.2
    dimension := hdim
    Y := d.Y
    g := g
    pair_I := hI
    U_normalizes_Y := h.UH_le_QH.trans (h.QH_le_T.trans h.normalizes_L)
    V_lt_coreY := (source_lemma_15_3_9_of_orthogonal_action hG d.T hempty d.action
      hM hu hmany hne).1
    central_pairP := hcentral
    pair_decomposition := hdec
    quadratic := q.form
    nondegenerate := q.nondegenerate
    V_dimension := q.dimension
    singularity_46 := fun A _ hAV hAM => h46.2.1.2 A hAV.le hAM
    VU_card := h8
    MH_three := FusionCore.CosetSetup.Source49.intersection_three_prime_from_original
      hG d hempty hM hu hmany hfixed
      (FusionCore.CosetSetup.OriginalSource.source_partner_eq hG d hempty hM hu hmany).ge
    ZS_normalizer_three := FusionCore.CosetSetup.Source49.normalizer_three_prime_from_original
      hG d hempty hM hu hmany hfixed
    extraspecial_product := hexprod }

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
