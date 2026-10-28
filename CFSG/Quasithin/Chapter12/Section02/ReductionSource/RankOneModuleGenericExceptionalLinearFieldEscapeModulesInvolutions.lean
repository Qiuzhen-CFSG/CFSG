module
public import Theory.SpecificGroups.PSL3Four.NormalElementaryComponent
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOriginalCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesInvolutions

/-!
# The original opposite actor: Sylow normality, displacement and inner action

For the actual centralizer-span action of 5.1.23, the opposite elementary
image is the image of the G.2.3 core. Hence it is normalized by both the
original Sylow image and the right Cartan. The chief count gives rank
greater than one, while each of its involutions moves at most rank+1
dimensions on the literal U/⟨z⟩ representation.

The original residual and diagram actor now apply normal-elementary
PSL₃(4) placement: this same opposite subgroup lies in the product of
the residual image and its centralizer. This removes outer residual
actions from the remaining ambient obstruction. It does not yet remove
the centralizer factor or prove abelianness of the source span.

Source: Aschbacher--Smith G.2.3, E.2.7 and 5.1.23, printed pp.333--334,
219 and 645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- A contrary source span supplies an elementary subgroup normal under the
original Sylow image and right Cartan, with uniformly small involution displacement.
All the groups, the projection, and the representation are the original ones. -/
theorem linear_cubic_nonabelian_opposite_involutions
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    let P := ((T : Subgroup G).subgroupOf S.H).map (SpanAction.projection s)
    IsElementaryTwo E ∧ 1 < rank E ∧
      E = ((S.S g).subgroupOf S.H).map (SpanAction.projection s) ∧ E ≤ P ∧
      P ⊔ (B.subgroupOf S.H).map (SpanAction.projection s) ≤
        normalizer (E : Set (SpanAction.Actor s)) ∧
      ∀ a ∈ E, a ≠ 1 → orderOf a = 2 ∧
        fixedCodim (SpanAction.representation s) (zpowers a) ≤ rank E + 1 := by
  intro S s E P
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hga : g ∈ S.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨he,_⟩ := SpanAction.binary_opposite_image s b g hga hgn
  have hr : 1 < rank E :=
    linear_cubic_nonabelian_rank_gt_one D h hpsl c d hne hn g hg hgn
  have hE : IsElementaryTwo E := by
    refine ⟨?_,he⟩
    intro hh
    simp only [hh,Representation.BinaryOffender.rank_bot] at hr
    omega
  obtain ⟨hcore,hEP,hPE⟩ := SpanAction.binary_opposite_image_core_and_normalizer s b g hga hgn
  refine ⟨hE,hr,hcore,hEP,sup_le hPE (right_cartan_normalizes_opposite_image c d s g hg),?_⟩
  intro a ha ha1
  let : IsElementaryAbelian 2 E := he
  refine ⟨orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha) ha1,?_⟩
  simpa only [fixedCodim_zpowers_eq_displacement_rank,Module.End.one_eq_id] using
    SpanAction.binary_opposite_involution_displacement s b g hga hgn a ha ha1

/-- The literal opposite image induces inner automorphisms on the original
PSL₃(4) image. This uses its actual Sylow normality and the original diagram actor. -/
theorem linear_cubic_nonabelian_opposite_inner
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    let K := ((residual H).subgroupOf S.H).map (SpanAction.projection s)
    E ≤ K ⊔ centralizer (K : Set (SpanAction.Actor s)) := by
  intro S s E K
  let bn := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hga : g ∈ S.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hE,_⟩ := SpanAction.binary_opposite_image s bn g hga hgn
  let : IsElementaryAbelian 2 E := hE
  obtain ⟨_,hEP,hPE⟩ := SpanAction.binary_opposite_image_core_and_normalizer s bn g hga hgn
  obtain ⟨hN,_⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let : K.Normal := hN
  have hTC : (T : Subgroup G) ≤ S.H := le_sup_right.trans s.local_le
  let P := (T.subtype hTC).mapSurjective (SpanAction.projection_surjective s)
  obtain ⟨F,hF,hfin,hcard,j,t,a,b,ha,hb,hd⟩ :=
    linear_cubic_residual_diagram_action D h hH hK hnf hlinear d
  have ht : SpanAction.projection s (inclusion hTC t) ∈ (P : Subgroup (SpanAction.Actor s)) :=
    mem_map_of_mem (SpanAction.projection s) t.property
  exact Matrix.PSL3Four.NormalElementarySylow.le_component_sup_centralizer_of_diagram
    K P E hEP hPE hcard j (SpanAction.projection s (inclusion hTC t)) ht a b ha hb hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
