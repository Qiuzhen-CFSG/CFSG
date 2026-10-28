module
public import Stellmacher.SectionTen.TenOneLargeCoreAction
public import Stellmacher.SectionTen.TenOneLargeCentralizerAction
public import Stellmacher.SectionTen.TenOneGeneratedElementary
public import Stellmacher.SectionTen.TenOneGeneratedQuotient
public import Theory.ElementaryAbelian.Join

/-!
# The elementary centralizer enlargement in source (16)

For the actual no-transvection Section Ten context, let Y be the join of
the W-centralizer of the terminal module and the omega-one center of the
middle neighborhood group. This module constructs the elementary subgroup
YVend, proves that the terminal stabilizer normalizes it, and establishes
its residual and middle-section commutator bounds. The common module
intersection lies in the neighborhood omega center, whose intersection
with Vend is already bounded by that common intersection.

W is elementary and lies in the neighborhood group, so the two factors
of Y commute. The terminal-centralizer action theorem bounds [YVend,Eend].
The actual edge Sylow supplements Eend, turning edge normalization into
full terminal normalization. For the middle section, [W,Qmiddle] lies in
the common intersection; the omega-center commutator lies in both the
omega center and Vend, where the mutual-centralizer theorem bounds it.

These are the inputs to the small-image commutator-family argument in
Stellmacher (10.1)(16), Journal of Algebra 190 (1997), printed p.64. Neither
the source-(16) centralizer equality nor the later Frobenius model is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

omit [Finite G] in
private theorem normalizes_omega (Q : Subgroup G) :
    Subgroup.normalizer (Q:Set G) ≤ Subgroup.normalizer (omegaOneCenter Q:Set G) := by
  let K : Subgroup Q := (omega₁ (G:=Subgroup.center Q) (p:=2)).map (Subgroup.center Q).subtype
  let _ : (omega₁ (G:=Subgroup.center Q) (p:=2)).Characteristic := omega₁_characteristic (Subgroup.center Q)
  let _ : K.Characteristic := inferInstance
  exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q K

omit [Finite G] in
private theorem normalizes_closure (X P : Subgroup G) :
    P ≤ Subgroup.normalizer (conjugateClosure X P:Set G) := by
  rw [conjugateClosure,Subgroup.le_normalizer_closure_iff]
  intro mover hmover point hpoint
  obtain ⟨earlier,element,rfl⟩ := hpoint
  apply Subgroup.subset_closure
  refine ⟨⟨mover*(earlier:G),P.mul_mem hmover earlier.property⟩,element,?_⟩
  change mover*((earlier:G)*(element:G)*(earlier:G)⁻¹)*mover⁻¹=
    (mover*(earlier:G))*(element:G)*(mover*(earlier:G))⁻¹
  group

public theorem ten_one_large_centralizer_setup
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let A:=VAt ctx.Γ ctx.criticalPath.firstStep
    let V:=VAt ctx.Γ ctx.criticalPath.a'
    let W:=conjugateClosure (A⊓QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
    let Wnext:=GeneratedNeighborhoodV ctx.Γ middle
    let I:=A⊓V
    let O:=omegaOneCenter Wnext
    let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔O
    IsElementaryAbelian 2 (Y⊔V:Subgroup G) ∧
    Y ≤ Wnext ∧ Y ≤ Subgroup.centralizer (V:Set G) ∧
    GAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer ((Y⊔V:Subgroup G):Set G) ∧
    ⁅Y⊔V,EAt ctx.Γ ctx.criticalPath.a'⁆ ≤ V ∧
    ⁅Y,twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ⊓ QAt ctx.Γ middle⁆ ≤ I ∧
    I ≤ O ∧ O ⊓ V ≤ I := by
  dsimp only
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let Pm:=GAt ctx.Γ middle
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let W:=conjugateClosure (A⊓QAt ctx.Γ ctx.criticalPath.a') Pm
  let Wnext:=GeneratedNeighborhoodV ctx.Γ middle
  let I:=A⊓V
  let O:=omegaOneCenter Wnext
  let C:=W⊓Subgroup.centralizer (V:Set G)
  let Y:=C⊔O
  let BB:=Y⊔V
  let edge:=P⊓Pm
  obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1<ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hlong : 2<ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hAW : A≤Wnext := le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,rfl⟩
  have hVW : V≤Wnext := le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩
  have hWW : W≤Wnext := (ten_one_generated_containment ctx middle hpath).trans inf_le_right
  have hWQ : Wnext≤QAt ctx.Γ middle := nine_seven_neighborhood_le_own_core
    ctx.toLocalContext.toSectionNineLocalContext hlong middle
  have hQP : QAt ctx.Γ middle≤Pm := by
    change ctx.Γ.twoCoreAt middle≤Pm
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hWP : Wnext≤Pm := hWQ.trans hQP
  have hOW : O≤Wnext := (omegaOneCenter_le_centerAmbient Wnext).trans (Subgroup.map_subtype_le _)
  have hOC : O≤Subgroup.centralizer (Wnext:Set G) :=
    (omegaOneCenter_le_centerAmbient Wnext).trans (centerAmbient_le_centralizer Wnext)
  have hOV : O≤Subgroup.centralizer (V:Set G) := hOC.trans (Subgroup.centralizer_le hVW)
  have hYW : Y≤Wnext := sup_le (inf_le_left.trans hWW) hOW
  have hYC : Y≤Subgroup.centralizer (V:Set G) := sup_le inf_le_right hOV
  let _ : IsElementaryAbelian 2 W := ten_one_generated_elementary ctx middle hpath
  let _ : IsElementaryAbelian 2 C := {
    toIsMulCommutative := Subgroup.le_centralizer_iff_isMulCommutative.mp
      ((show C≤W from inf_le_left).trans
        ((Subgroup.le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative W)).trans
          (Subgroup.centralizer_le inf_le_left)))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) (x:G) x.property.1)) }
  let _ : IsElementaryAbelian 2 O := omegaOneCenterAmbient_elementaryAbelian Wnext
  let _ : IsElementaryAbelian 2 Y := IsElementaryAbelian.sup_of_le_centralizer
    (hOC.trans (Subgroup.centralizer_le (inf_le_left.trans hWW)))
  let _ : IsElementaryAbelian 2 A :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hshort).1
  let _ : IsElementaryAbelian 2 V := by
    obtain ⟨actor,_,hmove⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
    change IsElementaryAbelian 2 (v ctx.Γ ctx.criticalPath.a')
    rw [←hmove,v_act]
    exact IsElementaryAbelian.map (MulAut.conj actor⁻¹).toMonoidHom
  let _ : IsElementaryAbelian 2 BB :=
    IsElementaryAbelian.sup_of_le_centralizer (Subgroup.le_centralizer_iff.mp hYC)
  have hBBC : BB≤Subgroup.centralizer (V:Set G) := sup_le hYC
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hBBQ : BB≤QAt ctx.Γ ctx.criticalPath.a' :=
    hBBC.trans (sectionTenOpeningData ctx middle hpath).endpoint_centralizer
  have hBE : ⁅BB,E⁆≤V := (Subgroup.commutator_mono (le_inf hBBQ hBBC) le_rfl).trans
    (ten_one_large_centralizer_residual_commutator ctx middle hpath hno)
  have hPmO : Pm≤Subgroup.normalizer (O:Set G) :=
    (nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle).trans (normalizes_omega Wnext)
  have hPV : P≤Subgroup.normalizer (V:Set G) := stabilizer_le_normalizer_v ctx.Γ _
  have hPNC : P≤Subgroup.normalizer (Subgroup.centralizer (V:Set G):Set G) := hPV.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hedgeC : edge≤Subgroup.normalizer (C:Set G) :=
    (le_inf (inf_le_right.trans (normalizes_closure _ _)) (inf_le_left.trans hPNC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hedgeY : edge≤Subgroup.normalizer (Y:Set G) :=
    (le_inf hedgeC (inf_le_right.trans hPmO)).trans
      (C.normalizer_inf_normalizer_le_normalizer_sup O)
  have hedgeB : edge≤Subgroup.normalizer (BB:Set G) :=
    (le_inf hedgeY (inf_le_left.trans hPV)).trans
      (Y.normalizer_inf_normalizer_le_normalizer_sup V)
  have hEB : E≤Subgroup.normalizer (BB:Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hBE.trans le_sup_right)
  have hPB : P≤Subgroup.normalizer (BB:Set G) := by
    let edgeSylow : Sylow 2 edge := default
    have hdata := edge_sectionThree_data ctx.sectionSeven ctx.Γ
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) edgeSylow
    have hgen := SectionThree.twoResidual_sup_sylowImage hdata.2.1.1.2.1
    have hEP : twoResidualAmbient P=E := by
      change twoResidualAmbient P=ctx.Γ.twoResidualAt ctx.criticalPath.a'
      rw [ctx.Γ.twoResidualAt_def]
      rfl
    rw [hEP] at hgen
    change E ⊔ sylowTwoAmbient edge edgeSylow=P at hgen
    rw [←hgen]
    exact sup_le hEB ((Subgroup.map_subtype_le _).trans hedgeB)
  have hOVI : O⊓V≤I := by
    have hh : O⊓V≤V⊓Subgroup.centralizer (A:Set G) := le_inf inf_le_right
      (inf_le_left.trans (hOC.trans (Subgroup.centralizer_le hAW)))
    exact hh.trans_eq (ten_one_large_mutual_centralizers ctx middle hpath hno).2
  have hIO : I≤O := by
    intro x hx
    apply (mem_omegaOneCenterAmbient_iff Wnext x).mpr
    refine ⟨hAW hx.1,elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx.1,?_⟩
    exact Subgroup.mem_centralizer_iff.mp (ten_one_common_intersection_centralizes ctx middle hpath hx)
  have hCK : ⁅C,U⊓QAt ctx.Γ middle⁆≤I :=
    (Subgroup.commutator_mono inf_le_left inf_le_right).trans
      (ten_one_large_generated_core_commutator ctx middle hpath hno)
  have hOK : ⁅O,U⊓QAt ctx.Γ middle⁆≤I := by
    have hKO : U⊓QAt ctx.Γ middle≤Subgroup.normalizer (O:Set G) :=
      (inf_le_right.trans hQP).trans hPmO
    exact (le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hKO)
      ((Subgroup.commutator_mono (le_sup_right.trans le_sup_left) (inf_le_left.trans (twoCoreIn_le E))).trans hBE)).trans hOVI
  have hYK : ⁅Y,U⊓QAt ctx.Γ middle⁆≤I := by
    have hh := SectionEight.eight_six_commutator_sSup_le ({C,O}:Set (Subgroup G))
      (U⊓QAt ctx.Γ middle) I Pm (ten_one_common_intersection_normalized ctx middle hpath)
      (by intro D hD; rcases hD with rfl|hD; exact (inf_le_left.trans hWW).trans hWP
          have : D=O := Set.mem_singleton_iff.mp hD; subst D; exact hOW.trans hWP)
      (by intro D hD; rcases hD with rfl|hD; exact hCK
          have : D=O := Set.mem_singleton_iff.mp hD; subst D; exact hOK)
    simpa only [sSup_pair] using hh
  exact ⟨inferInstance,hYW,hYC,hPB,hBE,hYK,hIO,hOVI⟩

end Stellmacher.SectionTen
