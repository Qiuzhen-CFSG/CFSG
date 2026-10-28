module
public import Stellmacher.SectionEight.EightSixCostFourNextQuotient
public import Stellmacher.SectionEight.EightSixNextCoreFrattini
public import Theory.GroupTheory.WreathTwoElementaryCard

/-!
# The residual-fixed next core in the cost-four branch

For the original selected cost-four configuration, let V0 be the centralizer
of O²(E) in the actual next two-core. Then V0/Znext is elementary abelian
and |V0|≤8. The next wreath quotient is constructed from the selected local
data; no quotient-model or fixed-core size hypothesis is assumed.

Frattini functoriality along V0≤Qnext and the proved equality
Φ(Qnext)=Znext put Φ(V0) in the central line, giving the elementary quotient.
The source intersection V0∩D=Znext and V0≤Qnext identify
V0∩Qprevious=Znext. Source (14) puts V0 in the initial core, hence in the
previous stabilizer. Local transitivity transports the actual next wreath
quotient to that stabilizer. Restricting its projection to V0 has precisely
the native Znext kernel. The image is elementary and therefore has order
at most four by the dihedral Sylow bound. The kernel has order two, so the
kernel-index formula gives |V0|≤8.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(b),
printed p.44, the fixed-core estimate immediately before the construction
in (b3). This supplies the remaining upper bound for the case-B Sylow order.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u v

private theorem quotient_model_map
    {G : Type u} [Group G] {Model : Type v} [Group Model]
    {A B : Subgroup G} (equiv : G ≃* G)
    (hmodel : QuotientIsModel A B Model) :
    QuotientIsModel (A.map equiv.toMonoidHom) (B.map equiv.toMonoidHom) Model := by
  obtain ⟨projection,hsurjective,hkernel⟩ := hmodel
  let localEquiv := A.equivMapOfInjective equiv.toMonoidHom equiv.injective
  refine ⟨projection.comp localEquiv.symm.toMonoidHom,
    hsurjective.comp localEquiv.symm.surjective,?_⟩
  ext point
  change projection (localEquiv.symm point) = 1 ↔
    (point:G) ∈ B.map equiv.toMonoidHom
  rw [← MonoidHom.mem_ker,hkernel,Subgroup.mem_subgroupOf,Subgroup.mem_map_equiv]
  have hcoe : ((localEquiv.symm point:A):G) = equiv.symm (point:G) := by
    apply equiv.injective
    rw [equiv.apply_symm_apply]
    exact congrArg Subtype.val (localEquiv.apply_symm_apply point)
  rw [hcoe]

public theorem eight_six_cost_four_fixed_core_card_bound
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4) :
    let V0 := QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (twoResidualIn E : Set G)
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    QuotientIsElementaryAbelian V0 Z 2 ∧ Nat.card V0 ≤ 8 := by
  classical
  dsimp only
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let R := QAt Γ cp.firstStep
  let P := GAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let V0 := R ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  have hV0R : V0 ≤ R := inf_le_left
  have hRP : R ≤ P := by
    change Γ.twoCoreAt _ ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ _
  have hN0 : (Z.subgroupOf V0).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hV0R.trans (hRP.trans hPZ))
  let _ := hN0
  have hRtwo : IsPGroup 2 R := by
    change IsPGroup 2 (Γ.twoCoreAt _)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hV0two : IsPGroup 2 V0 := hRtwo.to_le hV0R
  let _ : Fact (IsPGroup 2 R) := ⟨hRtwo⟩
  let _ : Fact (IsPGroup 2 V0) := ⟨hV0two⟩
  have hbase := eight_six_common_structure_local ctx hcenter hquot hlength hcard previous hprev
    D L Q hD hL hQ
  have hPhiR : FrattiniAmbient R = Z := eight_six_next_core_frattini ctx hcenter hlength hcard
    previous D L Q hprev.1 hD hL data hbase.2.2.2
  have hPhi0 : FrattiniAmbient V0 ≤ Z := by
    rintro x ⟨v,hv,rfl⟩
    apply hPhiR.le
    exact Subgroup.mem_map_of_mem R.subtype
      ((frattini_map_le_of_isPGroup (p := 2) (Subgroup.inclusion hV0R))
        (Subgroup.mem_map_of_mem (Subgroup.inclusion hV0R) hv))
  have hElem : QuotientIsElementaryAbelian V0 Z 2 :=
    eight_six_quotient_elementary_of_frattini_le V0 Z hV0two hN0 hPhi0
  have hV0D : V0 ⊓ D = Z := eight_six_selected_fixed_core_intersection
    ctx hcenter hquot hlength hcard previous D L Q hprev hD hL data E A0 actor geom hedge
  have hZ0 : Z ≤ V0 := hV0D.ge.trans inf_le_left
  have hV0previous : V0 ⊓ QAt Γ previous = Z := by
    apply le_antisymm
    · intro x hx
      apply hV0D.le
      exact ⟨hx.1,hD ▸ ⟨hx.2,hV0R hx.1⟩⟩
    · exact le_inf hZ0 ((hV0D.ge.trans inf_le_right).trans (hD.le.trans inf_le_left))
  have hV0Qa : V0 ≤ QAt Γ cp.a := (eight_six_selected_fixed_core_containment
    ctx hcenter hquot hlength hcard previous D L Q hprev hD hL hQ data E A0 actor geom
      hcore hedge ha hout hlarge hmin).1
  have hV0Pprev : V0 ≤ GAt Γ previous := hV0Qa.trans
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous hprev.1 default).2.2
  have hnext := eight_six_cost_four_next_quotient ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
  have hfirst : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  obtain ⟨g,hg⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a hfirst hprev.1
  have hprevModel : QuotientIsModel (GAt Γ previous) (QAt Γ previous) SL2TwoWreathC2 := by
    rw [← hg]
    change QuotientIsModel (stabilizer Γ (Γ.act g cp.firstStep))
      (q Γ (Γ.act g cp.firstStep)) SL2TwoWreathC2
    rw [stabilizer_act,SevenSix.q_act]
    exact quotient_model_map (MulAut.conj (g:G)⁻¹) hnext
  obtain ⟨projection,_,hker⟩ := hprevModel
  let ρ : V0 →* SL2TwoWreathC2 := projection.comp (Subgroup.inclusion hV0Pprev)
  have hρker : ρ.ker = Z.subgroupOf V0 := by
    ext x
    change projection ⟨(x:G),hV0Pprev x.property⟩ = 1 ↔ (x:G) ∈ Z
    rw [← MonoidHom.mem_ker,hker]
    change (x:G) ∈ QAt Γ previous ↔ (x:G) ∈ Z
    exact ⟨fun hx => hV0previous.le ⟨x.property,hx⟩,fun hx => (hV0previous.ge hx).2⟩
  have hpowers (x : ρ.range) : x ^ 2 = 1 := by
    apply Subtype.ext
    obtain ⟨v,hv⟩ := x.property
    change (x:SL2TwoWreathC2) ^ 2 = 1
    rw [← hv,← map_pow]
    apply MonoidHom.mem_ker.mp
    rw [hρker]
    exact hPhi0 (Subgroup.mem_map_of_mem V0.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) v))
  have hImageElem : IsElementaryAbelian 2 ρ.range := {
    toIsMulCommutative := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hpowers x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpowers }
  have hImageCard : Nat.card ρ.range ≤ 4 :=
    wreath_two_elementary_subgroup_card_le_four ρ.range hImageElem
  have hKcard : Nat.card ρ.ker = 2 := by
    rw [hρker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ0).toEquiv).trans
      (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  have hcount := ρ.ker.card_mul_index
  rw [hKcard,Subgroup.index_ker] at hcount
  refine ⟨hElem,?_⟩
  change Nat.card V0 ≤ 8
  omega
end Stellmacher.SectionEight
