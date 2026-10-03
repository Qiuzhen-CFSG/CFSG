module
public import Stellmacher.SectionTen.TenOneLargeResidualDerived
public import Stellmacher.SectionTen.TenOneLargeResidualJoinIndex
public import Stellmacher.SectionTen.TenOneLargeFirstFrobenius
public import Stellmacher.SectionTen.TenOneLargeCommonConclusions
public import Stellmacher.SectionTen.GeneratedTenOneReduction
public import Stellmacher.SectionTen.TenOneLargeSylowBounds
public import Stellmacher.SectionTen.TenOneLargeMiddleResidualIndex

/-!
# The complete large alternative of Stellmacher (10.1)

Under the original no-transvection hypothesis, the prescribed subgroups W,
W0 and Wnext satisfy the common index and derived equations and the complete
large alternative. No local quotient model, cardinality, derived equality
or terminal core bound is assumed separately.

The native terminal core bound gives the original Sylow interval. The
first local quotient is the proved Frobenius group of order twenty. A single
middle-stabilizer conjugation transports the terminal residual quotient and
derived structure to the first vertex. The common neighborhood index chain,
source-(17) generated index, middle residual join index and derived-center
index supply every remaining clause with its prescribed denominator.

Source: Stellmacher (10.1)(b), Journal of Algebra 190 (1997), printed pp.60–65.
This conclusion joins the complete small alternative in the final ambient
classification while retaining the original graph, path and subgroup definitions.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
private theorem first_step_structure
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (ZAt ctx.Γ ctx.criticalPath.firstStep) (2 ^ 4) ∧
    QuotientCardEq (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep))
      (VAt ctx.Γ ctx.criticalPath.firstStep) (2 ^ 4) ∧
    DerivedAmbient (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) =
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let U := twoCoreIn (EAt Γ cp.firstStep)
  let Ut := twoCoreIn (EAt Γ cp.a')
  let V := VAt Γ cp.firstStep
  let Vt := VAt Γ cp.a'
  let Z := ZAt Γ cp.firstStep
  let Zt := ZAt Γ cp.a'
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
  let f : MulAut G := MulAut.conj (mover:G)⁻¹
  have hUmap : U.map f.toMonoidHom = Ut := by
    change (twoCoreIn (Γ.twoResidualAt cp.firstStep)).map f.toMonoidHom =
      twoCoreIn (Γ.twoResidualAt cp.a')
    rw [←hmove,Γ.twoResidualAt_def,Γ.twoResidualAt_def]
    change _ = twoCoreIn (twoResidualIn (stabilizer Γ (Γ.act (mover:G) cp.firstStep)))
    rw [stabilizer_act,conjugateBy,twoResidualIn_map_equiv,twoCoreIn_map_equiv]
    rfl
  have hVmap : V.map f.toMonoidHom = Vt := by
    change _ = v Γ cp.a'
    rw [←hmove,v_act]
  have hZmap : Z.map f.toMonoidHom = Zt := by
    change _ = z Γ cp.a'
    rw [←hmove,z_act]
  have hUc : Nat.card Ut = Nat.card U := by
    rw [←hUmap]
    exact Subgroup.card_map_of_injective f.injective
  have hVc : Nat.card Vt = Nat.card V := by
    rw [←hVmap]
    exact Subgroup.card_map_of_injective f.injective
  have hZc : Nat.card Zt = Nat.card Z := by
    rw [←hZmap]
    exact Subgroup.card_map_of_injective f.injective
  have hshort : 1 < cp.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hZcard : Nat.card Zt = 2 :=
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
      hshort cp.a' ⟨alignment,halignment⟩).1
  have hVcard : Nat.card Vt = 32 :=
    (ten_one_large_terminal_structure ctx middle hpath hno).2.1
  refine ⟨?_,?_,?_⟩
  · change Nat.card V = 16 * Nat.card Z
    rw [←hVc,←hZc,hVcard,hZcard]
  · change Nat.card U = 16 * Nat.card V
    rw [←hUc,←hVc]
    exact ten_one_large_residual_quotient_card ctx middle hpath hno
  · change DerivedAmbient U = V
    rw [show DerivedAmbient U = ⁅U,U⁆ from Subgroup.map_subtype_commutator U]
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    rw [Subgroup.map_commutator,hUmap,hVmap]
    exact (Subgroup.map_subtype_commutator Ut).symm.trans
      (ten_one_large_terminal_residual_derived_eq ctx middle hpath hno)


public theorem ten_one_large_conclusion
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex) (W W0 Wnext : Subgroup G)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hW : W=conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
    (hWnext : Wnext=GeneratedNeighborhoodV ctx.Γ middle)
    (hW0 : W0=NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    AmbientLemmaTenOneConclusion ctx middle W W0 Wnext := by
  have hSylow := ten_one_large_sylow_card_bounds ctx middle hpath hno
  have hMiddleIndex := ten_one_large_middle_residual_join_index ctx middle hpath hno
  have hlarge := (ten_one_large_terminal_structure ctx middle hpath hno).2.2
  have hFrob := ten_one_large_first_frobenius ctx middle hpath hno
  obtain ⟨hzero,hnext,hnextZero,hderived⟩ := ten_one_large_common_index_chain
    ctx middle hpath W W0 Wnext hW hWnext hW0
    (ten_one_large_first_residual_index ctx middle hpath hno).1 hlarge hno hFrob
  refine ⟨⟨hW,hWnext,hW0⟩,⟨hzero,hnext⟩,hderived,?_⟩
  apply AmbientLemmaTenOneAlternative.b hSylow
    ⟨(sectionTenOpeningData ctx middle hpath).quotient_model,hFrob⟩
    (first_step_structure ctx middle hpath hno)
  refine ⟨(sectionTenOpeningData ctx middle hpath).center_card,?_,hnextZero,?_,?_⟩
  · rw [hW,hderived]
    exact (ten_one_large_neighborhood_action ctx middle hpath hno).1
  · rw [hWnext]
    exact hMiddleIndex
  · rw [hWnext]
    exact ten_one_large_derived_center_index ctx middle hpath hlarge hno
