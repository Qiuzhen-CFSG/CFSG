module

public import Stellmacher.SectionEight.GeneratedEightSixQuotientTwoGenerators
public import Stellmacher.SectionEight.GeneratedEightSixEquationOneSetup
public import Stellmacher.SectionFiveToSeven.Result7_5

/-!
# Order four in the small-index branch of (8.6)

Local transitivity transports the predecessor's index two to the first-step
intersection. The equation-one generation gives a quotient of order two or
four. The first-step core normalizes both the kernel and the generated core,
so an order-two quotient would have trivial action, contradicting the
equation-one commutator identity and transported noncontainment.

Source: Stellmacher, printed p.42, paragraph between (5) and (6), using (1)
on printed p.41. The generated context retains Hypothesis Two on the ambient
group; equality with the initial vertex core is not used.
The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

set_option linter.unusedVariables false in
public theorem eight_six_small_index_quotient_four_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : Later.SectionEightLocalContext G S P1 P2)
    (_hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (_hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (_hlength : ctx.criticalPath.length = 2)
    (_hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    QuotientCardEq Q D 4 := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let A := VAt graph previous ⊓ QAt graph path.a
  let B := VAt graph path.firstStep ⊓ QAt graph path.a
  let R := QAt graph path.firstStep
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one ctx.sectionSeven graph).local_transitivity path.a hprev.1
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj)
  let transport := MulAut.conj (actor : G)⁻¹
  have hVmap : (VAt graph previous).map transport.toMonoidHom =
      VAt graph path.firstStep := by
    rw [← hactor]
    exact (v_act graph actor previous).symm
  have hQmap : (QAt graph path.a).map transport.toMonoidHom = QAt graph path.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (QAt graph path.a : Set G)).inv_mem
        (SevenSix.stabilizer_le_normalizer_q graph path.a actor.property))
  have hAmap : A.map transport.toMonoidHom = B := by
    dsimp only [A, B]
    rw [Subgroup.map_inf _ _ _ transport.injective, hVmap, hQmap]
  have hDnorm : GAt graph path.a ≤ Subgroup.normalizer (D : Set _) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer data.intersection_normal.1).mp
      data.intersection_normal.2
  have hDmap : D.map transport.toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (D : Set G)).inv_mem
        (hDnorm actor.property))
  have hgen : Q = A ⊔ B ⊔ D := by simpa [A, B] using data.core_generation
  have hRedge : R ≤ GAt graph path.a := by
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path).2.trans
      (path.S_le_edge_stabilizers.trans inf_le_left)
  have hLnorm : GAt graph path.a ≤ Subgroup.normalizer (L : Set _) := by
    rw [hdefs.2.1]
    exact eight_six_conjugate_closure_normalizer _ _
  have hQle : Q ≤ GAt graph path.a := by
    rw [hdefs.2.2.1]
    exact (SevenSix.twoCoreIn_le L).trans data.closure_le
  have hQnorm : GAt graph path.a ≤ Subgroup.normalizer (Q : Set _) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mp
    rw [hdefs.2.2.1]
    exact SevenSix.twoCoreIn_normal_of_normal L _ data.closure_le
      (Subgroup.normal_subgroupOf_of_le_normalizer hLnorm)
  have hRQ : R ≤ Subgroup.normalizer (Q : Set _) := hRedge.trans hQnorm
  have hRD : R ≤ Subgroup.normalizer (D : Set _) := hRedge.trans hDnorm
  apply quotient_two_generators_card_four_of_normalizes A B D Q R hgen hbase.2.1
    hindex transport hAmap hDmap data.core_commutator hRQ hRD

public theorem generated_eight_six_small_index_quotient_four
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : Later.GeneratedSectionEightContext H S0 S P1 P2)
    (_hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (_hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (_hlength : ctx.criticalPath.length = 2)
    (_hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    QuotientCardEq Q D 4 := by
  exact eight_six_small_index_quotient_four_local ctx.toLocalContext
    _hcenter _hquot _hlength _hcard previous D L Q T hprev hdefs hbase hindex data

end Stellmacher.SectionEight
