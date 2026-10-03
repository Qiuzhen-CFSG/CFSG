module

public import Stellmacher.SectionNine.NineTwoCommutatorCenter
public import Stellmacher.SectionNine.NineTwoCoreNoncontainment
public import Stellmacher.SectionNine.NineTwoRankOneClassification

/-!
# Stellmacher (9.2): the local quotient and center of a generating neighbor

Under the two-neighbor index and generation hypotheses, the indicated vertex
stabilizer modulo its ordinary two-core is SL₂(2), and its center module has
order four. The ambient version retains Hypothesis Two on H even when the
coset graph is formed in a generated subgroup G. The original theorem is its
specialization through the existing ambient-context adapter.

First align the terminal vertex orbit using (7.5), then use local transitivity
to move the requested edge to the normalized initial edge. Conjugation
transports both index and generation, together with the exact cores and
centers. In the normalized configuration, (7.6) and equal cardinalities of
conjugate core intersections give the corrected core noncontainment. The
proved canonical (6.4) forces the relevant commutator into the next center.
The original (1.7) support decomposition then makes the whole initial center
have order four. The faithful action and residual-centralizer argument
identify its kernel with the ordinary two-core, yielding the required SL₂(2)
quotient. Finally transport that literal quotient and cardinality back.

Source: B. Stellmacher, Journal of Algebra 190 (1997), (9.2), printed p.48 /
PDF p.38 of `refs/files/stellmacher-n-group.pdf`. The full scan supplies the
core noncontainment negation omitted by the abbreviated transcription.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem quotientIsModel_map
    {G : Type u} [Group G] {A B : Subgroup G}
    (equiv : G ≃* G) (hmodel : QuotientIsModel A B SL2Two) :
    QuotientIsModel (A.map equiv.toMonoidHom) (B.map equiv.toMonoidHom) SL2Two := by
  obtain ⟨projection, hsurjective, hkernel⟩ := hmodel
  let localEquiv := A.equivMapOfInjective equiv.toMonoidHom equiv.injective
  refine ⟨projection.comp localEquiv.symm.toMonoidHom,
    hsurjective.comp localEquiv.symm.surjective, ?_⟩
  ext point
  change projection (localEquiv.symm point) = 1 ↔
    (point : G) ∈ B.map equiv.toMonoidHom
  rw [← MonoidHom.mem_ker, hkernel, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv]
  have hcoe : ((localEquiv.symm point : A) : G) = equiv.symm (point : G) := by
    apply equiv.injective
    rw [equiv.apply_symm_apply]
    calc
      equiv ((localEquiv.symm point : A) : G) =
          (localEquiv (localEquiv.symm point) : G) :=
        (Subgroup.coe_equivMapOfInjective_apply A equiv.toMonoidHom
          equiv.injective (localEquiv.symm point)).symm
      _ = (point : G) := congrArg Subtype.val (localEquiv.apply_symm_apply point)
  rw [hcoe]

private theorem ambient_nine_two_of_normalized
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlocal : ∀ m : ctx.Γ.Vertex, m ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep →
      QuotientCardEq (ZAt ctx.Γ ctx.criticalPath.a)
        (ZAt ctx.Γ ctx.criticalPath.a ⊓ ZAt ctx.Γ m) 2 →
      QAt ctx.Γ m ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
        GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep →
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a) (QAt ctx.Γ ctx.criticalPath.a)
        SL2Two ∧ Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (d l m : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a' d)
    (hl : l ∈ Neighborhood ctx.Γ d) (hm : m ∈ Neighborhood ctx.Γ d)
    (hindex : QuotientCardEq (ZAt ctx.Γ l) (ZAt ctx.Γ l ⊓ ZAt ctx.Γ m) 2)
    (hgenerate : QAt ctx.Γ m ⊔ (GAt ctx.Γ l ⊓ GAt ctx.Γ d) = GAt ctx.Γ d) :
    QuotientIsModel (GAt ctx.Γ l) (QAt ctx.Γ l) SL2Two ∧
      Nat.card (ZAt ctx.Γ l) = 4 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  obtain ⟨alignment, _, hstep⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨endpoint, hendpoint⟩ := hd
  let initial := alignment * endpoint
  have hinitial : Γ.act initial cp.firstStep = d := by
    change Γ.act (alignment * endpoint) cp.firstStep = d
    rw [Γ.act_mul, hstep]
    exact hendpoint
  have hneighbor : Γ.act initial cp.a ∈ neighborhood Γ d := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    rw [← hinitial]
    exact adjacent_act Γ initial (Γ.adjacent_symm cp.firstStep_adj)
  obtain ⟨correction, hcorrection⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    d hneighbor hl
  have hfix : Γ.act (correction : G) d = d := by
    exact (Set.ext_iff.mp (Γ.stabilizer_def d) (correction : G)).mp correction.property
  let actor := initial * (correction : G)
  have hleft : Γ.act actor cp.a = l := by
    change Γ.act (initial * (correction : G)) cp.a = l
    rw [Γ.act_mul]
    exact hcorrection
  have hright : Γ.act actor cp.firstStep = d := by
    change Γ.act (initial * (correction : G)) cp.firstStep = d
    rw [Γ.act_mul, hinitial, hfix]
  let neighbor := Γ.act actor⁻¹ m
  have hneighbor_act : Γ.act actor neighbor = m := by
    change Γ.act actor (Γ.act actor⁻¹ m) = m
    rw [← Γ.act_mul, inv_mul_cancel, Γ.act_one]
  have hnext : Γ.act actor⁻¹ d = cp.firstStep := by
    rw [← hright, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
  have hneighbor_mem : neighbor ∈ Neighborhood Γ cp.firstStep := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    rw [← hnext]
    exact adjacent_act Γ actor⁻¹ ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hm)
  let conjugation := MulAut.conj actor⁻¹
  have hZa : (ZAt Γ cp.a).map conjugation.toMonoidHom = ZAt Γ l := by
    rw [← z_act Γ actor, hleft]
  have hZm : (ZAt Γ neighbor).map conjugation.toMonoidHom = ZAt Γ m := by
    rw [← z_act Γ actor, hneighbor_act]
  have hQa : (QAt Γ cp.a).map conjugation.toMonoidHom = QAt Γ l := by
    rw [← SevenSix.q_act Γ actor, hleft]
  have hQm : (QAt Γ neighbor).map conjugation.toMonoidHom = QAt Γ m := by
    rw [← SevenSix.q_act Γ actor, hneighbor_act]
  have hGa : (GAt Γ cp.a).map conjugation.toMonoidHom = GAt Γ l := by
    change conjugateBy (stabilizer Γ cp.a) actor⁻¹ = stabilizer Γ l
    rw [← stabilizer_act Γ actor, hleft]
  have hGnext : (GAt Γ cp.firstStep).map conjugation.toMonoidHom = GAt Γ d := by
    change conjugateBy (stabilizer Γ cp.firstStep) actor⁻¹ = stabilizer Γ d
    rw [← stabilizer_act Γ actor, hright]
  have hindex_local : QuotientCardEq (ZAt Γ cp.a) (ZAt Γ cp.a ⊓ ZAt Γ neighbor) 2 := by
    unfold QuotientCardEq at hindex ⊢
    rw [← hZa, ← hZm, ← Subgroup.map_inf _ _ _ conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective] at hindex
    exact hindex
  have hgenerate_local : QAt Γ neighbor ⊔ (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) =
      GAt Γ cp.firstStep := by
    apply (Subgroup.map_injective (f := conjugation.toMonoidHom) conjugation.injective)
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ conjugation.injective,
      hQm, hGa, hGnext]
    exact hgenerate
  obtain ⟨hmodel, hcard⟩ := hlocal neighbor hneighbor_mem hindex_local hgenerate_local
  constructor
  · have htransport := quotientIsModel_map conjugation hmodel
    rwa [hGa, hQa] at htransport
  · rw [← hZa, Subgroup.card_map_of_injective conjugation.injective]
    exact hcard


/-- **Stellmacher (9.2)** with Hypothesis Two retained on the ambient group. -/
public theorem lemma_nine_two_ambient
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (d l m : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a' d)
    (hl : l ∈ Neighborhood ctx.Γ d)
    (hm : m ∈ Neighborhood ctx.Γ d)
    (hindex : QuotientCardEq
      (ZAt ctx.Γ l) (ZAt ctx.Γ l ⊓ ZAt ctx.Γ m) 2)
    (hgenerate : QAt ctx.Γ m ⊔
      (GAt ctx.Γ l ⊓ GAt ctx.Γ d) = GAt ctx.Γ d) :
    QuotientIsModel (GAt ctx.Γ l) (QAt ctx.Γ l) SL2Two ∧
      Nat.card (ZAt ctx.Γ l) = 4 := by
  apply ambient_nine_two_of_normalized ctx ?_ d l m hd hl hm hindex hgenerate
  intro neighbor hneighbor hidx hgen
  have hnot := nine_two_core_noncontainment ctx.sectionSeven ctx.Γ ctx.criticalPath
    neighbor hneighbor hgen
  have hcomm := nine_two_commutator_center ctx neighbor hneighbor hidx hgen hnot
  exact nine_two_rank_one_classification ctx neighbor hneighbor hidx hgen hnot hcomm


/-- **Stellmacher (9.2).**  The local quotient and center order conclusion
under the stated two-neighbor hypotheses. -/
public theorem lemma_nine_two
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (d l m : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a' d)
    (hl : l ∈ Neighborhood ctx.Γ d)
    (hm : m ∈ Neighborhood ctx.Γ d)
    (hindex : QuotientCardEq
      (ZAt ctx.Γ l) (ZAt ctx.Γ l ⊓ ZAt ctx.Γ m) 2)
    (hgenerate : QAt ctx.Γ m ⊔
      (GAt ctx.Γ l ⊓ GAt ctx.Γ d) = GAt ctx.Γ d) :
    QuotientIsModel (GAt ctx.Γ l) (QAt ctx.Γ l) SL2Two ∧
      Nat.card (ZAt ctx.Γ l) = 4 := by
  exact lemma_nine_two_ambient ctx.toAmbientContext d l m hd hl hm hindex hgenerate

end Stellmacher.SectionNine
