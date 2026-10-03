module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionNine.NineSixSmallModule

/-!
# Independent inputs for the order-eight bridge in Stellmacher (9.7)

Endpoint alignment transports the first-step module cardinality and every
literal core quotient model to the terminal vertex. Criticality supplies an
involutory actor outside the terminal core. The penultimate core normalizes
the intersection of its two neighboring modules. Finally, the given
index-two module intersection equals the first-step intersection with the
terminal core, by critical minimality and the finite subgroup order formula.

These results use only the genuine local Section Nine context. They do not
assert the terminal order-eight classification, which still requires the
ambient (9.3), (9.5), and transvection/centralizer argument. Hypothesis Two
is never transferred from the ambient group to the graph group.

Source: `refs/files/stellmacher-n-group.pdf`, printed p.53 / PDF p.43,
the first paragraph of the proof of (9.7).
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u w

private theorem quotient_model_act
    {G : Type u} {M : Type w} [Group G] [Finite G] [Group M]
    {T A B : Subgroup G} (Γ : CosetGraphContext G T A B)
    (actor : G) (vertex : Γ.Vertex)
    (hmodel : QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) M) :
    QuotientIsModel (GAt Γ (Γ.act actor vertex)) (QAt Γ (Γ.act actor vertex)) M := by
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  change QuotientIsModel (stabilizer Γ (Γ.act actor vertex))
    (q Γ (Γ.act actor vertex)) M
  rw [stabilizer_act, SevenSix.q_act]
  let equiv := (GAt Γ vertex).equivMapOfInjective
    (MulAut.conj actor⁻¹).toMonoidHom (MulAut.conj actor⁻¹).injective
  refine ⟨projection.comp equiv.symm.toMonoidHom,
    hsurj.comp equiv.symm.surjective, ?_⟩
  ext point
  change projection (equiv.symm point) = 1 ↔
    (point : G) ∈ (QAt Γ vertex).map (MulAut.conj actor⁻¹).toMonoidHom
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_map_equiv]
  have heq : (equiv.symm point : G) = (MulAut.conj actor⁻¹).symm (point : G) := by
    apply (MulAut.conj actor⁻¹).injective
    change (equiv (equiv.symm point) : G) = _
    simp only [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val (equiv.apply_symm_apply point)
  change (equiv.symm point : G) ∈ QAt Γ vertex ↔ _
  rw [heq]

public theorem nine_seven_endpoint_module_card
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) =
      Nat.card (VAt ctx.Γ ctx.criticalPath.a') := by
  obtain ⟨actor, _, hactor⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hmodule : (VAt ctx.Γ ctx.criticalPath.firstStep).map
      (MulAut.conj actor⁻¹).toMonoidHom = VAt ctx.Γ ctx.criticalPath.a' := by
    rw [← v_act ctx.Γ actor, hactor]
  rw [← hmodule, Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective]

public theorem nine_seven_endpoint_quotient_model_iff
    {G : Type u} {M : Type w} [Group G] [Finite G] [Group M] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep) M ↔
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
        (QAt ctx.Γ ctx.criticalPath.a') M := by
  obtain ⟨actor, _, hactor⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  constructor
  · intro hmodel
    simpa only [hactor] using
      quotient_model_act ctx.Γ actor ctx.criticalPath.firstStep hmodel
  · intro hmodel
    have hinverse : ctx.Γ.act actor⁻¹ ctx.criticalPath.a' =
        ctx.criticalPath.firstStep := by
      rw [← hactor, ← ctx.Γ.act_mul, mul_inv_cancel, ctx.Γ.act_one]
    simpa only [hinverse] using
      quotient_model_act ctx.Γ actor⁻¹ ctx.criticalPath.a' hmodel

public theorem nine_seven_exists_actor
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) :
    ∃ actor : G,
      actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
      CosetGraphContext.IsInvolution actor := by
  have hnot : ¬ VAt ctx.Γ ctx.criticalPath.firstStep ≤
      QAt ctx.Γ ctx.criticalPath.a' := by
    intro hle
    exact ctx.criticalPath.critical.2
      ((lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1.trans hle)
  obtain ⟨actor, hmem, houtside⟩ := Set.not_subset.mp hnot
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb).1
  refine ⟨actor, hmem, houtside, ?_, elemPow_eq_one_of_isElementaryAbelian actor hmem⟩
  intro hone
  exact houtside (hone ▸ (QAt ctx.Γ ctx.criticalPath.a').one_mem)

public theorem nine_seven_terminal_intersection_normalized
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (previous : ctx.Γ.Vertex)
    (hprevious : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) previous) :
    QAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
      Subgroup.normalizer
        (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ previous : Set G) := by
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hterminal : ctx.Γ.adjacent penultimate cp.a' := by
    have hadj := cp.path_adj ⟨cp.length - 1, by dsimp [cp]; omega⟩
    have heq : (⟨cp.length - 1, by dsimp [cp]; omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [cp]
      omega
    rw [heq, cp.path_end] at hadj
    exact hadj
  have hprior : ctx.Γ.adjacent penultimate previous := by
    obtain ⟨index, hindex, rfl⟩ := hprevious
    have hadj := cp.path_adj ⟨cp.length - 2, by dsimp [cp]; omega⟩
    have hleft : (⟨cp.length - 2, by dsimp [cp]; omega⟩ : Fin cp.length).castSucc =
        index := Fin.ext hindex.symm
    have hright : (⟨cp.length - 2, by dsimp [cp]; omega⟩ : Fin cp.length).succ =
        ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [cp]
      omega
    rw [hleft, hright] at hadj
    exact ctx.Γ.adjacent_symm hadj
  have hnormalize (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent penultimate vertex) :
      QAt ctx.Γ penultimate ≤ Subgroup.normalizer (VAt ctx.Γ vertex : Set G) := by
    have hcore := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
      penultimate vertex ((SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
      default).2.2
    exact hcore.trans (stabilizer_le_normalizer_v ctx.Γ vertex)
  exact (le_inf (hnormalize cp.a' hterminal) (hnormalize previous hprior)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

public theorem nine_seven_first_core_intersection
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third =
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a' := by
  let initial := VAt ctx.Γ ctx.criticalPath.firstStep
  let common := initial ⊓ VAt ctx.Γ third
  let coreSlice := initial ⊓ QAt ctx.Γ ctx.criticalPath.a'
  have hle : common ≤ coreSlice := inf_le_inf_left initial
    (nine_six_third_module_le_terminal_core ctx third hpath)
  have hproper : coreSlice ≠ initial := by
    intro heq
    have hcontain : initial ≤ QAt ctx.Γ ctx.criticalPath.a' := heq.ge.trans inf_le_right
    exact ctx.criticalPath.critical.2
      ((lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1.trans
        hcontain)
  have hcardlt : Nat.card coreSlice < Nat.card initial := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le (show coreSlice ≤ initial from inf_le_left))
    intro heq
    exact hproper (Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge)
  obtain ⟨factor, hfactor⟩ := Subgroup.card_dvd_of_le
    (show coreSlice ≤ initial from inf_le_left)
  have hfactor_ge : 2 ≤ factor := by nlinarith
  have hindex' : Nat.card initial = 2 * Nat.card common := hindex
  have hcardle : Nat.card coreSlice ≤ Nat.card common := by nlinarith
  exact Subgroup.eq_of_le_of_card_ge hle hcardle

end Stellmacher.SectionNine
