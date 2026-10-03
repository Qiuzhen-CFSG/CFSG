module
public import Stellmacher.SectionEight.EightFourSylowInvariantFixed
public import Stellmacher.SectionEight.EightFourSourceNineCentralizerSize

/-!
# The terminal invariant containment reduced to actual core generation

The original source-nine data and its proved cardinalities suffice for the
last invariant-subgroup argument once the distinguished Sylow is generated
by the initial two neighboring cores. This theorem deliberately exposes
that one prerequisite; it is not the unconditional terminal theorem.

The local theorem keeps the same graph, quotient witness and source-nine
data; the original canonical API is an exact fieldwise-data wrapper.
At the actual transported edge, one core centralizes the shifted center
and the other normalizes both endpoint centers by adjacency. Their join
preserves the endpoint intersection. Pulling this subgroup back to the
original center permits use of the original quotient witness, its proved
fixed order four, and the proved intersection lower bound. No replacement
witness or normalization of a whole center by an adjacent stabilizer is
asserted. Source: Stellmacher (8.4), printed p.40/PDF p.30, final paragraph
of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

section LocalProof
variable {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

include hcenter w hbranch hbase hcov hsub hformula configuration hlen

public theorem eight_four_source_nine_terminal_invariant_of_core_generation_local
    (hgeneration : S = QAt ctx.Γ ctx.criticalPath.a ⊔
      QAt ctx.Γ ctx.criticalPath.firstStep) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    F next configuration.d ≤
      ZAt ctx.Γ ctx.criticalPath.a' ⊓ ZAt ctx.Γ next := by
  classical
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let next := graph.act configuration.y⁻¹ path.a'
  let intersection := ZAt graph path.a' ⊓ ZAt graph next
  let hyp := ctx.sectionSeven
  have hpos := path.length_pos
  have hprevious : graph.adjacent path.a' (path.path ⟨path.length - 1, by omega⟩) := by
    have hedge := path.path_adj ⟨path.length - 1, by omega⟩
    have hindex : (⟨path.length - 1, by omega⟩ : Fin path.length).succ =
        ⟨path.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hindex, path.path_end] at hedge
    exact graph.adjacent_symm hedge
  have hfix : graph.act configuration.x⁻¹ path.a' = path.a' := by
    have hmem := (GAt graph path.a').inv_mem (configuration.hL0 configuration.hx)
    change configuration.x⁻¹ ∈ (graph.vertexStabilizer path.a' : Set H) at hmem
    rwa [graph.stabilizer_def] at hmem
  have hmiddle : graph.adjacent path.a' configuration.d := by
    have hedge := adjacent_act graph configuration.x⁻¹ hprevious
    rwa [hfix, ← configuration.hd] at hedge
  have hcoreEnd : QAt graph configuration.d ≤ GAt graph path.a' :=
    ((lemma_seven_three hyp graph).sylow_and_core configuration.d path.a'
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr
        (graph.adjacent_symm hmiddle)) default).2.2
  have hcoreNext : QAt graph configuration.d ≤ GAt graph next :=
    ((lemma_seven_three hyp graph).sylow_and_core configuration.d next
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr configuration.hadj) default).2.2
  have hcoreNormalize : QAt graph configuration.d ≤
      Subgroup.normalizer (intersection : Set H) :=
    (le_inf (hcoreEnd.trans (stabilizer_le_normalizer_z graph path.a'))
      (hcoreNext.trans (stabilizer_le_normalizer_z graph next))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hnextCentral : QAt graph next ≤
      Subgroup.centralizer (ZAt graph next : Set H) := by
    rw [Subgroup.le_centralizer_iff]
    exact ((lemma_seven_three hyp graph).center_core next configuration.d
      ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr
        (graph.adjacent_symm configuration.hadj))).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))
  have hnextNormalize : QAt graph next ≤ Subgroup.normalizer (intersection : Set H) :=
    (hnextCentral.trans (Subgroup.centralizer_le
      (show intersection ≤ ZAt graph next from inf_le_right))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hnormalize : QAt graph next ⊔ QAt graph configuration.d ≤
      Subgroup.normalizer (intersection : Set H) := sup_le hnextNormalize hcoreNormalize
  have hfixedCard : Nat.card (F next configuration.d) = 4 :=
    eight_four_source_nine_shifted_fixed_card_four_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen
  have hnonzero : F next configuration.d ≠ ⊥ := by
    intro heq
    have hone := Subgroup.card_eq_one.mpr heq
    omega
  obtain ⟨actor, horient⟩ : ∃ actor : H,
      graph.act actor path.a = next ∧ graph.act actor path.firstStep = configuration.d := by
    by_contra hnone
    apply hnonzero
    rw [hformula next configuration.d]
    apply le_bot_iff.mp
    exact iSup_le fun actor => iSup_le fun horient => (hnone ⟨actor, horient⟩).elim
  have hfixedTransport := hcov actor path.a path.firstStep
  rw [horient.1, horient.2, hbase] at hfixedTransport
  have hcenterTransport := z_act graph actor path.a
  rw [horient.1] at hcenterTransport
  change ZAt graph next = (ZAt graph path.a).conjBy actor⁻¹ at hcenterTransport
  have hcoreTransport := SevenSix.q_act graph actor path.a
  rw [horient.1] at hcoreTransport
  have hotherCoreTransport := SevenSix.q_act graph actor path.firstStep
  rw [horient.2] at hotherCoreTransport
  change QAt graph next = (QAt graph path.a).map
    (MulAut.conj actor⁻¹).toMonoidHom at hcoreTransport
  change QAt graph configuration.d = (QAt graph path.firstStep).map
    (MulAut.conj actor⁻¹).toMonoidHom at hotherCoreTransport
  have hSylowTransport : S.conjBy actor⁻¹ =
      QAt graph next ⊔ QAt graph configuration.d := by
    calc
      S.conjBy actor⁻¹ = (QAt graph path.a ⊔ QAt graph path.firstStep).conjBy actor⁻¹ :=
        congrArg (fun subgroup : Subgroup H => subgroup.conjBy actor⁻¹) hgeneration
      _ = _ := by
        change (QAt graph path.a ⊔ QAt graph path.firstStep).map
          (MulAut.conj actor⁻¹).toMonoidHom = _
        rw [Subgroup.map_sup, ← hcoreTransport, ← hotherCoreTransport]
  let pulled := intersection.conjBy actor
  have hpulledLe : pulled ≤ ZAt graph path.a := by
    have hmap := Subgroup.map_mono
      (show intersection ≤ ZAt graph next from inf_le_right)
      (f := (MulAut.conj actor).toMonoidHom)
    rw [hcenterTransport] at hmap
    change pulled ≤ ((ZAt graph path.a).conjBy actor⁻¹).conjBy actor at hmap
    simpa only [Subgroup.conjBy_inv'] using hmap
  have hpulledNormalize : S ≤ Subgroup.normalizer (pulled : Set H) := by
    rw [← hSylowTransport] at hnormalize
    have hmap := (Subgroup.map_mono hnormalize
      (f := (MulAut.conj actor).toMonoidHom)).trans
      (Subgroup.le_normalizer_map (MulAut.conj actor).toMonoidHom)
    change (S.conjBy actor⁻¹).conjBy actor ≤ Subgroup.normalizer (pulled : Set H) at hmap
    simpa only [Subgroup.conjBy_inv'] using hmap
  have hpulledCard : Nat.card (w.oneJFixedPoints S) ≤ Nat.card pulled := by
    rw [eight_four_source_nine_fixed_card_four_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen]
    change 4 ≤ Nat.card (intersection.map (MulAut.conj actor).toMonoidHom)
    rw [Subgroup.card_map_of_injective (MulAut.conj actor).injective]
    exact eight_four_source_nine_endpoint_intersection_card_ge_four_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen
  have hcontains := eight_four_sylow_invariant_contains_fixed_local ctx hcenter w
    pulled hpulledLe hpulledNormalize hpulledCard
  have hmap := Subgroup.map_mono hcontains (f := (MulAut.conj actor⁻¹).toMonoidHom)
  change (w.oneJFixedPoints S).conjBy actor⁻¹ ≤
    (intersection.conjBy actor).conjBy actor⁻¹ at hmap
  rw [Subgroup.conjBy_inv, ← hfixedTransport] at hmap
  exact hmap

end LocalProof

section CanonicalProof
variable {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

include hcenter w hbranch hbase hcov hsub hformula configuration hlen

public theorem eight_four_source_nine_terminal_invariant_of_core_generation
    (hgeneration : S = QAt ctx.Γ ctx.criticalPath.a ⊔
      QAt ctx.Γ ctx.criticalPath.firstStep) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    F next configuration.d ≤
      ZAt ctx.Γ ctx.criticalPath.a' ⊓ ZAt ctx.Γ next  := by
  exact eight_four_source_nine_terminal_invariant_of_core_generation_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula
    configuration.toLocal hlen hgeneration
end CanonicalProof

end Stellmacher.SectionEight
