module

public import Stellmacher.ExceptionalTypeRealization
public import Stellmacher.SectionEleven.SylowTerminalContext
public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Realizing the Section Ten Sylow terminal configuration

The exact case-(b) quotients have orders six and twenty. Their kernels are
two-cores, so the actual intersection at a+2 and a+1 is a two-group. Edge
conjugacy and the ambient Sylow in the original pair identify its image with
an ambient Sylow, not merely a Sylow of the graph group. Section Seven gives
generation by this edge, and hence its join has trivial two-core. The embedded
exceptional-type constructor preserves every supplied scan-correct case field.

The alternative centralizer obstruction is excluded using solvability of the
actual ambient two-locals. The multiple-maximal branch supplies these bridges
with the completed classification from `SectionTen.AmbientTenOne`. The global
Hypothesis Two stays on the original ambient group throughout.

Source: Stellmacher (10.1) and its following type definition, journal scan
printed pp. 59–65, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEleven

open Later SectionsFiveToSeven CosetGraphContext

universe u v

private theorem core_quotient_card
    {G : Type u} {X : Type v} [Group G] [Finite G] [Group X] [Finite X]
    (P : Subgroup G) (hmodel : QuotientIsModel P (twoCoreIn P) X) :
    ∃ exponent : ℕ, Nat.card P = 2 ^ exponent * Nat.card X := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨projection, hsurjective, hkernel⟩ := hmodel
  have hcore : (twoCoreIn P).subgroupOf P = pCore 2 P := by
    exact Subgroup.comap_map_eq_self (by simp)
  rw [hcore] at hkernel
  obtain ⟨exponent, hcard⟩ := (pCore_isPGroup (p := 2) (G := P)).exists_card_eq
  refine ⟨exponent, ?_⟩
  have hindex : (pCore 2 P).index = Nat.card X := by
    rw [← hkernel, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurjective,
      Subgroup.card_top]
  simpa only [hcard, hindex] using (pCore 2 P).card_mul_index.symm

public theorem ten_one_case_b_intersection_isPGroup
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext.{u,u} G S P1 P2) (path : CriticalPath graph)
    (next : graph.Vertex) (W W0 Wnext : Subgroup G)
    (hcase : TenOneCaseBTypeData graph path next W W0 Wnext) :
    IsPGroup 2 (GAt graph next ⊓ GAt graph path.firstStep : Subgroup G) := by
  have hnext := hcase.local_quotients.1
  change QuotientIsModel _ (graph.twoCoreAt next) _ at hnext
  rw [graph.twoCoreAt_def next] at hnext
  obtain ⟨leftExponent, hleft⟩ := core_quotient_card _ hnext
  have hsl : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  rw [hsl] at hleft
  obtain ⟨action, _, hfirst⟩ := hcase.local_quotients.2
  let : Finite (SemidirectProduct C5 C4 action) :=
    Finite.of_equiv (C5 × C4) SemidirectProduct.equivProd.symm
  change QuotientIsModel _ (graph.twoCoreAt path.firstStep) _ at hfirst
  rw [graph.twoCoreAt_def path.firstStep] at hfirst
  obtain ⟨rightExponent, hright⟩ := core_quotient_card _ hfirst
  have hfrobenius : Nat.card (SemidirectProduct C5 C4 action) = 20 := by
    rw [Nat.card_congr (SemidirectProduct.equivProd), Nat.card_prod]
    norm_num [C5, C4, Nat.card_zmod]
  rw [hfrobenius] at hright
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro prime hprime
  obtain ⟨hprime, hdivides, _⟩ := Nat.mem_primeFactors.mp hprime
  have hleftDivides := hdivides.trans
    (Subgroup.card_dvd_of_le (show GAt graph next ⊓ GAt graph path.firstStep ≤
      GAt graph next from inf_le_left))
  have hrightDivides := hdivides.trans
    (Subgroup.card_dvd_of_le (show GAt graph next ⊓ GAt graph path.firstStep ≤
      GAt graph path.firstStep from inf_le_right))
  rw [hleft] at hleftDivides
  rw [hright] at hrightDivides
  have heq : prime = 2 := by
    rcases hprime.dvd_mul.mp hleftDivides with htwo | hsix
    · exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
        (hprime.dvd_of_dvd_pow htwo)
    rcases hprime.dvd_mul.mp hrightDivides with htwo | htwenty
    · exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
        (hprime.dvd_of_dvd_pow htwo)
    have hgcd : prime ∣ 2 := by
      simpa using Nat.dvd_gcd hsix htwenty
    exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hgcd
  subst prime
  simpa using hprime

public theorem ten_one_offset_adjacent_firstStep
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : path.length = 3) (next : graph.Vertex)
    (hoffset : IsCriticalPathOffset graph path 2 next) :
    graph.adjacent next path.firstStep := by
  obtain ⟨index, hindex, rfl⟩ := hoffset
  have hfirst := path.path_adj ⟨1, by omega⟩
  have heq : (⟨1, by omega⟩ : Fin path.length).succ = index := Fin.ext hindex.symm
  rw [heq] at hfirst
  change graph.adjacent (path.path ⟨1, by omega⟩) (path.path index) at hfirst
  rw [path.path_first] at hfirst
  exact graph.adjacent_symm hfirst

public theorem ten_one_ambient_involution_centralizer_solvable
    {H G : Type u} [Group H] [Group G]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (element : G) (hinvolution : Later.IsInvolution element) :
    Group.IsSolvable (Subgroup.centralizer ({embedding element} : Set H)) := by
  by_contra hnot
  have hne : embedding element ≠ 1 := by
    intro heq
    exact hinvolution.1 (hinjective (heq.trans (map_one embedding).symm))
  have hpow : embedding element ^ 2 = 1 := by
    rw [← map_pow, hinvolution.2, map_one]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horder : orderOf (embedding element) = 2 := orderOf_eq_prime hpow hne
  obtain ⟨localGroup, hlocal, hnonsolvable⟩ :=
    Theory.GroupTheory.exists_nonsolvable_twoLocal_of_involution_centralizer horder hnot
  exact hnonsolvable (hLocal localGroup hlocal).1

public theorem multiple_ten_one_of_case_b
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (next : ctx.Γ.Vertex)
    (W W0 Wnext : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hcase : TenOneCaseBTypeData ctx.Γ ctx.criticalPath next W W0 Wnext) :
    IsOfTwistedF4TwoDerivedType H := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let joinGroup := P1 ⊔ P2
  let first := P1.subgroupOf joinGroup
  let second := P2.subgroupOf joinGroup
  have hadj := ten_one_offset_adjacent_firstStep graph path hcase.critical_length
    next hcase.path_offset
  have htwo := ten_one_case_b_intersection_isPGroup graph path next W W0 Wnext hcase
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven graph).edge_stabilizers_conjugate
    next path.firstStep hadj
  have hbaseTwo : IsPGroup 2 (first ⊓ second : Subgroup joinGroup) := by
    change IsPGroup 2 (graph.stabilizer next ⊓ graph.stabilizer path.firstStep :
      Subgroup joinGroup) at htwo
    rw [hactor] at htwo
    exact htwo.of_equiv ((MulAut.conj actor).subgroupMap (first ⊓ second)).symm
  have hbaseMap : (first ⊓ second).map joinGroup.subtype = P1 ⊓ P2 := by
    rw [Subgroup.map_inf _ _ _ joinGroup.subtype_injective]
    rw [Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right]
  have hambientTwo : IsPGroup 2 (P1 ⊓ P2 : Subgroup H) := by
    rw [← hbaseMap]
    exact hbaseTwo.map joinGroup.subtype
  have hbaseSylow : P1 ⊓ P2 = (S0 : Subgroup H) :=
    S0.is_maximal' hambientTwo (le_inf
      ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
      ctx.hypothesisTwo.fiveOne.P2_mem.1.2.1.1)
  have hmapConj : joinGroup.subtype.comp (MulAut.conj actor).toMonoidHom =
      (MulAut.conj (actor : H)).toMonoidHom.comp joinGroup.subtype := by
    ext element
    rfl
  have hintersection :
      (GAt graph next ⊓ GAt graph path.firstStep).map joinGroup.subtype =
        (((actor : H) • S0 : Sylow 2 H) : Subgroup H) := by
    change (graph.stabilizer next ⊓ graph.stabilizer path.firstStep).map _ = _
    rw [hactor]
    change ((first ⊓ second).map (MulAut.conj actor).toMonoidHom).map _ = _
    rw [Subgroup.map_map, hmapConj, ← Subgroup.map_map, hbaseMap, hbaseSylow]
    rfl
  have hneighbor : path.firstStep ∈ graph.neighborhood next :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr hadj
  have hgenerate : GAt graph next ⊔ GAt graph path.firstStep = ⊤ :=
    (edge_sectionThree_data ctx.sectionSeven graph hneighbor
      (default : Sylow 2 (↥(graph.stabilizer next ⊓
        graph.stabilizer path.firstStep)))).2.2.2.2.1
  have hcore : pCore 2 (↥(GAt graph next ⊔ GAt graph path.firstStep)) = ⊥ := by
    rw [hgenerate]
    let equiv : (⊤ : Subgroup joinGroup) ≃* joinGroup := Subgroup.topEquiv
    apply (Subgroup.map_eq_bot_iff_of_injective _ (f := equiv.toMonoidHom)
      equiv.injective).mp
    rw [pCore_map_iso, ctx.sectionSeven.twoCore_eq_bot]
  exact isOfTwistedF4TwoDerivedType_of_embedded_caseB joinGroup.subtype
    joinGroup.subtype_injective ((actor : H) • S0) graph path next W W0 Wnext
    hintersection hcore hcase

public theorem multiple_ten_one_of_terminal_alternative
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hterminal :
      (∃ next : ctx.Γ.Vertex, ∃ W W0 Wnext : Subgroup (P1 ⊔ P2 : Subgroup H),
        TenOneCaseBTypeData ctx.Γ ctx.criticalPath next W W0 Wnext) ∨
      (∃ element : (P1 ⊔ P2 : Subgroup H), Later.IsInvolution element ∧
        ¬ Group.IsSolvable (Subgroup.centralizer ({(element : H)} : Set H)))) :
    IsOfTwistedF4TwoDerivedType H := by
  rcases hterminal with ⟨next, W, W0, Wnext, hcase⟩ | ⟨element, hinvolution, hnot⟩
  · exact multiple_ten_one_of_case_b ctx next W W0 Wnext hcase
  · exact (hnot (ten_one_ambient_involution_centralizer_solvable (P1 ⊔ P2).subtype
      Subtype.val_injective hLocal element hinvolution)).elim

end Stellmacher.SectionEleven
