module
public import Theory.GroupTheory.GreatestCommutatorSubgroup
public import Theory.GroupTheory.WreathQuotientSylowControl
public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionNine.DistanceOneCenterIntersection
public import Stellmacher.SectionNine.DistanceOneExtraction
public import Stellmacher.SectionNine.DistanceOneProductCore
public import Stellmacher.SectionNine.DistanceOneAdmissibleSeed
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_4
public import Stellmacher.SectionThree.LemmaThreeFour
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The maximal distance-one subgroup and relation (9)

For the actual length-one extraction, assume its coatom identification,
faithful wreath quotient, source relations (3)–(4), and the final
intersection identity in (8). The admissible-seed theorem supplies a
subgroup with the two exact commutator equations. Join closure and
finiteness give a greatest such subgroup U of the neighboring core.
The edge Sylow normalizes all three defining parameters, so it normalizes
U; the seed's size and noncontainment properties pass to U.

The extracted product lies in the neighboring core. Hence it commutes
with U on the faithful quotient of the starting stabilizer. The concrete
wreath Sylow-centralizer bound pulls back through the actual Sylow-kernel
intersection, yielding U≤V∨Qa and the action bound of index at most four.
Noncontainment in Qa gives a nontrivial action, and (3.4) gives [Ea,U]=Ea.
The result is the full maximal-subgroup construction through relation (9),
with no seed or later core equality among its hypotheses.

Source: Stellmacher, N-group paper (1997), proof of (9.1), journal pp.46–47,
`refs/files/stellmacher-n-group.pdf`. The subsequent chief-factor argument
and the actual production of the listed source hypotheses are separate.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext
open Stellmacher.SectionsFiveToSeven.SevenSix
open scoped commutatorElement
universe u



private theorem distance_one_greatest_from_seed
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (V seed : Subgroup G)
    (hseedQ : seed ≤ q ctx.Γ ctx.criticalPath.a')
    (hseedQcomm : ⁅seed, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a')
    (hseedEcomm : ⁅seed, e ctx.Γ ctx.criticalPath.a'⁆ = seed)
    (hseedcard : 8 ≤ Nat.card (seed ⊓ V : Subgroup G))
    (hseednot : ¬ seed ≤ q ctx.Γ ctx.criticalPath.a) :
    ∃ U : Subgroup G,
      U ≤ q ctx.Γ ctx.criticalPath.a' ∧
      ⁅U, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a' ∧
      ⁅U, e ctx.Γ ctx.criticalPath.a'⁆ = U ∧
      (∀ W : Subgroup G, W ≤ q ctx.Γ ctx.criticalPath.a' →
        ⁅W, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a' →
        ⁅W, e ctx.Γ ctx.criticalPath.a'⁆ = W → W ≤ U) ∧
      U ≤ T ∧ (U.subgroupOf T).Normal ∧
      8 ≤ Nat.card (U ⊓ V : Subgroup G) ∧ ¬ U ≤ q ctx.Γ ctx.criticalPath.a ∧
      ⁅e ctx.Γ ctx.criticalPath.a, U⁆ = e ctx.Γ ctx.criticalPath.a := by
  let Gamma := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length = 1 := hb
  have hfirst : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have hTnext : T ≤ stabilizer Gamma cp.a' := by
    rw [← hfirst]
    exact (edge_sylow_data ctx.sectionSeven Gamma cp).2.1
  have hQnextT : q Gamma cp.a' ≤ T := by
    rw [← hfirst]
    exact (local_cores_le_edge_sylow ctx.sectionSeven Gamma cp).2
  have hTQ : T ≤ Subgroup.normalizer (q Gamma cp.a') :=
    hTnext.trans (stabilizer_le_normalizer_q Gamma cp.a')
  have hTZ : T ≤ Subgroup.normalizer (z Gamma cp.a') :=
    hTnext.trans (stabilizer_le_normalizer_z Gamma cp.a')
  have hTE : T ≤ Subgroup.normalizer (e Gamma cp.a') := by
    apply hTnext.trans
    rw [CosetGraphContext.e, Gamma.twoResidualAt_def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le _)).mp
      (twoResidualIn_normal _)
  obtain ⟨U, hUQ, hUQcomm, hUEcomm, hgreatest⟩ :=
    Subgroup.exists_greatest_commutator_subgroup (q Gamma cp.a') (z Gamma cp.a')
      (e Gamma cp.a') (hQnextT.trans hTZ) seed hseedQ hseedQcomm hseedEcomm
  have hU : U ≤ T := hUQ.trans hQnextT
  have hnormal : (U.subgroupOf T).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.greatest_commutator_subgroup_normalized _ _ _ _ _
        hUQ hUQcomm hUEcomm hgreatest hTQ hTZ hTE)
  have hseedU : seed ≤ U := hgreatest seed hseedQ hseedQcomm hseedEcomm
  have hnot : ¬ U ≤ q Gamma cp.a := fun hle => hseednot (hseedU.trans hle)
  refine ⟨U, hUQ, hUQcomm, hUEcomm, hgreatest, hU, hnormal, ?_, hnot, ?_⟩
  · exact hseedcard.trans (Nat.card_le_card_of_injective
      (Subgroup.inclusion (inf_le_inf_right V hseedU)) (Subgroup.inclusion_injective _))
  · have h34 := Stellmacher.SectionThree.lemma_three_four T
      (sectionThreeHypotheses ctx.sectionSeven) (stabilizer Gamma cp.a)
      ((pFamily_iff_pSet _ _ _).mp (edge_local_data ctx.sectionSeven Gamma cp).1.1)
      U ⟨hU, hnormal⟩ (edge_local_data ctx.sectionSeven Gamma cp).1.2
    rcases h34 with hcore | hcomm
    · apply (hnot ?_).elim
      rw [q, Gamma.twoCoreAt_def]
      exact hcore
    · change ⁅e Gamma cp.a, U⁆ = e Gamma cp.a
      rw [CosetGraphContext.e, Gamma.twoResidualAt_def]
      exact hcomm


private theorem distance_one_commutator_centralizes_start_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (U V : Subgroup G) (hVQ : V ≤ q ctx.Γ ctx.criticalPath.a')
    (hcomm : ⁅U, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a') :
    ⁅U, V⁆ ≤ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) := by
  have hcent : z ctx.Γ ctx.criticalPath.a' ≤
      Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact ctx.commutator_eq
  exact (Subgroup.commutator_mono le_rfl hVQ).trans (hcomm.le.trans hcent)

private theorem distance_one_action_nontrivial_of_not_le_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (U : Subgroup G) (hUT : U ≤ T) (hnot : ¬ U ≤ q ctx.Γ ctx.criticalPath.a) :
    Nat.card (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G) <
      Nat.card U := by
  apply lt_of_not_ge
  intro hcard
  have heq := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
  apply hnot
  rw [← (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).edge_centralizer]
  exact le_inf hUT (heq.symm.le.trans inf_le_right)





private theorem distance_one_faithful_quotient_control
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfaith : DistanceOneFaithfulConclusion ctx)
    (U V : Subgroup G) (hUT : U ≤ T) (hVT : V ≤ T)
    (hfour : 4 ≤ (V ⊓ q ctx.Γ ctx.criticalPath.a).relIndex V)
    (hcomm : ⁅U, V⁆ ≤ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)) :
    U ≤ V ⊔ q ctx.Γ ctx.criticalPath.a ∧
      Nat.card U ≤ 4 * Nat.card
        (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G) := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let C := Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)
  obtain ⟨projection, hsurj, hker⟩ := hfaith.2
  obtain ⟨hTP, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hUP : U ≤ P := hUT.trans hTP
  have hVP : V ≤ P := hVT.trans hTP
  have hnative : (sylow : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTP]
    exact hsylow
  have hkernel : projection.ker = C.subgroupOf P := by
    rw [hker]
    ext element
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, element.property, true_and]
    rfl
  have hQC : T ⊓ C = q ctx.Γ ctx.criticalPath.a :=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).edge_centralizer
  have hVC : V ⊓ C = V ⊓ q ctx.Γ ctx.criticalPath.a := by
    rw [← hQC, ← inf_assoc, inf_eq_left.mpr hVT]
  have hindex : 4 ≤ projection.ker.relIndex (V.subgroupOf P) := by
    rw [hkernel, Subgroup.relIndex_subgroupOf hVP, ← Subgroup.inf_relIndex_right,
      inf_comm C V, hVC]
    exact hfour
  have hnativecomm : ⁅U.subgroupOf P, V.subgroupOf P⁆ ≤ projection.ker := by
    rw [hkernel]
    apply Subgroup.commutator_le.mpr
    intro first hfirst second hsecond
    exact hcomm (Subgroup.commutator_mem_commutator hfirst hsecond)
  obtain ⟨hcontain, hbound⟩ := wreath_quotient_sylow_control projection hsurj sylow
    (U.subgroupOf P) (V.subgroupOf P)
    (by rw [hnative]; exact Subgroup.comap_mono hUT)
    (by rw [hnative]; exact Subgroup.comap_mono hVT) hindex hnativecomm
  constructor
  · have hmap := Subgroup.map_mono (f := P.subtype) hcontain
    rw [Subgroup.map_subgroupOf_eq_of_le hUP, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hVP, hnative, hkernel] at hmap
    change U ≤ V ⊔ ((T ⊓ C).subgroupOf P).map P.subtype at hmap
    rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hTP), hQC] at hmap
    exact hmap
  · have hUcard : Nat.card (U.subgroupOf P) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv
    have hCcard : Nat.card (U.subgroupOf P ⊓ projection.ker : Subgroup P) =
        Nat.card (U ⊓ C : Subgroup G) := by
      rw [hkernel]
      change Nat.card ((U ⊓ C).subgroupOf P) = Nat.card (U ⊓ C : Subgroup G)
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hUP)).toEquiv
    rwa [hUcard, hCcard] at hbound





/-- The greatest subgroup with the neighboring commutator equations has
the size, normality and action properties of source relation (9). -/
public theorem distance_one_maximal_v1_of_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (data : DistanceOneExtractionData ctx)
    (hcoatom : data.coatom = z ctx.Γ ctx.criticalPath.a ⊓
      stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a))
    (hfour :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
      4 ≤ (V ⊓ q ctx.Γ ctx.criticalPath.a).relIndex V)
    (hthree :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
      ⁅(Subgroup.center V).map V.subtype, twoResidualIn data.E⁆ = ⊥)
    (hintersection : z ctx.Γ ctx.criticalPath.a ⊓
        stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) =
      z ctx.Γ ctx.criticalPath.a ⊓ q ctx.Γ ctx.criticalPath.a') :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    z ctx.Γ ctx.criticalPath.a ⊓ z ctx.Γ next = z ctx.Γ ctx.criticalPath.a' ∧
    ∃ U : Subgroup G,
      U ≤ q ctx.Γ ctx.criticalPath.a' ∧
      z ctx.Γ ctx.criticalPath.a' ≤ U ∧
      ⁅U, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a' ∧
      ⁅U, e ctx.Γ ctx.criticalPath.a'⁆ = U ∧
      (∀ W : Subgroup G, W ≤ q ctx.Γ ctx.criticalPath.a' →
        ⁅W, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a' →
        ⁅W, e ctx.Γ ctx.criticalPath.a'⁆ = W → W ≤ U) ∧
      U ≤ T ∧ (U.subgroupOf T).Normal ∧
      8 ≤ Nat.card (U ⊓ V : Subgroup G) ∧ ¬ U ≤ q ctx.Γ ctx.criticalPath.a ∧
      U ≤ V ⊔ q ctx.Γ ctx.criticalPath.a ∧
      Nat.card (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G) <
        Nat.card U ∧
      Nat.card U ≤ 4 * Nat.card
        (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G) ∧
      ⁅e ctx.Γ ctx.criticalPath.a, U⁆ = e ctx.Γ ctx.criticalPath.a := by
  obtain ⟨seed, hseedQ, hseedQcomm, hseedEcomm, hseedcard, hseednot⟩ :=
    distance_one_admissible_seed_of_extraction ctx hb hfaith data hcoatom hfour hthree hintersection
  let Gamma := ctx.Γ
  let cp := ctx.criticalPath
  let next := Gamma.act data.x⁻¹ cp.a
  let V := (z Gamma cp.a ⊓ stabilizer Gamma next) ⊔
    (z Gamma next ⊓ stabilizer Gamma cp.a)
  have hVQ : V ≤ q Gamma cp.a' :=
    distance_one_product_le_next_core ctx hb data hintersection
  have hlen : cp.length = 1 := hb
  have hfirst : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have hVT : V ≤ T := by
    apply hVQ.trans
    rw [← hfirst]
    exact (local_cores_le_edge_sylow ctx.sectionSeven Gamma cp).2
  obtain ⟨U, hUQ, hUQcomm, hUEcomm, hgreatest, hUT, hnormal, hcard, hnot, hres⟩ :=
    distance_one_greatest_from_seed ctx hb V seed hseedQ hseedQcomm hseedEcomm hseedcard hseednot
  have hcomm := distance_one_commutator_centralizes_start_center ctx U V hVQ hUQcomm
  obtain ⟨hcontain, hupper⟩ := distance_one_faithful_quotient_control
    ctx.toLocalContext hfaith U V hUT hVT hfour hcomm
  have hQnextT : q Gamma cp.a' ≤ T := by
    rw [← hfirst]
    exact (local_cores_le_edge_sylow ctx.sectionSeven Gamma cp).2
  have hZle : z Gamma cp.a' ≤ U := by
    rw [← hUQcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQnextT.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mp hnormal))
  exact ⟨distance_one_center_intersection_eq_of_extraction ctx hb hfaith data hfour,
    U, hUQ, hZle, hUQcomm, hUEcomm, hgreatest, hUT, hnormal, hcard, hnot, hcontain,
    distance_one_action_nontrivial_of_not_le_core ctx.toLocalContext U hUT hnot, hupper, hres⟩

end Stellmacher.SectionNine
