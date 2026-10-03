module

public import Stellmacher.SectionNine.NineTwoCoreQuotientFromFour

/-!
# Small-center and orbit assembly for ambient (9.3)

The initial center has order at least four: (7.4) and the proper initial
core prohibit the distinguished Sylow subgroup from centralizing it, whereas
a group of order one or two is centralized by its normalizer. Elementary
abelianity rules out the remaining smaller order.

Consequently an upper bound of four determines the exact center order.
The genuine (9.2) quotient recognition then identifies the ordinary core
quotient, and simultaneous conjugation transports both conclusions to the
initial orbit. This is only the assembly reduction, not numbered (9.3):
the upper bound still requires the final centralizer contradiction.

Source: Stellmacher (9.3), printed pp.49–50/PDF pp.39–40 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem normalizer_centralizes_card_two
    {G : Type u} [Group G] (center : Subgroup G)
    (hcard : Nat.card center = 2) :
    Subgroup.normalizer (center : Set G) ≤ Subgroup.centralizer (center : Set G) := by
  obtain ⟨point, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : center)).mp hcard
  intro actor hactor
  rw [Subgroup.mem_centralizer_iff]
  intro vector hvector
  by_cases hone : vector = 1
  · simp [hone]
  have hconj : actor * vector * actor⁻¹ ∈ center :=
    (Subgroup.mem_normalizer_iff.mp hactor vector).mp hvector
  have hconj_ne : actor * vector * actor⁻¹ ≠ 1 := by
    intro heq
    apply hone
    have hcancel := congrArg (fun value : G => actor⁻¹ * value * actor) heq
    simpa [mul_assoc] using hcancel
  have hvector_eq : (⟨vector, hvector⟩ : center) = point :=
    hunique _ (fun heq => hone (congrArg Subtype.val heq))
  have hconj_eq : (⟨actor * vector * actor⁻¹, hconj⟩ : center) = point :=
    hunique _ (fun heq => hconj_ne (congrArg Subtype.val heq))
  have hcancel := congrArg (fun value : center => (value : G) * actor)
    (hconj_eq.trans hvector_eq.symm)
  simpa [mul_assoc] using hcancel.symm

/-- The initial center in the commuting critical-pair context has order at least four. -/
public theorem nine_three_initial_center_card_lower_bound
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    4 ≤ Nat.card (ZAt ctx.Γ ctx.criticalPath.a) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hneighbor : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneighbor
  have hnot : ¬ T ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) := by
    intro hcentral
    have hcore : T = q Γ cp.a := by
      rw [← (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer,
        inf_eq_left.mpr hcentral]
    exact (SevenSix.edge_local_data ctx.sectionSeven Γ cp).1.1.1.2.2.2
      (hcore.trans (Γ.twoCoreAt_def cp.a))
  have hnot_one : Nat.card (ZAt Γ cp.a) ≠ 1 := by
    intro hone
    apply hnot
    rw [Subgroup.card_eq_one.mp hone]
    intro actor _
    rw [Subgroup.mem_centralizer_iff]
    intro vector hvector
    have hvector_one : vector = 1 := hvector
    simp [hvector_one]
  have hnot_two : Nat.card (ZAt Γ cp.a) ≠ 2 := by
    intro htwo
    apply hnot
    exact (cp.S_le_edge_stabilizers.trans inf_le_left).trans
      ((stabilizer_le_normalizer_z_public Γ cp.a).trans
        (normalizer_centralizes_card_two _ htwo))
  have heven := (IsElementaryAbelian.isPGroup 2 (z Γ cp.a)).card_eq_or_dvd
  change Nat.card (ZAt Γ cp.a) = 1 ∨ 2 ∣ Nat.card (ZAt Γ cp.a) at heven
  have hpositive : 0 < Nat.card (ZAt Γ cp.a) := Nat.card_pos
  change 4 ≤ Nat.card (ZAt Γ cp.a)
  omega

private theorem quotient_model_map
    {G : Type u} [Group G] {stabilizerGroup core : Subgroup G}
    (equiv : G ≃* G) (hmodel : QuotientIsModel stabilizerGroup core SL2Two) :
    QuotientIsModel (stabilizerGroup.map equiv.toMonoidHom) (core.map equiv.toMonoidHom)
      SL2Two := by
  obtain ⟨projection, hsurjective, hkernel⟩ := hmodel
  let localEquiv := stabilizerGroup.equivMapOfInjective equiv.toMonoidHom equiv.injective
  refine ⟨projection.comp localEquiv.symm.toMonoidHom,
    hsurjective.comp localEquiv.symm.surjective, ?_⟩
  ext point
  change projection (localEquiv.symm point) = 1 ↔
    (point : G) ∈ core.map equiv.toMonoidHom
  rw [← MonoidHom.mem_ker, hkernel, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv]
  have hcoe : ((localEquiv.symm point : stabilizerGroup) : G) = equiv.symm (point : G) := by
    apply equiv.injective
    rw [equiv.apply_symm_apply]
    calc
      equiv ((localEquiv.symm point : stabilizerGroup) : G) =
          (localEquiv (localEquiv.symm point) : G) :=
        (Subgroup.coe_equivMapOfInjective_apply stabilizerGroup equiv.toMonoidHom
          equiv.injective (localEquiv.symm point)).symm
      _ = (point : G) := congrArg Subtype.val (localEquiv.apply_symm_apply point)
  rw [hcoe]

/-- An initial center upper bound supplies both conclusions throughout the initial orbit. -/
public theorem nine_three_ambient_of_center_card_le_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hsmall : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) ≤ 4) :
    ∀ vertex : ctx.Γ.Vertex,
      IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4 := by
  have hcard := Nat.le_antisymm hsmall
    (nine_three_initial_center_card_lower_bound ctx.toLocalContext)
  have hmodel := nine_two_core_quotient_of_card_four ctx hcard
  rintro vertex ⟨actor, hactor⟩
  let conjugation := MulAut.conj actor⁻¹
  have hlocal : (GAt ctx.Γ ctx.criticalPath.a).map conjugation.toMonoidHom =
      GAt ctx.Γ vertex := by
    change conjugateBy (stabilizer ctx.Γ ctx.criticalPath.a) actor⁻¹ =
      stabilizer ctx.Γ vertex
    rw [← stabilizer_act, hactor]
  have hcore : (QAt ctx.Γ ctx.criticalPath.a).map conjugation.toMonoidHom =
      QAt ctx.Γ vertex := by
    rw [← SevenSix.q_act ctx.Γ actor, hactor]
  have hcenter : (ZAt ctx.Γ ctx.criticalPath.a).map conjugation.toMonoidHom =
      ZAt ctx.Γ vertex := by
    rw [← z_act ctx.Γ actor, hactor]
  constructor
  · have htransport := quotient_model_map conjugation hmodel
    rwa [hlocal, hcore] at htransport
  · rw [← hcenter, Subgroup.card_map_of_injective conjugation.injective]
    exact hcard

end Stellmacher.SectionNine
