module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.MixedActor
public import Theory.GroupTheory.CenterFreeCubicFixedIndex

/-!
# The zero mixed-commutator branch is impossible for a large cubic center

If the mixed commutator vanishes, its index-two center intersection is the
fixed hyperplane of the other-center actor. That actor lies in the actual
Sylow, moves the initial center, and therefore crosses the local two-core.
The center-free S₃ fixed-index square bound forces center order at most four.

This proves the nonzero mixed-commutator conclusion in Stellmacher (9.3)
for the cubic local case directly, without the ambient (6.4) or its rank-two
wreath analysis. Source: Journal of Algebra 190 (1997), pp.49--50.
-/
namespace Stellmacher.SectionNine.LocalLonger
open Subgroup Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem source_fixed_hyperplane_of_mixed_bot
    {G : Type u} [Group G] [Finite G] (center stabilizer actor : Subgroup G)
    (hindex : Nat.card center = 2 * Nat.card (center ⊓ stabilizer : Subgroup G))
    (hzero : ⁅center ⊓ stabilizer, actor⁆ = ⊥)
    (hnontrivial : ¬ center ≤ Subgroup.centralizer (actor : Set G)) :
    center ⊓ Subgroup.centralizer (actor : Set G) = center ⊓ stabilizer := by
  let hyperplane := center ⊓ stabilizer
  let fixed := center ⊓ Subgroup.centralizer (actor : Set G)
  have hle : hyperplane ≤ fixed := le_inf inf_le_left
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hproper : fixed ≠ center := fun heq =>
    hnontrivial (heq ▸ (inf_le_right : fixed ≤ Subgroup.centralizer (actor : Set G)))
  have hlt : Nat.card fixed < Nat.card center := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left)
    intro heq
    exact hproper (Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge)
  obtain ⟨index, hcard⟩ := Subgroup.card_dvd_of_le (inf_le_left : fixed ≤ center)
  have hpositive : 0 < Nat.card fixed := Nat.card_pos
  have htwo : 2 ≤ index := by nlinarith
  have hbound : Nat.card fixed ≤ Nat.card hyperplane := by
    change Nat.card center = 2 * Nat.card hyperplane at hindex
    nlinarith
  exact (Subgroup.eq_of_le_of_card_ge hle hbound).symm

private theorem source_full_fixed_index_of_mixed_bot
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : FirstConfigurationData ctx)
    (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second)
    (hzero : let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
      (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
        ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) = ⊥) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 2 * Nat.card
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        ((ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a : Subgroup G) : Set G) : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let conjugation := MulAut.conj config.g⁻¹
  let oldFirst := Γ.act first.extraction.x⁻¹ first.l
  let oldSecond := Γ.act second.extraction.x⁻¹ second.l
  let vertex := Γ.act config.g oldFirst
  have hcenter : (ZAt Γ oldSecond).map conjugation.toMonoidHom = ZAt Γ cp.a := by
    change (z Γ oldSecond).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act, config.maps_new_vertex]
  have hgroup : (GAt Γ oldFirst).map conjugation.toMonoidHom = GAt Γ vertex := by
    change conjugateBy (stabilizer Γ oldFirst) config.g⁻¹ = _
    rw [← stabilizer_act]
  have hindex : Nat.card (ZAt Γ cp.a) =
      2 * Nat.card (ZAt Γ cp.a ⊓ GAt Γ vertex : Subgroup G) := by
    rw [← hcenter, ← hgroup, ← Subgroup.map_inf _ _ _ conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective]
    exact (four_center_indices ctx e hb hlarge first second).2.2.1
  have heq := source_fixed_hyperplane_of_mixed_bot (ZAt Γ cp.a) (GAt Γ vertex)
    (ZAt Γ vertex ⊓ GAt Γ cp.a) hindex hzero
    (mixed_actor_nontrivial_action ctx e hb hlarge first second config)
  exact hindex.trans
    (congrArg (fun subgroup : Subgroup G => 2 * Nat.card subgroup) heq.symm)

private theorem center_card_le_four_of_sylow_fixed_hyperplane
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h7 : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext.{u,u} G T A B) (cp : CriticalPath Γ)
    (e : ((stabilizer Γ cp.a) ⧸ pCore 2 (stabilizer Γ cp.a)) ≃* Equiv.Perm (Fin 3))
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (U : Subgroup G) (hUT : U ≤ T)
    (hnon : ¬ ZAt Γ cp.a ≤ Subgroup.centralizer (U : Set G))
    (hfixed : Nat.card (ZAt Γ cp.a) =
      2 * Nat.card (ZAt Γ cp.a ⊓ Subgroup.centralizer (U : Set G) : Subgroup G)) :
    Nat.card (ZAt Γ cp.a) ≤ 4 := by
  have hnot : ¬ U ≤ QAt Γ cp.a := by
    intro hUQ
    apply hnon
    apply Subgroup.le_centralizer_iff.mpr
    have hQZ := (lemma_seven_four h7 Γ cp).edge_centralizer
    exact hUQ.trans (hQZ.symm.le.trans inf_le_right)
  let P := stabilizer Γ cp.a
  let V := (ZAt Γ cp.a).subgroupOf P
  have hTP : T ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  obtain ⟨_,S,hS⟩ := (SevenSix.edge_sylow_data h7 Γ cp).1
  have hS' : (S : Subgroup P) = (T).subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hTP]
    exact hS
  have hZP : ZAt Γ cp.a ≤ P := by
    exact (lemma_seven_three h7 Γ).center_core cp.a cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) |>.trans
      (SevenSix.omegaOneCenter_le_centerAmbient (q Γ cp.a)) |>.trans
      ((map_subtype_le (center (q Γ cp.a))).trans (by
        rw [q, Γ.twoCoreAt_def]
        exact map_subtype_le _))
  have hVnorm : V.Normal := (normal_subgroupOf_iff_le_normalizer hZP).mpr
    (stabilizer_le_normalizer_z Γ cp.a)
  let := hVnorm
  have hc : center P = ⊥ := (lemma_seven_five h7 Γ cp hcomm).start_center_trivial
  have hQ : (pCore 2 P).map P.subtype = QAt Γ cp.a := by
    exact (Γ.twoCoreAt_def cp.a).symm
  have hVQ : V ≤ centralizer (pCore 2 P : Set P) := by
    intro x hx y hy
    apply Subtype.ext
    have hz := (lemma_seven_four h7 Γ cp).edge_centralizer
    have hyQ : (y : G) ∈ q Γ cp.a := by
      change (y : G) ∈ QAt Γ cp.a
      rw [← hQ]
      exact mem_map_of_mem P.subtype hy
    rw [← hz] at hyQ
    exact hyQ.2 (x : G) hx |>.symm
  have hUS : U.subgroupOf P ≤ (S : Subgroup P) := by
    rw [hS']
    intro x hx
    exact hUT hx
  have hUnot : ¬ U.subgroupOf P ≤ pCore 2 P := by
    intro hh
    apply hnot
    intro x hx
    have hxp : x ∈ P := hTP (hUT hx)
    change x ∈ QAt Γ cp.a
    rw [← hQ]
    exact mem_map_of_mem P.subtype (hh (show (⟨x,hxp⟩ : P) ∈ U.subgroupOf P from hx))
  have hfixeq : V ⊓ centralizer (U.subgroupOf P : Set P) =
      (ZAt Γ cp.a ⊓ centralizer (U : Set G)).subgroupOf P := by
    ext x
    constructor
    · rintro ⟨hx,hcx⟩
      refine ⟨hx, ?_⟩
      intro y hy
      exact congrArg Subtype.val (hcx (⟨y,hTP (hUT hy)⟩ : P) hy)
    · rintro ⟨hx,hcx⟩
      refine ⟨hx, ?_⟩
      intro y hy
      exact Subtype.ext (hcx (y : G) hy)
  have hfixindex : (V ⊓ centralizer (U.subgroupOf P : Set P)).relIndex V = 2 := by
    rw [hfixeq]
    change ((ZAt Γ cp.a ⊓ centralizer (U : Set G)).subgroupOf P).relIndex
      ((ZAt Γ cp.a).subgroupOf P) = 2
    rw [relIndex_subgroupOf hZP]
    have hh := ((ZAt Γ cp.a ⊓ centralizer (U : Set G)).subgroupOf (ZAt Γ cp.a)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show ZAt Γ cp.a ⊓ centralizer (U : Set G) ≤ ZAt Γ cp.a from inf_le_left)).toEquiv] at hh
    change (ZAt Γ cp.a ⊓ centralizer (U : Set G)).relIndex (ZAt Γ cp.a) *
      Nat.card (ZAt Γ cp.a ⊓ centralizer (U : Set G) : Subgroup G) = Nat.card (ZAt Γ cp.a) at hh
    change Nat.card (ZAt Γ cp.a) = 2 * Nat.card (ZAt Γ cp.a ⊓ centralizer (U : Set G) : Subgroup G) at hfixed
    have hpos := Nat.card_pos (α := (ZAt Γ cp.a ⊓ centralizer (U : Set G) : Subgroup G))
    nlinarith
  have hh := SymmetricThreeTwoCore.normal_card_le_four_of_fixed_index_two e S V hc
    hVQ (U.subgroupOf P) hUS hUnot hfixindex
  rwa [Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv] at hh


/-- The actual normalized mixed commutator is nontrivial under the large-center assumption. -/
public theorem mixed_commutator_ne_bot
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.a) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)) ≃* Equiv.Perm (Fin 3))
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : FirstConfigurationData ctx) (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,
      ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) ≠ ⊥ := by
  dsimp only
  intro hzero
  have hfixed := source_full_fixed_index_of_mixed_bot ctx e hb hlarge first second config hzero
  have hsmall := center_card_le_four_of_sylow_fixed_hyperplane ctx.sectionSeven
    ctx.Γ ctx.criticalPath e ctx.commutator_eq _
    (mixed_actor_quadratic ctx hb first second config).1
    (mixed_actor_nontrivial_action ctx e hb hlarge first second config) hfixed
  omega

end Stellmacher.SectionNine.LocalLonger
