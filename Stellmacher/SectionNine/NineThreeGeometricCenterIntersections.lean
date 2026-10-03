module
public import Stellmacher.SectionNine.NineThreeExtractedCenterNoncontainment
public import Stellmacher.SectionNine.LemmaNineTwo

/-!
# Center intersections for either geometric extraction in (9.3)

Retain the actual ambient context and extraction at an edge d,l, with d
in the terminal-vertex orbit. Let the actor belong to the center at a
supplied base vertex u. Suppose that center centralizes its core, the
center at l lies in that core and has order greater than four, and the
actor module lies in Q_l. A subgroup W in both centers and Q_u, with the
supplied doubled-cardinality bound, then identifies the intersections
of the extracted center with Q_u and Z_l. It also proves the corresponding
cardinality bound and that the extracted center lies outside G_u.

Write I≤F≤Y for the Z_l, Q_u, and G_u intersections. If F differs from I,
finite subgroup indices and the bound force F=Y. The actor and its
conjugate module then centralize Y, so E centralizes it; the residual
conjugator fixes it, forcing Y into Z_l. This contradicts F≠I. If the
whole extracted center lies in G_u, its core noncontainment and the same
cardinality bound give index two between the conjugate centers. Mapping
the extracted edge-generation equality backwards gives the exact (9.2)
hypotheses, forcing |Z_l|=4, a contradiction. The public
`geometric_extraction_core_edge_generation` records that generation
consequence separately for the exact index-four argument in (9.3).

The explicit geometric inputs cover both uses in Stellmacher (9.3),
relation (2) and the repeated argument after (3), Journal of Algebra
190 (1997), p.49, `refs/files/stellmacher-n-group.pdf`. Hypothesis Two
remains on the original ambient group; no new critical path is assumed.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem double_card_le_of_lt
    {G : Type u} [Group G] [Finite G] (K L : Subgroup G)
    (hle : K ≤ L) (hne : K ≠ L) : 2 * Nat.card K ≤ Nat.card L := by
  have hlt : Nat.card K < Nat.card L := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hle)
    intro he
    exact hne (Subgroup.eq_of_le_of_card_ge hle he.ge)
  obtain ⟨n,hn⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hn2 : 2 ≤ n := by nlinarith
  nlinarith

private theorem original_edge_generation
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (d l : Γ.Vertex)
    (V E A0 : Subgroup G) (actor : G)
    (data : NineThreeGeometricData Γ d l V E A0 actor) :
    E ⊔ (stabilizer Γ l ⊓ stabilizer Γ d) = stabilizer Γ d := by
  have hxE : data.x ∈ E := Subgroup.map_subtype_le _ data.residual_mem
  have hxP : data.x ∈ stabilizer Γ d := data.group_le hxE
  have hEmap : E.conjBy data.x⁻¹ = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (E.le_normalizer (E.inv_mem hxE))
  have hPmap : (stabilizer Γ d).conjBy data.x⁻¹ = stabilizer Γ d :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((stabilizer Γ d).le_normalizer ((stabilizer Γ d).inv_mem hxP))
  have hGm : stabilizer Γ (Γ.act data.x⁻¹ l) = (stabilizer Γ l).conjBy data.x := by
    rw [stabilizer_act,inv_inv]
    rfl
  have hh := congrArg (Subgroup.map (MulAut.conj data.x⁻¹).toMonoidHom) data.edge_generated
  rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ (MulAut.conj data.x⁻¹).injective] at hh
  change E.conjBy data.x⁻¹ ⊔ ((stabilizer Γ d).conjBy data.x⁻¹ ⊓
    (stabilizer Γ (Γ.act data.x⁻¹ l)).conjBy data.x⁻¹) =
    (stabilizer Γ d).conjBy data.x⁻¹ at hh
  rwa [hEmap,hPmap,hGm,Subgroup.conjBy_inv,inf_comm] at hh

/-- The core at the actual extracted neighbor generates the fixed stabilizer
with the original full edge, whenever the actor module lies in the old core. -/
public theorem geometric_extraction_core_edge_generation
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (d l : Γ.Vertex)
    (V E A0 : Subgroup G) (actor : G) (hVQ : V ≤ QAt Γ l)
    (data : NineThreeGeometricData Γ d l V E A0 actor) :
    QAt Γ (Γ.act data.x⁻¹ l) ⊔ (GAt Γ l ⊓ GAt Γ d) = GAt Γ d := by
  let m := Γ.act data.x⁻¹ l
  have hmrev : d ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hQmGd : QAt Γ m ≤ GAt Γ d :=
    ((lemma_seven_three h Γ).sylow_and_core m d hmrev default).2.2
  have hVlGl : V ≤ GAt Γ l := by
    apply hVQ.trans
    change q Γ l ≤ stabilizer Γ l
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hVlE : V ≤ E := by rw [data.generated]; exact le_sup_left
  have hVlEdge : V ≤ GAt Γ l ⊓ GAt Γ d :=
    le_inf hVlGl (hVlE.trans data.group_le)
  have hgenOld := original_edge_generation Γ d l V E A0 actor data
  apply le_antisymm (sup_le hQmGd inf_le_right)
  apply hgenOld.ge.trans
  refine sup_le ?_ le_sup_right
  rw [data.generated]
  exact sup_le (hVlEdge.trans le_sup_right) (data.conjugate_core_le.trans le_sup_left)

public theorem nine_three_geometric_center_intersections
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (u0 d l : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a' d)
    (hl : l ∈ neighborhood ctx.Γ d)
    (V E A0 : Subgroup G) (hVQ : V ≤ QAt ctx.Γ l)
    (actor : G) (haV : actor ∈ V) (haZ : actor ∈ ZAt ctx.Γ u0)
    (hZu : ZAt ctx.Γ u0 ≤ Subgroup.centralizer (QAt ctx.Γ u0 : Set G))
    (hZlQ : ZAt ctx.Γ l ≤ QAt ctx.Γ u0)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ l))
    (data : NineThreeGeometricData ctx.Γ d l V E A0 actor)
    (W : Subgroup G)
    (hWm : W ≤ ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l))
    (hWa : W ≤ QAt ctx.Γ u0)
    (hWl : W ≤ ZAt ctx.Γ l)
    (hbound : Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ GAt ctx.Γ u0) ≤
      2 * Nat.card W) :
    let m := ctx.Γ.act data.x⁻¹ l
    ZAt ctx.Γ m ⊓ QAt ctx.Γ u0 = ZAt ctx.Γ m ⊓ ZAt ctx.Γ l ∧
      Nat.card ↥(ZAt ctx.Γ m ⊓ GAt ctx.Γ u0) ≤
        2 * Nat.card ↥(ZAt ctx.Γ m ⊓ QAt ctx.Γ u0) ∧
      ¬ ZAt ctx.Γ m ≤ GAt ctx.Γ u0 := by
  let Γ := ctx.Γ
  let m := Γ.act data.x⁻¹ l
  let Y := ZAt Γ m ⊓ GAt Γ u0
  let F := ZAt Γ m ⊓ QAt Γ u0
  let I := ZAt Γ m ⊓ ZAt Γ l
  have hQaGa : QAt Γ u0 ≤ GAt Γ u0 := by
    change q Γ u0 ≤ stabilizer Γ u0
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hIF : I ≤ F := inf_le_inf_left _ hZlQ
  have hFY : F ≤ Y := inf_le_inf_left _ hQaGa
  have hWI : W ≤ I := le_inf hWm hWl
  have hYbound : Nat.card Y ≤ 2 * Nat.card I :=
    hbound.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le hWI))
  have hmrev : d ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hZm : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core m d hmrev).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hF_eq : F = I := by
    by_contra hne
    have hFbig := double_card_le_of_lt I F hIF (Ne.symm hne)
    have hFYeq : F = Y := Subgroup.eq_of_le_of_card_ge hFY (hYbound.trans hFbig)
    have hYQa : Y ≤ QAt Γ u0 := hFYeq ▸ (inf_le_right : F ≤ QAt Γ u0)
    have haY : actor ∈ Subgroup.centralizer (Y : Set G) :=
      Subgroup.centralizer_le hYQa (hZu haZ)
    have hAxY : V.conjBy data.x ≤ Subgroup.centralizer (Y : Set G) :=
      data.conjugate_core_le.trans ((Subgroup.le_centralizer_iff.mp hZm).trans
        (Subgroup.centralizer_le inf_le_left))
    have hEY : E ≤ Subgroup.centralizer (Y : Set G) := by
      rw [data.actor_generated actor haV data.actor_outside]
      exact sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr haY)) hAxY
    have hYI : Y ≤ I := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      have hxE : data.x ∈ E := Subgroup.map_subtype_le _ data.residual_mem
      have hcomm := Subgroup.mem_centralizer_iff.mp (hEY hxE) z hz
      have hback : data.x⁻¹ * z * data.x = z := by
        rw [mul_assoc, hcomm]
        simp
      have hzConj : z ∈ (ZAt Γ l).conjBy data.x := by
        have hzM := hz.1
        change z ∈ CosetGraphContext.z Γ (Γ.act data.x⁻¹ l) at hzM
        rw [z_act,inv_inv] at hzM
        exact hzM
      have hzBack : data.x⁻¹ * z * data.x ∈ ZAt Γ l := by
        obtain ⟨t,ht,he⟩ := hzConj
        rw [← he]
        simpa [mul_assoc] using ht
      rwa [hback] at hzBack
    exact hne (le_antisymm (hFY.trans hYI) hIF)
  have hcardBound : Nat.card Y ≤ 2 * Nat.card F :=
    hbound.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le (le_inf hWm hWa)))
  have hmQa : ¬ ZAt Γ m ≤ QAt Γ u0 :=
    nine_three_geometric_extracted_center_not_le_core ctx.sectionSeven Γ u0 d l
      V E A0 actor haV haZ hZu data
  have hmGa : ¬ ZAt Γ m ≤ GAt Γ u0 := by
    intro hcontained
    have hYeq : Y = ZAt Γ m := inf_eq_left.mpr hcontained
    have hIne : I ≠ ZAt Γ m := by
      intro he
      exact hmQa (he ▸ (inf_le_right.trans hZlQ : I ≤ QAt Γ u0))
    have hlower := double_card_le_of_lt I (ZAt Γ m) inf_le_left hIne
    have hindexm : Nat.card (ZAt Γ m) = 2 * Nat.card I :=
      le_antisymm (hYeq ▸ hYbound) hlower
    have hmlcard : Nat.card (ZAt Γ m) = Nat.card (ZAt Γ l) := by
      change Nat.card (z Γ (Γ.act data.x⁻¹ l)) = _
      rw [z_act,inv_inv]
      exact Subgroup.card_map_of_injective (MulAut.conj data.x).injective
    have hindex : QuotientCardEq (ZAt Γ l) (ZAt Γ l ⊓ ZAt Γ m) 2 := by
      change Nat.card (ZAt Γ l) = 2 * Nat.card ↥(ZAt Γ l ⊓ ZAt Γ m)
      rw [← hmlcard, inf_comm]
      exact hindexm
    have hgenQ := geometric_extraction_core_edge_generation ctx.sectionSeven Γ d l
      V E A0 actor hVQ data
    have hnine := lemma_nine_two_ambient ctx d l m hd hl
      data.neighbor hindex hgenQ
    exact (ne_of_gt hlarge) hnine.2
  exact ⟨hF_eq,hcardBound,hmGa⟩
end Stellmacher.SectionNine
