module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# The elimination step for the shifted commutator in (8.4)

The center at the second path vertex meets the center at the first extracted
terminal neighbor trivially. Critical minimality makes the intersection
centralize the selected initial factor. Centrality at the terminal neighbor
makes it centralize the conjugate factor and the neighbor stabilizer. The
first extraction generates the terminal stabilizer, so the intersection is
central in the ambient group. Its two-group property and the trivial ambient
two-core finish the proof.

Only the local Section Seven hypotheses, critical path and noncommuting
endpoints are used; no Hypothesis Two on the generated group is required.
This is the elimination step after the R2 containment in Stellmacher (8.4),
printed p.40 of `refs/files/stellmacher-n-group.pdf`. It does not assert or
assume the preceding shifted-commutator containment.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_terminal_neighbor_center_le_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (neighbor : ctx.Γ.Vertex)
    (hadj : ctx.Γ.adjacent ctx.criticalPath.a' neighbor) :
    ZAt ctx.Γ neighbor ≤ CenterAmbient (GAt ctx.Γ neighbor) := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hend : ⁅z Γ cp.a', stabilizer Γ cp.a'⁆ ≠ ⊥ := by
    intro hcomm
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact bot_unique ((Subgroup.commutator_mono le_rfl
      ((lemma_seven_four h Γ cp).first_containment.1.trans
        (lemma_seven_four h Γ cp).first_containment.2)).trans_eq hcomm)
  have hcomm : ⁅z Γ cp.firstStep, stabilizer Γ cp.firstStep⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcenter.trans (SevenSix.centerAmbient_le_centralizer _))
  obtain ⟨actor, hedge | hedge⟩ :=
    (lemma_seven_one h Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  · have hact : ⁅z Γ neighbor, stabilizer Γ neighbor⁆ = ⊥ := by
      rw [← hedge.2, z_act, stabilizer_act, conjugateBy, ← Subgroup.map_commutator,
        hcomm, Subgroup.map_bot]
    have hsub : z Γ neighbor ≤ stabilizer Γ neighbor := by
      rw [← hedge.2, z_act, stabilizer_act, conjugateBy]
      exact Subgroup.map_mono (hcenter.trans (Subgroup.map_subtype_le _))
    intro element helement
    refine ⟨⟨element, hsub helement⟩, ?_, rfl⟩
    change (⟨element, hsub helement⟩ : stabilizer Γ neighbor) ∈
      Subgroup.center (stabilizer Γ neighbor)
    rw [Subgroup.mem_center_iff]
    intro other
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hact helement)
        other other.property
  · have hact : ⁅z Γ (Γ.act actor cp.firstStep),
        stabilizer Γ (Γ.act actor cp.firstStep)⁆ = ⊥ := by
      rw [z_act, stabilizer_act, conjugateBy, ← Subgroup.map_commutator,
        hcomm, Subgroup.map_bot]
    rw [hedge.2] at hact
    exact False.elim (hend hact)

public theorem eight_four_first_configuration_second_center_inf_eq_bot_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (A L0 : Subgroup H) (x : H)
    (hA : A ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hAprev : A ≤ QAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩))
    (hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hLgen : L0 = A ⊔ A.conjBy x) (hx : x ∈ L0)
    (hfull : L0 ⊔
      (GAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) ⊓
        GAt ctx.Γ ctx.criticalPath.a') = GAt ctx.Γ ctx.criticalPath.a')
    (hlen : 2 < ctx.criticalPath.length) :
    ZAt ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩) ⊓
      ZAt ctx.Γ (ctx.Γ.act x⁻¹
        (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩)) = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  have hlength : 2 < cp.length := hlen
  let previous := cp.path ⟨cp.length - 1, by omega⟩
  let second := cp.path ⟨2, by omega⟩
  let neighbor := Γ.act x⁻¹ previous
  let R := ZAt Γ second ⊓ ZAt Γ neighbor
  let conjugation := (MulAut.conj x).toMonoidHom
  have hpos := cp.length_pos
  have hprevious : Γ.adjacent cp.a' previous := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hindex : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hindex, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hfix : Γ.act x⁻¹ cp.a' = cp.a' := by
    have hmem := (GAt Γ cp.a').inv_mem (hL0 hx)
    change x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hmem
    rw [Γ.stabilizer_def] at hmem
    exact hmem
  have hadj : Γ.adjacent cp.a' neighbor := by
    have hedge := adjacent_act Γ x⁻¹ hprevious
    rwa [hfix] at hedge
  have hneighbor := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj
  have hcentral := eight_four_terminal_neighbor_center_le_local ctx hcenter neighbor hadj
  have hRC : R ≤ Subgroup.centralizer (GAt Γ neighbor : Set H) :=
    inf_le_right.trans (hcentral.trans (SevenSix.centerAmbient_le_centralizer _))
  have hdistance : Γ.distance cp.a second ≤ 2 := by
    let path : Fin 3 → Γ.Vertex := fun index => cp.path ⟨index, by omega⟩
    have hpath : ∀ index : Fin 2,
        Γ.adjacent (path index.castSucc) (path index.succ) := by
      intro index
      exact cp.path_adj ⟨index, by omega⟩
    have hbound := Γ.distance_le_of_path 2 path hpath
    change Γ.distance (cp.path 0) second ≤ 2 at hbound
    rwa [cp.path_start] at hbound
  have hAQ : A ≤ QAt Γ second := hA.trans
    (SevenSix.critical_minimality Γ cp (by
      change Γ.distance cp.a second < cp.length
      omega))
  have hsecondAdj : Γ.adjacent cp.firstStep second := by
    have hedge := cp.path_adj ⟨1, by omega⟩
    change Γ.adjacent (cp.path ⟨1, by omega⟩) second at hedge
    rwa [cp.path_first] at hedge
  have hsecondCenter : ZAt Γ second ≤ Subgroup.centralizer (QAt Γ second : Set H) :=
    ((lemma_seven_three h Γ).center_core second cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hsecondAdj))).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))
  have hRA : R ≤ Subgroup.centralizer (A : Set H) :=
    inf_le_left.trans (hsecondCenter.trans (Subgroup.centralizer_le hAQ))
  have hQmap : (QAt Γ previous).map conjugation = QAt Γ neighbor := by
    simp only [neighbor, SevenSix.q_act, inv_inv, conjugation]
  have hAxQ : A.conjBy x ≤ QAt Γ neighbor :=
    (Subgroup.map_mono hAprev).trans_eq hQmap
  have hAxP : A.conjBy x ≤ GAt Γ neighbor := hAxQ.trans (by
    rw [show QAt Γ neighbor = twoCoreIn (GAt Γ neighbor) from Γ.twoCoreAt_def neighbor]
    exact Subgroup.map_subtype_le _)
  have hAxR : A.conjBy x ≤ Subgroup.centralizer (R : Set H) :=
    hAxP.trans (Subgroup.le_centralizer_iff.mp hRC)
  have hL0R : L0 ≤ Subgroup.centralizer (R : Set H) := by
    rw [hLgen]
    exact sup_le (Subgroup.le_centralizer_iff.mp hRA) hAxR
  have hL0map : L0.map conjugation = L0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (L0.le_normalizer hx)
  have hPmap : (GAt Γ cp.a').map conjugation = GAt Γ cp.a' :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((GAt Γ cp.a').le_normalizer (hL0 hx))
  have hpreviousMap : (GAt Γ previous).map conjugation = GAt Γ neighbor := by
    simp only [neighbor, stabilizer_act, conjugateBy, inv_inv, conjugation]
  have hnewgen : L0 ⊔ (GAt Γ neighbor ⊓ GAt Γ cp.a') = GAt Γ cp.a' := by
    have hmap := congrArg (Subgroup.map conjugation) hfull
    change (L0 ⊔ (GAt Γ previous ⊓ GAt Γ cp.a')).map conjugation =
      (GAt Γ cp.a').map conjugation at hmap
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
      hL0map, hpreviousMap, hPmap] at hmap
    exact hmap
  have hneighborR : GAt Γ neighbor ≤ Subgroup.centralizer (R : Set H) :=
    Subgroup.le_centralizer_iff.mp hRC
  have hendR : GAt Γ cp.a' ≤ Subgroup.centralizer (R : Set H) := by
    rw [← hnewgen]
    exact sup_le hL0R (inf_le_left.trans hneighborR)
  have hgenerated : GAt Γ cp.a' ⊔ GAt Γ neighbor = ⊤ :=
    (edge_sectionThree_data h Γ hneighbor default).2.2.2.2.1
  have htopR : (⊤ : Subgroup H) ≤ Subgroup.centralizer (R : Set H) := by
    rw [← hgenerated]
    exact sup_le hendR hneighborR
  have hnormal : R.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique (htopR.trans (Subgroup.centralizer_le_normalizer (R : Set H))))
  let _ : IsElementaryAbelian 2 (ZAt Γ neighbor) :=
    SevenSix.z_isElementaryAbelian_of_neighbor h Γ
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hadj))
  have htwo : IsPGroup 2 R :=
    (IsElementaryAbelian.isPGroup 2 (ZAt Γ neighbor)).to_le inf_le_right
  have hcore : R ≤ pCore 2 H := le_sSup ⟨hnormal, htwo⟩
  exact bot_unique (hcore.trans_eq h.twoCore_eq_bot)

end Stellmacher.SectionEight
