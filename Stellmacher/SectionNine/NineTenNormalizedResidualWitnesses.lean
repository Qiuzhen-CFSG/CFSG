module

public import Stellmacher.SectionNine.NineTenSecondExtraction
public import Stellmacher.SectionNine.NineTenGeneratingCriticalPair
public import Stellmacher.SectionFiveToSeven.SuppliedCriticalPathNormalization
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricConjugation

/-!
# Normalize both actual residual extraction witnesses in (9.10)

Normalize the path supplied by the second extracted neighbor while retaining
both original geometric extractions. The second extraction produces the new
initial vertex; the first produces the retained terminal neighbor from the
penultimate vertex. Both packets are transported by the same automorphism.
The path tail is unchanged before that transport, so its penultimate vertex
is exactly the one in the normalized first extraction.

Residual functoriality, commutator covariance and the exact geometric
conjugation theorem preserve the second prescribed-actor bound and every
outside-coatom actor bound of the first extraction. The same normalized
path, two explicit center noncontainments, two actual conjugators, terminal
neighbor and noncommuting initial/neighbor centers remain in the conclusion.
No identification with a smaller center-generated extraction group is made.

This is the same-witness normalization before (9.10)(2), printed p.57, with
the extra first-extraction data needed for the selected-support assertion
after (3)--(4). The existing normalized interfaces are adapters in
`NineTenNormalizedExtraction`; later proofs may use this stronger packet.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_normalized_extraction_with_residual_witnesses
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ∃ cp : CriticalPath ctx.Γ,
      cp.length = ctx.criticalPath.length ∧
      ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ cp.a'⁆ = ⊥ ∧
      (¬ ZAt ctx.Γ cp.a' ≤ VAt ctx.Γ cp.firstStep) ∧
      (¬ ZAt ctx.Γ cp.firstStep ≤ VAt ctx.Γ cp.a') ∧
      ∃ (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
        (data : NineThreeGeometricData ctx.Γ cp.firstStep second
          (VAt ctx.Γ cp.a') E A0 actor),
        IsCriticalPathOffset ctx.Γ cp 2 second ∧
        ctx.Γ.act data.x⁻¹ second = cp.a ∧
        neighbor ∈ neighborhood ctx.Γ cp.a' ∧
        actor ∈ ZAt ctx.Γ neighbor ∧
        ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥ ∧
        twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆ ∧
        ∃ (firstActor : G) (firstE firstA0 : Subgroup G)
          (firstData : NineThreeGeometricData ctx.Γ cp.a'
            (cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
            (VAt ctx.Γ cp.firstStep) firstE firstA0 firstActor),
          ctx.Γ.act firstData.x⁻¹
            (cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) = neighbor ∧
          ∀ b : G, b ∈ VAt ctx.Γ cp.firstStep → b ∉ firstA0 →
            twoResidualIn firstE ≤ ⁅twoResidualIn firstE, Subgroup.zpowers b⁆ := by
  let Γ := ctx.Γ
  let original := ctx.criticalPath
  let second := original.path ⟨2, by dsimp [original]; omega⟩
  obtain ⟨terminalNeighbor, hterminalNeighbor, _, _, _, _, _, hnoncomm,
      oldFirstActor, oldFirstE, oldFirstA0, oldFirstData, holdFirstNew, holdFirstActors⟩ :=
    nine_ten_first_extracted_neighbor_with_residual_witness ctx.toLocalContext hb
  obtain ⟨oldActor, oldE, oldA0, oldData, hactorZ, hgenerate, _, hcenterNoncomm, hactorComm⟩ :=
    nine_ten_second_extraction_with_actor_commutator ctx hb hfirstNot terminalNeighbor hterminalNeighbor hnoncomm
  let firstNeighbor := Γ.act oldData.x⁻¹ second
  have hfirstNeighbor : firstNeighbor ∈ neighborhood Γ original.firstStep := oldData.neighbor
  obtain ⟨hcritical, hcomm, _⟩ := nine_ten_generating_neighbor_critical_pair ctx hb
    hterminalNot terminalNeighbor firstNeighbor hterminalNeighbor hfirstNeighbor hgenerate
  let path : Fin (original.length + 1) → Γ.Vertex :=
    fun index => if index.val = 0 then firstNeighbor else original.path index
  have hstart : path 0 = firstNeighbor := by simp [path]
  have hend : path ⟨original.length, Nat.lt_succ_self _⟩ = original.a' := by
    simp [path, Nat.ne_of_gt original.length_pos, original.path_end]
  have hadj : ∀ index : Fin original.length,
      Γ.adjacent (path index.castSucc) (path index.succ) := by
    intro index
    by_cases hzero : index.val = 0
    · have heq : index = ⟨0, original.length_pos⟩ := Fin.ext hzero
      subst index
      simpa [path, original.path_first] using
        Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hfirstNeighbor)
    · simpa only [path, Fin.val_castSucc, Fin.val_succ, hzero, Nat.succ_ne_zero,
        if_false] using original.path_adj index
  obtain ⟨mover, cp, hlength, hleft, hright, hfirst, hpath⟩ :=
    exists_criticalPath_of_supplied_path ctx.sectionSeven Γ original
      firstNeighbor original.a' hcritical path hstart hend hadj
  have hfirstEq : cp.firstStep = Γ.act mover original.firstStep := by
    simpa [path, original.path_first] using hfirst
  have hcommMoved : ⁅ZAt Γ cp.a, ZAt Γ cp.a'⁆ = ⊥ := by
    change ⁅z Γ cp.a, z Γ cp.a'⁆ = ⊥
    rw [hleft, hright, z_act Γ mover firstNeighbor, z_act Γ mover original.a',
      ← Subgroup.map_commutator]
    change (⁅ZAt Γ firstNeighbor, ZAt Γ original.a'⁆).map _ = ⊥
    rw [hcomm, Subgroup.map_bot]
  have hterminalMoved : ¬ ZAt Γ cp.a' ≤ VAt Γ cp.firstStep := by
    change ¬ z Γ cp.a' ≤ v Γ cp.firstStep
    rw [hright, hfirstEq, z_act, v_act]
    exact fun hle => hterminalNot
      ((Subgroup.map_le_map_iff_of_injective (MulAut.conj mover⁻¹).injective).mp hle)
  have hfirstMoved : ¬ ZAt Γ cp.firstStep ≤ VAt Γ cp.a' := by
    change ¬ z Γ cp.firstStep ≤ v Γ cp.a'
    rw [hfirstEq, hright, z_act, v_act]
    exact fun hle => hfirstNot
      ((Subgroup.map_le_map_iff_of_injective (MulAut.conj mover⁻¹).injective).mp hle)
  have htransport := geometric_extraction_conjugation Γ original.firstStep second
    (VAt Γ original.a') oldE oldA0 oldActor oldData mover
  have hmodule : (VAt Γ original.a').map (MulAut.conj mover⁻¹).toMonoidHom =
      VAt Γ cp.a' := by
    change (v Γ original.a').map _ = v Γ cp.a'
    rw [hright, v_act]
  rw [← hfirstEq, hmodule, ← hleft] at htransport
  obtain ⟨data, _, hnew⟩ := htransport
  have hneighborMoved : Γ.act mover terminalNeighbor ∈ neighborhood Γ cp.a' := by
    apply (mem_neighborhood_iff_adjacent Γ).mpr
    rw [hright]
    exact adjacent_act Γ mover ((mem_neighborhood_iff_adjacent Γ).mp hterminalNeighbor)
  have hactorMoved : (MulAut.conj mover⁻¹) oldActor ∈
      ZAt Γ (Γ.act mover terminalNeighbor) := by
    change (MulAut.conj mover⁻¹) oldActor ∈ z Γ (Γ.act mover terminalNeighbor)
    rw [z_act Γ mover terminalNeighbor]
    exact Subgroup.mem_map_of_mem _ hactorZ
  have hcenterMoved : ⁅ZAt Γ cp.a, ZAt Γ (Γ.act mover terminalNeighbor)⁆ ≠ ⊥ := by
    intro hbot
    apply hcenterNoncomm
    apply Subgroup.map_injective (f := (MulAut.conj mover⁻¹).toMonoidHom)
      (MulAut.conj mover⁻¹).injective
    rw [Subgroup.map_bot]
    change ⁅z Γ cp.a, z Γ (Γ.act mover terminalNeighbor)⁆ = ⊥ at hbot
    rw [hleft, z_act Γ mover firstNeighbor, z_act Γ mover terminalNeighbor,
      ← Subgroup.map_commutator] at hbot
    exact hbot
  have hresidualMap : (twoResidualIn oldE).map (MulAut.conj mover⁻¹).toMonoidHom =
      twoResidualIn (oldE.map (MulAut.conj mover⁻¹).toMonoidHom) :=
    map_twoResidualAmbient_of_subgroup_image oldE
      (MulAut.conj mover⁻¹).toMonoidHom _ rfl
  have hactorCommMoved :
      twoResidualIn (oldE.map (MulAut.conj mover⁻¹).toMonoidHom) ≤
        ⁅twoResidualIn (oldE.map (MulAut.conj mover⁻¹).toMonoidHom),
          Subgroup.zpowers ((MulAut.conj mover⁻¹) oldActor)⁆ := by
    have h := Subgroup.map_mono (f := (MulAut.conj mover⁻¹).toMonoidHom) hactorComm
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hresidualMap] at h
    exact h
  let oldPenultimate := original.path
    ⟨original.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  change NineThreeGeometricData Γ original.a' oldPenultimate
    (VAt Γ original.firstStep) oldFirstE oldFirstA0 oldFirstActor at oldFirstData
  change Γ.act oldFirstData.x⁻¹ oldPenultimate = terminalNeighbor at holdFirstNew
  have hpenultimate : penultimate = Γ.act mover oldPenultimate := by
    have h := hpath ⟨original.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    have hnonzero : original.length - 1 ≠ 0 := by
      change 1 < original.length at hb
      omega
    simp only [path, hnonzero, if_false] at h
    have hindex : (⟨original.length - 1, by rw [hlength]; omega⟩ : Fin (cp.length + 1)) =
        ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      change original.length - 1 = cp.length - 1
      rw [hlength]
    change cp.path ⟨original.length - 1, _⟩ = Γ.act mover oldPenultimate at h
    rw [hindex] at h
    exact h
  have hfirstModule : (VAt Γ original.firstStep).map
      (MulAut.conj mover⁻¹).toMonoidHom = VAt Γ cp.firstStep := by
    change (v Γ original.firstStep).map _ = v Γ cp.firstStep
    rw [hfirstEq, v_act]
  have hfirstTransport := geometric_extraction_conjugation Γ original.a' oldPenultimate
    (VAt Γ original.firstStep) oldFirstE oldFirstA0 oldFirstActor oldFirstData mover
  rw [← hright, ← hpenultimate, hfirstModule, holdFirstNew] at hfirstTransport
  obtain ⟨firstData, _, hfirstNew⟩ := hfirstTransport
  have hfirstResidualMap : (twoResidualIn oldFirstE).map
      (MulAut.conj mover⁻¹).toMonoidHom =
      twoResidualIn (oldFirstE.map (MulAut.conj mover⁻¹).toMonoidHom) :=
    map_twoResidualAmbient_of_subgroup_image oldFirstE
      (MulAut.conj mover⁻¹).toMonoidHom _ rfl
  have hfirstActors : ∀ b : G, b ∈ VAt Γ cp.firstStep →
      b ∉ oldFirstA0.map (MulAut.conj mover⁻¹).toMonoidHom →
      twoResidualIn (oldFirstE.map (MulAut.conj mover⁻¹).toMonoidHom) ≤
        ⁅twoResidualIn (oldFirstE.map (MulAut.conj mover⁻¹).toMonoidHom),
          Subgroup.zpowers b⁆ := by
    intro b hb hb0
    rw [← hfirstModule] at hb
    obtain ⟨oldB, holdB, rfl⟩ := hb
    have holdNot : oldB ∉ oldFirstA0 := by
      intro hold
      exact hb0 (Subgroup.mem_map_of_mem _ hold)
    have h := Subgroup.map_mono (f := (MulAut.conj mover⁻¹).toMonoidHom)
      (holdFirstActors oldB holdB holdNot)
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hfirstResidualMap] at h
    exact h
  refine ⟨cp, hlength, hcommMoved, hterminalMoved, hfirstMoved,
    Γ.act mover terminalNeighbor, Γ.act mover second, (MulAut.conj mover⁻¹) oldActor,
    oldE.map (MulAut.conj mover⁻¹).toMonoidHom,
    oldA0.map (MulAut.conj mover⁻¹).toMonoidHom, data, ?_, hnew,
    hneighborMoved, hactorMoved, hcenterMoved, hactorCommMoved,
    (MulAut.conj mover⁻¹) oldFirstActor,
    oldFirstE.map (MulAut.conj mover⁻¹).toMonoidHom,
    oldFirstA0.map (MulAut.conj mover⁻¹).toMonoidHom, firstData,
    hfirstNew, hfirstActors⟩
  refine ⟨⟨2, by rw [hlength]; change 2 < original.length + 1; change 1 < original.length at hb; omega⟩,
    rfl, ?_⟩
  have hoffset := hpath ⟨2, by change 1 < original.length at hb; omega⟩
  simpa [path, second] using hoffset

end Stellmacher.SectionNine
