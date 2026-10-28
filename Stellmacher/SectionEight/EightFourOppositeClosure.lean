module

public import Stellmacher.SectionEight.LemmaEightOneOffender
public import Stellmacher.QuotientModuleOffenderFixedPoints

/-!
# The opposite-center normal closure: upper image bound

The closure is formed in the first-step stabilizer. The local versions
use only the actual Section Seven graph data; the canonical APIs are
definitionally graph-preserving wrappers with the same quotient action. Critical minimality puts it in the first-step core. It contains
the opposite center and is normal both in that stabilizer and in S. Every
conjugate of the opposite center is another vertex center at distance at
most the critical length from the initial vertex. The initial center
therefore acts on that vertex center. The local faithful index bound,
applied there, makes its image an offender for the original center, unless
the image is trivial. Closure generation then gives the upper inclusion
in the barred offender join. This is one direction of the assertion at
the opening of (8.4), journal p.38 of
`refs/files/stellmacher-n-group.pdf`; equality requires a separate
normal-Sylow generation argument. The final transport theorem gives source
(3) conditionally on that equality, for the witness's exact action.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

@[expose] public def oppositeClosureLocal
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2) : Subgroup H :=
  (Subgroup.normalClosure
    ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep) : Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
        (GAt ctx.Γ ctx.criticalPath.firstStep).subtype

private theorem opposite_center_le_next_core_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2) :
    ZAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlen := cp.length_pos
  have hdist : Γ.distance cp.a' cp.firstStep < cp.length := by
    rw [Γ.distance_symm]
    have hd := SevenSix.path_distance_le Γ cp 1 cp.length (by omega) le_rfl
    have hd' : Γ.distance cp.firstStep cp.a' ≤ cp.length - 1 := by
      simpa [cp.path_first, cp.path_end] using hd
    omega
  exact SevenSix.critical_minimality Γ cp hdist

public theorem opposite_closure_le_next_core_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2) :
    oppositeClosureLocal ctx ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hZend : z Γ cp.a' ≤ q Γ cp.firstStep := opposite_center_le_next_core_local ctx
  have hcore : q Γ cp.firstStep = twoCoreIn (stabilizer Γ cp.firstStep) :=
    Γ.twoCoreAt_def cp.firstStep
  rw [hcore] at hZend
  have hsub : (z Γ cp.a').subgroupOf (stabilizer Γ cp.firstStep) ≤
      pCore 2 (stabilizer Γ cp.firstStep) := by
    intro element helement
    obtain ⟨preimage, hpreimage, heq⟩ := hZend helement
    exact (Subtype.ext heq : preimage = element) ▸ hpreimage
  change oppositeClosureLocal ctx ≤ q Γ cp.firstStep
  rw [hcore]
  exact Subgroup.map_mono (Subgroup.normalClosure_le_normal hsub)

private theorem translated_center_le_opposite_closure_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (actor : H) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep) :
    z ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a') ≤ oppositeClosureLocal ctx := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := stabilizer Γ cp.firstStep
  let closure := Subgroup.normalClosure ((z Γ cp.a').subgroupOf next : Set next)
  have hZnext : z Γ cp.a' ≤ next :=
    (opposite_center_le_next_core_local ctx).trans (by
      change q Γ cp.firstStep ≤ next
      rw [q, Γ.twoCoreAt_def]
      exact SevenSix.twoCoreIn_le _)
  rw [z_act]
  rintro _ ⟨element, helement, rfl⟩
  let point : next := ⟨element, hZnext helement⟩
  let conjugator : next := ⟨actor⁻¹, next.inv_mem hactor⟩
  exact Subgroup.mem_map.mpr ⟨conjugator * point * conjugator⁻¹,
    (inferInstance : closure.Normal).conj_mem point
      (Subgroup.subset_normalClosure helement) conjugator, rfl⟩

public theorem opposite_center_le_opposite_closure_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2) :
    ZAt ctx.Γ ctx.criticalPath.a' ≤ oppositeClosureLocal ctx := by
  simpa only [ctx.Γ.act_one] using
    translated_center_le_opposite_closure_local ctx 1 (Subgroup.one_mem _)

public theorem opposite_closure_normal_next_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2) :
    NormalIn (oppositeClosureLocal ctx) (GAt ctx.Γ ctx.criticalPath.firstStep) := by
  refine ⟨Subgroup.map_subtype_le _, ?_⟩
  change ((Subgroup.normalClosure
    ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep) : Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
        (GAt ctx.Γ ctx.criticalPath.firstStep).subtype
          |>.comap (GAt ctx.Γ ctx.criticalPath.firstStep).subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  infer_instance

public theorem opposite_closure_normal_sylow_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2) :
    NormalIn (oppositeClosureLocal ctx) S := by
  have hle : oppositeClosureLocal ctx ≤ S :=
    (opposite_closure_le_next_core_local ctx).trans
      (SevenSix.local_cores_le_edge_sylow
        (ctx.sectionSeven) ctx.Γ ctx.criticalPath).2
  refine ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_⟩
  exact (ctx.criticalPath.S_le_edge_stabilizers.trans inf_le_right).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (opposite_closure_normal_next_local ctx).1).mp (opposite_closure_normal_next_local ctx).2)

private theorem initial_center_le_stabilizer_of_distance_le_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (endpoint : ctx.Γ.Vertex)
    (hdist : ctx.Γ.distance ctx.criticalPath.a endpoint ≤ ctx.criticalPath.length) :
    z ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ endpoint := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let distance := Γ.distance cp.a endpoint
  by_cases hzero : distance = 0
  · have heq : cp.a = endpoint := (Γ.distance_zero_iff _ _).mp hzero
    rw [← heq]
    have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
    have hqP : q Γ cp.a ≤ stabilizer Γ cp.a := by
      rw [q, Γ.twoCoreAt_def]
      exact SevenSix.twoCoreIn_le _
    exact ((lemma_seven_three h Γ).center_core _ _ hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((Subgroup.map_subtype_le _).trans hqP))
  have hpos : 0 < distance := Nat.pos_of_ne_zero hzero
  obtain ⟨path, hstart, hend, hadj⟩ := Γ.distance_path cp.a endpoint
  let penult := path ⟨distance - 1, by omega⟩
  have hpenult : Γ.distance cp.a penult ≤ distance - 1 := by
    let initialPath : Fin (distance - 1 + 1) → Γ.Vertex :=
      fun index => path ⟨index, by omega⟩
    have hbound := Γ.distance_le_of_path (distance - 1) initialPath
      (fun index => by
        convert hadj ⟨index, by omega⟩ using 1 <;> rfl)
    simpa [initialPath, hstart, penult] using hbound
  have hZaQ : z Γ cp.a ≤ q Γ penult :=
    SevenSix.critical_minimality Γ cp (by change distance ≤ cp.length at hdist; omega)
  have hlastadj : Γ.adjacent penult endpoint := by
    have hedge := hadj ⟨distance - 1, by omega⟩
    have hsucc : (⟨distance - 1, by omega⟩ : Fin distance).succ =
        ⟨distance, Nat.lt_succ_self _⟩ := Fin.ext (by simp; omega)
    rw [hsucc, hend] at hedge
    exact hedge
  exact hZaQ.trans ((lemma_seven_three h Γ).sylow_and_core _ _
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj) default).2.2

private theorem translated_endpoint_distance_le_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (actor : H) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep) :
    ctx.Γ.distance ctx.criticalPath.a (ctx.Γ.act actor ctx.criticalPath.a') ≤
      ctx.criticalPath.length := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlen := cp.length_pos
  have hfix : Γ.act actor cp.firstStep = cp.firstStep := by
    change actor ∈ (Γ.vertexStabilizer cp.firstStep : Set H) at hactor
    rw [Γ.stabilizer_def] at hactor
    exact hactor
  let path : Fin (cp.length + 1) → Γ.Vertex :=
    Fin.cases cp.a (fun index => Γ.act actor (cp.path index.succ))
  have hstart : path 0 = cp.a := rfl
  have hend : path ⟨cp.length, Nat.lt_succ_self _⟩ = Γ.act actor cp.a' := by
    have heq : (⟨cp.length, Nat.lt_succ_self _⟩ : Fin (cp.length + 1)) =
        (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ := Fin.ext (by simp; omega)
    simp only [heq, path, Fin.cases_succ]
    congr 1
    convert cp.path_end using 1
    congr 1
    apply Fin.ext
    simp
    omega
  have hadj : ∀ index : Fin cp.length, Γ.adjacent (path index.castSucc) (path index.succ) := by
    intro index
    by_cases hzero : index.val = 0
    · have hindex : index = ⟨0, hlen⟩ := Fin.ext hzero
      subst index
      simpa [path, cp.path_first, hfix] using cp.firstStep_adj
    · have hpred : index.castSucc =
          (⟨index.val - 1, by omega⟩ : Fin cp.length).succ := Fin.ext (by simp; omega)
      rw [hpred]
      simp only [path, Fin.cases_succ]
      have hedge := adjacent_act Γ actor (cp.path_adj index)
      convert hedge using 1
      congr 2
      apply Fin.ext
      simp
      omega
  simpa only [hstart, hend] using Γ.distance_le_of_path cp.length path hadj

private theorem translated_center_image_le_oneJ_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (actor : H) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hYS : z ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a') ≤ S) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ((z ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a')).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a)).map w.projection ≤
      SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a)
        ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let endpoint := Γ.act actor cp.a'
  have hSP : S ≤ stabilizer Γ cp.a := cp.S_le_edge_stabilizers.trans inf_le_left
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hlen := cp.length_pos
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hsucc : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := Fin.ext (by simp; omega)
    rw [hsucc, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hneighbor := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    (adjacent_act Γ actor hlastadj)
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hneighbor
  by_cases hcentral : z Γ cp.a ≤ Subgroup.centralizer (z Γ endpoint : Set H)
  · have hreverse : z Γ endpoint ≤ Subgroup.centralizer (z Γ cp.a : Set H) := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
    apply le_trans (show ((z Γ endpoint).subgroupOf (stabilizer Γ cp.a)).map w.projection ≤ ⊥ from ?_) bot_le
    rintro _ ⟨element, helement, rfl⟩
    change w.projection element = 1
    change element ∈ w.projection.ker
    rw [w.kernel_eq]
    exact ⟨element.property, hreverse helement⟩
  · exact le_sSup (w.oneA_of_card_le (z Γ endpoint) S hYS hSP
      (local_quotient_index_bound h Γ endpoint hneighbor (z Γ cp.a)
        (initial_center_le_stabilizer_of_distance_le_local ctx endpoint
          (translated_endpoint_distance_le_local ctx actor hactor)) hcentral))

public theorem opposite_closure_image_le_oneJ_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ((oppositeClosureLocal ctx).subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection ≤
      SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a)
        ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  let := w.groupX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let initial := stabilizer Γ cp.a
  let next := stabilizer Γ cp.firstStep
  let J := SectionOne.oneJ (V := ZAt Γ cp.a) ((S.subgroupOf initial).map w.projection)
  let lift := (J.comap w.projection).map initial.subtype
  have hS1S : oppositeClosureLocal ctx ≤ S :=
    (opposite_closure_le_next_core_local ctx).trans
      (SevenSix.local_cores_le_edge_sylow
        (ctx.sectionSeven) Γ cp).2
  have hSinitial : S ≤ initial := cp.S_le_edge_stabilizers.trans inf_le_left
  have hclosure : oppositeClosureLocal ctx ≤ lift := by
    apply Subgroup.map_le_iff_le_comap.mpr
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro element helement
    obtain ⟨point, hpoint, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp helement
    obtain ⟨actor, rfl⟩ := isConj_iff.mp hconj
    let endpoint := Γ.act (actor : H)⁻¹ cp.a'
    have hYclosure : z Γ endpoint ≤ oppositeClosureLocal ctx :=
      translated_center_le_opposite_closure_local ctx _ (next.inv_mem actor.property)
    have hYimage := translated_center_image_le_oneJ_local ctx w _
      (next.inv_mem actor.property) (hYclosure.trans hS1S)
    have hmem : (actor : H) * (point : H) * (actor : H)⁻¹ ∈ z Γ endpoint := by
      rw [z_act]
      exact Subgroup.mem_map.mpr ⟨point, hpoint, by simp⟩
    let imagePoint : initial := ⟨_, hSinitial (hYclosure.trans hS1S hmem)⟩
    exact Subgroup.mem_map.mpr ⟨imagePoint,
      hYimage (Subgroup.mem_map_of_mem w.projection hmem), rfl⟩
  change ((oppositeClosureLocal ctx).subgroupOf initial).map w.projection ≤ J
  rintro _ ⟨element, helement, rfl⟩
  obtain ⟨point, hpoint, heq⟩ := hclosure helement
  have heq' : point = element := Subtype.ext heq
  exact heq' ▸ hpoint

public theorem fixed_center_eq_opposite_closure_centralizer_of_image_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (himage : let _ := w.groupX
      let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
      ((oppositeClosureLocal ctx).subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection =
        SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a)
          ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection)) :
    w.oneJFixedPoints S = ZAt ctx.Γ ctx.criticalPath.a ⊓
      Subgroup.centralizer (oppositeClosureLocal ctx : Set H) := by
  let h := ctx.sectionSeven
  have hS1A : oppositeClosureLocal ctx ≤ GAt ctx.Γ ctx.criticalPath.a :=
    (opposite_closure_le_next_core_local ctx).trans
      ((SevenSix.local_cores_le_edge_sylow h ctx.Γ ctx.criticalPath).2.trans
        (ctx.criticalPath.S_le_edge_stabilizers.trans inf_le_left))
  have hfixed := w.fixedPoints_map_subtype (oppositeClosureLocal ctx) hS1A
  dsimp only at hfixed himage
  rw [himage] at hfixed
  exact hfixed

@[expose] public def oppositeClosure
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) : Subgroup H :=
  oppositeClosureLocal ctx.toLocalContext

public theorem opposite_closure_le_next_core
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) :
    oppositeClosure ctx ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  exact opposite_closure_le_next_core_local ctx.toLocalContext

public theorem opposite_center_le_opposite_closure
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) :
    ZAt ctx.Γ ctx.criticalPath.a' ≤ oppositeClosure ctx := by
  exact opposite_center_le_opposite_closure_local ctx.toLocalContext

public theorem opposite_closure_normal_next
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) :
    NormalIn (oppositeClosure ctx) (GAt ctx.Γ ctx.criticalPath.firstStep) := by
  exact opposite_closure_normal_next_local ctx.toLocalContext

public theorem opposite_closure_normal_sylow
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) :
    NormalIn (oppositeClosure ctx) S := by
  exact opposite_closure_normal_sylow_local ctx.toLocalContext

public theorem opposite_closure_image_le_oneJ
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ((oppositeClosure ctx).subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection ≤
      SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a)
        ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  exact opposite_closure_image_le_oneJ_local ctx.toLocalContext w

public theorem fixed_center_eq_opposite_closure_centralizer_of_image
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (himage : let _ := w.groupX
      let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
      ((oppositeClosure ctx).subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection =
        SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a)
          ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection)) :
    w.oneJFixedPoints S = ZAt ctx.Γ ctx.criticalPath.a ⊓
      Subgroup.centralizer (oppositeClosure ctx : Set H) := by
  exact fixed_center_eq_opposite_closure_centralizer_of_image_local ctx.toLocalContext w himage

end Stellmacher.SectionEight
