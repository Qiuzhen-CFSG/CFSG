module

public import Stellmacher.SectionNine.NineTenContainedTransvectionWreath
public import Stellmacher.SectionNine.NineEightSuppliedPathTransvection
public import Stellmacher.SectionFiveToSeven.SuppliedCriticalPathNormalization

/-!
# The reversed predecessor is the order-thirty-two wreath case

For a supplied commuting critical path, retain the actor on its first vertex,
its index-two displacement on the terminal module, and the containment of that
commutator in the supplied backward module. Normalize the whole path by one
graph action and apply the proved (9.5)--(9.7) wreath classification. Mapping
the resulting module, core quotient, and backward intersection through the
same conjugation equivalence returns the literal supplied endpoints.

This is the reoriented assertion (9.10)(6), printed p.58 of
`refs/files/stellmacher-n-group.pdf`. The theorem deliberately takes the
supplied path and actor explicitly so later extraction modules can retain the
original witnesses without identifying a new residual subgroup with one from
the source extraction.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u w

private theorem quotient_model_of_equiv_map
    {G : Type u} {M : Type w} [Group G] [Group M]
    (equiv : G ≃* G) (K U : Subgroup G)
    (hmodel : QuotientIsModel (K.map equiv.toMonoidHom)
      (U.map equiv.toMonoidHom) M) :
    QuotientIsModel K U M := by
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  let e := K.equivMapOfInjective equiv.toMonoidHom equiv.injective
  refine ⟨projection.comp e.toMonoidHom, hsurj.comp e.surjective, ?_⟩
  ext x
  change e x ∈ projection.ker ↔ (x : G) ∈ U
  rw [hker]
  change equiv (x : G) ∈ U.map equiv.toMonoidHom ↔ (x : G) ∈ U
  rw [Subgroup.mem_map_equiv]
  simp

public theorem nine_ten_predecessor_wreath_classification
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (left right : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hcomm : ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ = ⊥)
    (path : Fin (ctx.criticalPath.length + 1) → ctx.Γ.Vertex)
    (hstart : path 0 = left)
    (hend : path ⟨ctx.criticalPath.length, Nat.lt_succ_self _⟩ = right)
    (hadj : ∀ index : Fin ctx.criticalPath.length,
      ctx.Γ.adjacent (path index.castSucc) (path index.succ))
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ (path ⟨1, by omega⟩) ∧
      actor ∉ QAt ctx.Γ right)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ right, Subgroup.zpowers actor⁆ ⊔ ZAt ctx.Γ right)
      (ZAt ctx.Γ right) 2)
    (hcontain : ⁅VAt ctx.Γ right, Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ (path ⟨ctx.criticalPath.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) :
    Nat.card (VAt ctx.Γ right) = 2 ^ 5 ∧
      QuotientIsModel (GAt ctx.Γ right) (QAt ctx.Γ right) SL2TwoWreathC2 ∧
      Nat.card (VAt ctx.Γ right ⊓ VAt ctx.Γ
        (path ⟨ctx.criticalPath.length - 2,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2 ^ 3 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  obtain ⟨mover, normalized, hlength, hleft, hright, hnext, hpath⟩ :=
    exists_criticalPath_of_supplied_path ctx.sectionSeven Γ cp left right hcritical
      path hstart hend hadj
  let equiv := MulAut.conj mover⁻¹
  have hnormalizedComm : ⁅ZAt Γ normalized.a, ZAt Γ normalized.a'⁆ = ⊥ := by
    change ⁅Γ.z normalized.a, Γ.z normalized.a'⁆ = ⊥
    rw [hleft, hright, z_act, z_act, ← Subgroup.map_commutator]
    change (⁅ZAt Γ left, ZAt Γ right⁆).map _ = ⊥
    rw [hcomm, Subgroup.map_bot]
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    {ctx with criticalPath := normalized, commutator_eq := hnormalizedComm}
  have hlong : 3 < normalized.length := by
    rw [hlength]
    exact hb
  have hVright : (VAt Γ right).map equiv.toMonoidHom =
      VAt Γ normalized.a' := by
    rw [hright]
    exact (v_act Γ mover right).symm
  have hZright : (ZAt Γ right).map equiv.toMonoidHom =
      ZAt Γ normalized.a' := by
    rw [hright]
    exact (z_act Γ mover right).symm
  have hQright : (QAt Γ right).map equiv.toMonoidHom =
      QAt Γ normalized.a' := by
    rw [hright]
    exact (q_act Γ mover right).symm
  have hGright : (GAt Γ right).map equiv.toMonoidHom =
      GAt Γ normalized.a' := by
    rw [hright]
    exact (stabilizer_act Γ mover right).symm
  have hVnext : (VAt Γ (path ⟨1, by omega⟩)).map equiv.toMonoidHom =
      VAt Γ normalized.firstStep := by
    rw [hnext]
    exact (v_act Γ mover _).symm
  have hback : IsCriticalPathOffset Γ normalized
      (normalized.length - 2) (Γ.act mover
        (path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) := by
    refine ⟨⟨cp.length - 2, by rw [hlength]; omega⟩, ?_, ?_⟩
    · change cp.length - 2 = normalized.length - 2
      omega
    · exact hpath ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hVback : (VAt Γ (path ⟨cp.length - 2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).map equiv.toMonoidHom =
      VAt Γ (Γ.act mover (path ⟨cp.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) :=
    (v_act Γ mover _).symm
  let movedActor := equiv actor
  have hactorMoved : movedActor ∈ VAt Γ normalized.firstStep ∧
      movedActor ∉ QAt Γ normalized.a' := by
    constructor
    · rw [← hVnext]
      exact Subgroup.mem_map_of_mem equiv.toMonoidHom hactor.1
    · intro hmem
      apply hactor.2
      rw [← hQright] at hmem
      have hpre := Subgroup.mem_map_equiv.mp hmem
      simpa [movedActor] using hpre
  have hRmap : (⁅VAt Γ right, Subgroup.zpowers actor⁆).map
      equiv.toMonoidHom =
      ⁅VAt Γ normalized.a', Subgroup.zpowers movedActor⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hVright]
    rfl
  have hindexMoved : QuotientCardEq
      (⁅VAt Γ normalized.a', Subgroup.zpowers movedActor⁆ ⊔
        ZAt Γ normalized.a') (ZAt Γ normalized.a') 2 := by
    change Nat.card (_ : Subgroup G) = 2 * Nat.card (_ : Subgroup G)
    rw [← hRmap, ← hZright, ← Subgroup.map_sup,
      Subgroup.card_map_of_injective equiv.injective,
      Subgroup.card_map_of_injective equiv.injective]
    exact hindex
  have hcontainMoved : ⁅VAt Γ normalized.a', Subgroup.zpowers movedActor⁆ ≤
      VAt Γ (Γ.act mover (path ⟨cp.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) := by
    have hm := Subgroup.map_mono (f := equiv.toMonoidHom) hcontain
    rw [hRmap, hVback] at hm
    exact hm
  obtain ⟨hcard, hmodel, hinter⟩ := nine_ten_wreath_of_transvection_containment
    shifted hlong _ hback movedActor hactorMoved hindexMoved hcontainMoved
  have hcardBack : Nat.card (VAt Γ right) = 2 ^ 5 := by
    calc
      Nat.card (VAt Γ right) =
          Nat.card ((VAt Γ right).map equiv.toMonoidHom) :=
        (Subgroup.card_map_of_injective equiv.injective).symm
      _ = Nat.card (VAt Γ normalized.a') := by rw [hVright]
      _ = 2 ^ 5 := hcard
  have hinterBack : Nat.card (VAt Γ right ⊓ VAt Γ
      (path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) =
      2 ^ 3 := by
    have hmap :
        (VAt Γ right ⊓ VAt Γ (path ⟨cp.length - 2,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).map equiv.toMonoidHom =
          VAt Γ normalized.a' ⊓ VAt Γ (Γ.act mover (path ⟨cp.length - 2,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) := by
      rw [Subgroup.map_inf _ _ _ equiv.injective, hVright, hVback]
    have hcardMap : Nat.card ((VAt Γ right ⊓ VAt Γ (path ⟨cp.length - 2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).map equiv.toMonoidHom) =
        Nat.card (VAt Γ right ⊓ VAt Γ (path ⟨cp.length - 2,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) :=
      Subgroup.card_map_of_injective equiv.injective
    have hcardMapped := congrArg (fun K : Subgroup G => Nat.card K) hmap
    calc
      Nat.card (VAt Γ right ⊓ VAt Γ (path ⟨cp.length - 2,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) =
          Nat.card (VAt Γ normalized.a' ⊓ VAt Γ (Γ.act mover (path ⟨cp.length - 2,
            Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) : Subgroup G) :=
        hcardMap.symm.trans hcardMapped
      _ = 2 ^ 3 := hinter
  refine ⟨hcardBack, ?_, hinterBack⟩
  apply quotient_model_of_equiv_map equiv
  rwa [hGright, hQright]

end Stellmacher.SectionNine
