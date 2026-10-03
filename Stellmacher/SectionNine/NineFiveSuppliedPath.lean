module
public import Stellmacher.SectionNine.LemmaNineFive
public import Stellmacher.SectionFiveToSeven.SuppliedCriticalPathNormalization

/-!
# Apply (9.5) on an entire supplied commuting critical path

The ambient transvection-support dichotomy transfers to a supplied path of the
known critical length whose endpoints form a commuting critical pair. The
same normalization actor carries every vertex, the transvection actor, its
commutator, and the literal quotient kernel. In particular the backward
offset remains the supplied vertex, rather than one chosen by a new path.

Apply the proved full-path normalization, map the original actor data and
cardinal identity by conjugation, and invoke ambient (9.5). Subgroup cardinality
and intersection transport return the module orders; composing the quotient
maps with the actual conjugation equivalence returns their exact models.

This is the reorientation needed by Stellmacher (9.9)(3), printed p.56/PDF p.46
of `refs/files/stellmacher-n-group.pdf`. It requires genuine criticality,
commuting centers, and the complete adjacent path as inputs.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u w

private theorem quotient_model_of_equiv_map
    {G : Type u} {M : Type w} [Group G] [Group M]
    (equiv : G ≃* G) (K U : Subgroup G)
    (hmodel : QuotientIsModel (K.map equiv.toMonoidHom) (U.map equiv.toMonoidHom) M) :
    QuotientIsModel K U M := by
  obtain ⟨projection,hsurj,hker⟩ := hmodel
  let e := K.equivMapOfInjective equiv.toMonoidHom equiv.injective
  refine ⟨projection.comp e.toMonoidHom,hsurj.comp e.surjective,?_⟩
  ext x
  change e x ∈ projection.ker ↔ (x:G) ∈ U
  rw [hker]
  change equiv (x:G) ∈ U.map equiv.toMonoidHom ↔ (x:G) ∈ U
  rw [Subgroup.mem_map_equiv]
  simp

public theorem nine_five_of_supplied_critical_path
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (left right : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hcomm : ⁅ZAt ctx.Γ left,ZAt ctx.Γ right⁆ = ⊥)
    (path : Fin (ctx.criticalPath.length + 1) → ctx.Γ.Vertex)
    (hstart : path 0 = left)
    (hend : path ⟨ctx.criticalPath.length,Nat.lt_succ_self _⟩ = right)
    (hadj : ∀ index : Fin ctx.criticalPath.length,
      ctx.Γ.adjacent (path index.castSucc) (path index.succ))
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ (path ⟨1,by omega⟩) ∧ actor ∉ QAt ctx.Γ right)
    (hindex : QuotientCardEq (⁅VAt ctx.Γ right,Subgroup.zpowers actor⁆ ⊔ ZAt ctx.Γ right)
      (ZAt ctx.Γ right) 2)
    (hcontain : ⁅VAt ctx.Γ right,Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ (path ⟨ctx.criticalPath.length - 2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) :
    (Nat.card (VAt ctx.Γ right) = 2^3 ∧
      QuotientIsModel (GAt ctx.Γ right) (QAt ctx.Γ right) SL2Two) ∨
    (Nat.card (VAt ctx.Γ right) = 2^5 ∧
      QuotientIsModel (GAt ctx.Γ right) (QAt ctx.Γ right) SL2TwoWreathC2 ∧
      Nat.card (VAt ctx.Γ right ⊓ VAt ctx.Γ
        (path ⟨ctx.criticalPath.length - 2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let back := path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  obtain ⟨mover,normalized,hlength,hleft,hright,hnext,hpath⟩ :=
    exists_criticalPath_of_supplied_path ctx.sectionSeven Γ cp left right hcritical
      path hstart hend hadj
  let equiv := MulAut.conj mover⁻¹
  have hnormalizedComm : ⁅Γ.z normalized.a,Γ.z normalized.a'⁆ = ⊥ := by
    rw [hleft,hright,z_act,z_act,← Subgroup.map_commutator]
    change (⁅ZAt Γ left,ZAt Γ right⁆).map _ = ⊥
    rw [hcomm,Subgroup.map_bot]
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    {ctx with criticalPath:=normalized,commutator_eq:=hnormalizedComm}
  have hback : IsCriticalPathOffset Γ normalized (normalized.length-2) (Γ.act mover back) := by
    refine ⟨⟨cp.length-2,by rw [hlength]; omega⟩,by change cp.length-2=normalized.length-2; omega,?_⟩
    exact hpath ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hVright : (VAt Γ right).map equiv.toMonoidHom = VAt Γ normalized.a' := by
    rw [hright]
    exact (v_act Γ mover right).symm
  have hZright : (ZAt Γ right).map equiv.toMonoidHom = ZAt Γ normalized.a' := by
    rw [hright]
    exact (z_act Γ mover right).symm
  have hQright : (QAt Γ right).map equiv.toMonoidHom = QAt Γ normalized.a' := by
    rw [hright]
    exact (q_act Γ mover right).symm
  have hGright : (GAt Γ right).map equiv.toMonoidHom = GAt Γ normalized.a' := by
    rw [hright]
    exact (stabilizer_act Γ mover right).symm
  have hVnext : (VAt Γ (path ⟨1,by omega⟩)).map equiv.toMonoidHom = VAt Γ normalized.firstStep := by
    rw [hnext]
    exact (v_act Γ mover _).symm
  have hVback : (VAt Γ back).map equiv.toMonoidHom = VAt Γ (Γ.act mover back) :=
    (v_act Γ mover back).symm
  have hactorMoved : equiv actor ∈ VAt Γ normalized.firstStep ∧
      equiv actor ∉ QAt Γ normalized.a' := by
    constructor
    · rw [← hVnext]
      exact Subgroup.mem_map_of_mem equiv.toMonoidHom hactor.1
    · rw [← hQright,Subgroup.mem_map_equiv]
      simpa only [MulEquiv.symm_apply_apply] using hactor.2
  have hRmap : (⁅VAt Γ right,Subgroup.zpowers actor⁆).map equiv.toMonoidHom =
      ⁅VAt Γ normalized.a',Subgroup.zpowers (equiv actor)⁆ := by
    rw [Subgroup.map_commutator,MonoidHom.map_zpowers,hVright]
    rfl
  have hindexMoved : QuotientCardEq
      (⁅VAt Γ normalized.a',Subgroup.zpowers (equiv actor)⁆ ⊔ ZAt Γ normalized.a')
      (ZAt Γ normalized.a') 2 := by
    change Nat.card (_ : Subgroup G) = 2 * Nat.card (_ : Subgroup G)
    rw [← hRmap,← hZright,← Subgroup.map_sup,
      Subgroup.card_map_of_injective equiv.injective,Subgroup.card_map_of_injective equiv.injective]
    exact hindex
  have hcontainMoved : ⁅VAt Γ normalized.a',Subgroup.zpowers (equiv actor)⁆ ≤
      VAt Γ (Γ.act mover back) := by
    rw [← hRmap,← hVback]
    exact Subgroup.map_mono hcontain
  have hresult := lemma_nine_five_ambient shifted (by change 1<normalized.length; rw [hlength]; exact hb)
    (Γ.act mover back) hback (equiv actor) hactorMoved hindexMoved hcontainMoved
  have hcardV : Nat.card (VAt Γ normalized.a') = Nat.card (VAt Γ right) := by
    rw [← hVright,Subgroup.card_map_of_injective equiv.injective]
  have hcardI : Nat.card (VAt Γ normalized.a' ⊓ VAt Γ (Γ.act mover back) : Subgroup G) =
      Nat.card (VAt Γ right ⊓ VAt Γ back : Subgroup G) := by
    rw [← hVright,← hVback,← Subgroup.map_inf _ _ _ equiv.injective,
      Subgroup.card_map_of_injective equiv.injective]
  rcases hresult with ⟨hcard,hmodel⟩ | ⟨hcard,hmodel,hintersection⟩
  · left
    refine ⟨hcardV ▸ hcard,?_⟩
    apply quotient_model_of_equiv_map equiv
    rwa [hGright,hQright]
  · right
    refine ⟨hcardV ▸ hcard,?_,hcardI ▸ hintersection⟩
    apply quotient_model_of_equiv_map equiv
    rwa [hGright,hQright]

end Stellmacher.SectionNine
