module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes.Model

/-!
# Full original planes in the common three-space

The natural root-centralizer displacement plane lies in the marked three-space.
Fixed vectors lift through the actual chosen central quotient. Mapping their
commutators through the same projection gives the entire natural plane; taking
its full preimage adjoins exactly C_V(L). The action intertwiner identifies
these displacements with the literal ambient commutators [C_V(D),A].

Source applies this to every original long-root preimage and pairs each result
with its reciprocal full plane, retaining both covering centers. This does not
assert equality of those centers or of the unaugmented plane families.
Source: Aschbacher--Smith B.4.6 and 11.2.2(5), printed pp.88--90,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-- All the root planes reconstructed on the original side lie in the same
literal natural three-space. -/
theorem root_plane_le_three (u : Model F)
    (hZ : LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom ≤ longRootLocal) :
    (naturalPlane F).map (Natural.action F u) ≤
      (NaturalOffenders.upper (F:=F)).comap (Restricted.NaturalCoordinates.coordinates F) := by
  have hh : ((naturalPlane F).map (Natural.action F u)).restrictScalars (ZMod 2) ≤
      ((NaturalOffenders.upper (F:=F)).comap
        (Restricted.NaturalCoordinates.coordinates F)).restrictScalars (ZMod 2) := by
    rw [←root_commutator F u hZ]
    apply Submodule.span_le.mpr
    rintro _ ⟨b,⟨p,rfl⟩,v,-,rfl⟩
    change Restricted.NaturalCoordinates.coordinates F
      (Natural.action F (EvenTwoRank.elementaryEmbedding F p) v-v) ∈ NaturalOffenders.upper
    rw [map_sub]
    have he := (Restricted.NaturalCoordinates.repEquiv F).isIntertwining
      (EvenTwoRank.elementaryEmbedding F p) v
    change Restricted.NaturalCoordinates.coordinates F
        (Natural.action F (EvenTwoRank.elementaryEmbedding F p) v) =
      Restricted.NaturalCoordinates.action F (EvenTwoRank.elementaryEmbedding F p)
        (Restricted.NaturalCoordinates.coordinates F v) at he
    rw [he]
    simp [EvenTwoRank.elementaryEmbedding,EvenTwoRank.elementaryParameters,unipotentProduct,
      Matrix.vecHead,Matrix.vecTail]
  exact hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))

private def subgroupSpace (B : Subgroup G) : Submodule (ZMod 2) D.space :=
  AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm
    (B.comap (V.subtype.comp D.spaceEquiv.toMonoidHom)))

/-- The original full plane reconstructed from the fixed-space commutator.
The whole covering center is adjoined, using the original action and projection. -/
theorem original_root_plane (A : Subgroup G) (a : A →* Model S.field.Carrier)
    (hact : ∀ (x : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)
    (u : Model S.field.Carrier)
    (hZ : LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom ≤ longRootLocal) :
    ⁅A,V ⊓ centralizer (RootPullback.rootPreimage A a
      (LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom) : Set G)⁆ ⊔
      (V ⊓ centralizer (L : Set G)) =
      (Coordinates.g2 m).preimage ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier u)) := by
  let Z := LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom
  let E := V ⊓ centralizer (RootPullback.rootPreimage A a Z : Set G)
  let σ := Preliminary.markedAction D m
  let τ := NaturalOffenders.binaryNatural (F:=S.field.Carrier)
  let p := Preliminary.markedProjection D m
  let P := (naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier u)
  let U := subspaceCommutator σ (fixedSpace σ Z) (EvenTwoRank.elementary S.field.Carrier)
  have hZa : Z ≤ a.range := ha.symm ▸ RootCentralizers.root_le_elementary S.field.Carrier ⟨hZ,u,rfl⟩
  have hf : (fixedSpace σ Z).map p.toLinearMap = fixedSpace τ Z := by
    rw [marked_fixedSpace D S m Z,Submodule.map_comap_eq,
      LinearMap.range_eq_top.mpr (Preliminary.markedProjection_isCover D m).1,top_inf_eq]
    rfl
  have hm : U.map p.toLinearMap = P.restrictScalars (ZMod 2) := by
    have hh := subspaceCommutator_map_embedding τ σ (MonoidHom.id _) p.toLinearMap
      (fun b v => (LinearMap.congr_fun (p.isIntertwining' b) v).symm)
      (EvenTwoRank.elementary S.field.Carrier) (fixedSpace σ Z)
    rw [Subgroup.map_id,hf] at hh
    exact hh.symm.trans (root_commutator S.field.Carrier u hZ)
  have hpre : (P.restrictScalars (ZMod 2)).comap p.toLinearMap =
      U ⊔ Preliminary.centralSpace D := by
    rw [←hm,Submodule.comap_map_eq]
    congr 1
    exact Preliminary.markedProjection_ker D m
  let X := ⁅A,E⁆ ⊔ (V ⊓ centralizer (L : Set G))
  have hmove : U ≤ subgroupSpace D X := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,v,hv,rfl⟩
    rw [←ha] at hb
    obtain ⟨x,rfl⟩ := hb
    have hvE : (D.spaceEquiv (Multiplicative.ofAdd v) : G) ∈ E := by
      refine ⟨(D.spaceEquiv (Multiplicative.ofAdd v)).property,?_⟩
      rintro _ ⟨y,hy,rfl⟩
      exact (ReciprocalRoots.fixed_iff_commute D S m A a hact y v).mp (hv ⟨a y,hy⟩)
    let j : Multiplicative D.space →* G := V.subtype.comp D.spaceEquiv.toMonoidHom
    change j (Multiplicative.ofAdd (σ (a x) v-v)) ∈ X
    rw [ofAdd_sub,map_div,div_eq_mul_inv]
    change (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) *
      (D.spaceEquiv (Multiplicative.ofAdd v) : G)⁻¹ ∈ X
    rw [hact]
    exact (show ⁅A,E⁆ ≤ X from le_sup_left)
      (commutator_mem_commutator x.property hvE)
  have hcenter : Preliminary.centralSpace D ≤ subgroupSpace D X := by
    intro v hv
    exact (show V ⊓ centralizer (L : Set G) ≤ X from le_sup_right)
      ⟨(D.spaceEquiv (Multiplicative.ofAdd v)).property,(Preliminary.mem_centralSpace_iff D v).mp hv⟩
  apply le_antisymm
  · apply sup_le
    · apply commutator_le.mpr
      intro b hb v hv
      let w : D.space := (D.spaceEquiv.symm ⟨v,hv.1⟩).toAdd
      have hw : w ∈ fixedSpace σ Z := by
        rw [marked_fixedSpace D S m Z]
        apply (ReciprocalRoots.rootCentralizer_mem D S m A a hact Z hZa w).mp
        simpa only [w,ofAdd_toAdd,MulEquiv.apply_symm_apply] using hv
      have hmov : σ (a ⟨b,hb⟩) w-w ∈ U :=
        Submodule.subset_span ⟨a ⟨b,hb⟩,ha ▸ (show a ⟨b,hb⟩ ∈ a.range from ⟨⟨b,hb⟩,rfl⟩),w,hw,rfl⟩
      have hp : p (σ (a ⟨b,hb⟩) w-w) ∈ P := by
        change _ ∈ P.restrictScalars (ZMod 2)
        rw [←hm]
        exact ⟨_,hmov,rfl⟩
      have hh : (D.spaceEquiv (Multiplicative.ofAdd (σ (a ⟨b,hb⟩) w-w)) : G) ∈
          (Coordinates.g2 m).preimage P := by
        apply ((Coordinates.g2 m).mem_preimage P _).mpr
        change m.linearEquiv ((Preliminary.centralSpace D).mkQ
          (D.spaceEquiv.symm (D.spaceEquiv (Multiplicative.ofAdd (σ (a ⟨b,hb⟩) w-w)))).toAdd) ∈ P
        rw [D.spaceEquiv.symm_apply_apply]
        exact hp
      have he : (D.spaceEquiv (Multiplicative.ofAdd (σ (a ⟨b,hb⟩) w-w)) : G) = ⁅b,v⁆ := by
        rw [ofAdd_sub,map_div,Subgroup.coe_div,div_eq_mul_inv]
        change (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a ⟨b,hb⟩) w)) : G) *
          (D.spaceEquiv (Multiplicative.ofAdd w) : G)⁻¹ = _
        rw [hact]
        simp only [w,ofAdd_toAdd,MulEquiv.apply_symm_apply]
        rfl
      exact he ▸ hh
    · rw [←(Coordinates.g2 m).preimage_bot]
      exact ((Coordinates.g2 m).preimage_le_iff _ _).mpr bot_le
  · intro v hv
    let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
    let w : D.space := (D.spaceEquiv.symm v').toAdd
    have hw : w ∈ (P.restrictScalars (ZMod 2)).comap p.toLinearMap :=
      ((Coordinates.g2 m).mem_preimage P v').mp hv
    rw [hpre] at hw
    have hh := (sup_le hmove hcenter) hw
    change (D.spaceEquiv (Multiplicative.ofAdd w) : G) ∈ X at hh
    simpa only [w,v',ofAdd_toAdd,MulEquiv.apply_symm_apply] using hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
