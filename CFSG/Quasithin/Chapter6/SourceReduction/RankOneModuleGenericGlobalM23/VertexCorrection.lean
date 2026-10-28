module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.EdgeRigidity
public import Theory.Mathieu.M23.QuasithinGeometry.SourceRecognition.CoreCorrection

/-!
# Correcting the original M23 vertex marking on its whole intersection

Transport the native core-fixing automorphism calculation through the same
heptad marking used by the original coset system. The original core lies in
I intersect L. Consequently a vertex comparison preserving Ix and L and
agreeing on this core can be conjugated inside L to agree on every element
of Ix, while preserving its entire edge-fixer image.

The final source applications construct the original system under both
linear-amalgam orientations. They prove the correction step, not the existence
of its initial core-compatible vertex comparison; that construction and the
subsequent similarity/M23 recognition remain outstanding.

Source: Aschbacher--Smith 5.2.20(5), printed pp.656--657, last paragraph of
its proof; the actual coset system comes from 5.2.19--22.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Transport core correction using the same whole heptad marking. -/
theorem heptad_marked_core_correction
    (J R : Subgroup G) (hRJ : R ≤ J) (ζ : J ≃* heptadStabilizer)
    (hcore : (pCore 2 J).map ζ.toMonoidHom = heptadKernel)
    (hmark : (R.subgroupOf J).map ζ.toMonoidHom =
      fourPairStabilizer.subgroupOf heptadStabilizer) :
    J.pCoreIn 2 ≤ R ∧
      ∀ α : MulAut R, (∀ u : (J.pCoreIn 2).subgroupOf R, α u = u) →
        ∃ u : (J.pCoreIn 2).subgroupOf R, α = MulAut.conj (u : R) := by
  have hUR : J.pCoreIn 2 ≤ R := by
    rintro g ⟨u,hu,rfl⟩
    have hz : ζ u ∈ heptadKernel := hcore ▸ mem_map_of_mem ζ.toMonoidHom hu
    have hm : ζ u ∈ (R.subgroupOf J).map ζ.toMonoidHom := by
      rw [hmark]
      exact (heptadKernelAmbient_le_twoPair ⟨ζ u,hz,rfl⟩).1
    exact (mem_map_iff_mem (f := ζ.toMonoidHom) ζ.injective).mp hm
  let e : R ≃* fourPairStabilizer :=
    (subgroupOfEquivOfLe hRJ).symm.trans
      ((ζ.subgroupMap (R.subgroupOf J)).trans
        ((MulEquiv.subgroupCongr hmark).trans
          (subgroupOfEquivOfLe fourPairStabilizer_le_heptad)))
  have he (r : R) : (e r : Sporadic.Mathieu.M23) =
      (ζ ⟨r,hRJ r.property⟩ : Sporadic.Mathieu.M23) := rfl
  have hcore_iff (r : R) : (e r : Sporadic.Mathieu.M23) ∈ heptadKernelAmbient ↔
      (r : G) ∈ J.pCoreIn 2 := by
    rw [he]
    change heptadStabilizer.subtype (ζ ⟨r,hRJ r.property⟩) ∈
      heptadKernel.map heptadStabilizer.subtype ↔
      J.subtype ⟨r,hRJ r.property⟩ ∈ (pCore 2 J).map J.subtype
    rw [mem_map_iff_mem (f := heptadStabilizer.subtype) heptadStabilizer.subtype_injective,←hcore]
    exact (mem_map_iff_mem (f := ζ.toMonoidHom) ζ.injective).trans
      (mem_map_iff_mem (f := J.subtype) J.subtype_injective).symm
  refine ⟨hUR,?_⟩
  intro α hα
  let β := MulAut.congr e α
  have hβ (v : heptadKernelAmbient.subgroupOf fourPairStabilizer) : β v = v := by
    have hr : (e.symm v : G) ∈ J.pCoreIn 2 :=
      (hcore_iff (e.symm v)).mp (by rw [e.apply_symm_apply]; exact v.property)
    have hh := hα ⟨e.symm v,hr⟩
    change α (e.symm v) = e.symm v at hh
    change e (α (e.symm v)) = v
    rw [hh,e.apply_symm_apply]
  obtain ⟨v,hv⟩ := fourPair_core_fixing_inner β hβ
  have hr : (e.symm v : G) ∈ J.pCoreIn 2 :=
    (hcore_iff (e.symm v)).mp (by rw [e.apply_symm_apply]; exact v.property)
  refine ⟨⟨e.symm v,hr⟩,?_⟩
  apply (MulAut.congr e).injective
  rw [show MulAut.congr e α = β from rfl,hv]
  apply MulEquiv.ext
  intro g
  change (v : fourPairStabilizer) * g * (v : fourPairStabilizer)⁻¹ =
    e (e.symm v * e.symm g * (e.symm v)⁻¹)
  rw [map_mul,map_mul,map_inv,e.apply_symm_apply,e.apply_symm_apply]

omit [Finite G] in
/-- A vertex comparison preserving the whole intersection and agreeing on the
original core can be corrected inside the edge fixer to agree on all of Ix. -/
theorem heptad_marked_vertex_correction
    (J R X L : Subgroup G) (hRJ : R ≤ J) (hRX : R ≤ X)
    (ζ : J ≃* heptadStabilizer)
    (hcore : (pCore 2 J).map ζ.toMonoidHom = heptadKernel)
    (hmark : (R.subgroupOf J).map ζ.toMonoidHom =
      fourPairStabilizer.subgroupOf heptadStabilizer)
    (hUL : J.pCoreIn 2 ≤ L)
    (β : X ≃* pairStabilizer)
    (hβR : (R.subgroupOf X).map β.toMonoidHom =
      fourPairStabilizer.subgroupOf pairStabilizer)
    (hβcore : ∀ r : R, (r : G) ∈ J.pCoreIn 2 →
      (β ⟨r,hRX r.property⟩ : Sporadic.Mathieu.M23) =
        (ζ ⟨r,hRJ r.property⟩ : Sporadic.Mathieu.M23))
    (hβedge : ∀ a : X, (a : G) ∈ L ↔
      (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) :
    ∃ β' : X ≃* pairStabilizer,
      (∀ r : R, (β' ⟨r,hRX r.property⟩ : Sporadic.Mathieu.M23) =
        (ζ ⟨r,hRJ r.property⟩ : Sporadic.Mathieu.M23)) ∧
      ∀ a : X, (a : G) ∈ L ↔
        (β' a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup := by
  let e : R ≃* fourPairStabilizer :=
    (subgroupOfEquivOfLe hRJ).symm.trans
      ((ζ.subgroupMap (R.subgroupOf J)).trans
        ((MulEquiv.subgroupCongr hmark).trans
          (subgroupOfEquivOfLe fourPairStabilizer_le_heptad)))
  let b : R ≃* fourPairStabilizer :=
    (subgroupOfEquivOfLe hRX).symm.trans
      ((β.subgroupMap (R.subgroupOf X)).trans
        ((MulEquiv.subgroupCongr hβR).trans
          (subgroupOfEquivOfLe (show fourPairStabilizer ≤ pairStabilizer from inf_le_right))))
  let α := b.trans e.symm
  have hα (u : (J.pCoreIn 2).subgroupOf R) : α u = u := by
    apply e.injective
    change e (e.symm (b u)) = e u
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hβcore u u.property
  obtain ⟨u,hu⟩ := (heptad_marked_core_correction J R hRJ ζ hcore hmark).2 α hα
  have hb (r : R) : b r = e ((u : R)*r*(u : R)⁻¹) := by
    have hh := congrArg (fun a : MulAut R => e (a r)) hu
    change e (e.symm (b r)) = _ at hh
    rwa [e.apply_symm_apply] at hh
  let ux : X := ⟨u.val,hRX u.val.property⟩
  let β' : X ≃* pairStabilizer := (MulAut.conj ux⁻¹).trans β
  refine ⟨β',?_,?_⟩
  · intro r
    have hh := congrArg Subtype.val (hb ((u : R)⁻¹*r*u))
    have hs : (u : R)*((u : R)⁻¹*r*u)*(u : R)⁻¹ = r := by group
    rw [hs] at hh
    change (β (ux⁻¹ * ⟨r,hRX r.property⟩ * (ux⁻¹)⁻¹) : Sporadic.Mathieu.M23) = _
    rw [inv_inv]
    exact hh
  · intro a
    have huL : (ux : G) ∈ L := hUL u.property
    have hn : (ux : G)⁻¹ ∈ normalizer (L : Set G) :=
      L.le_normalizer (L.inv_mem huL)
    have hh := hβedge (MulAut.conj ux⁻¹ a)
    change (ux : G)⁻¹*(a : G)*((ux : G)⁻¹)⁻¹ ∈ L ↔ _ at hh
    exact ((mem_normalizer_iff.mp hn (a : G))).trans hh

/-- The original nonmaximal linear coset system, with the core correction
needed for full-intersection vertex alignment. Every original marking is retained. -/
theorem Preparation.linear_nonmaximal_coset_core_correction
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J : Subgroup G, J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer),
      U.x = ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ∧
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧ U.H ≤ J ∧
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction ∧
      (U.H.subgroupOf J).map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
        fourPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom =
        fourTwoPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
        fourEdgeStabilizer.subgroupOf heptadStabilizer ∧
      (∀ a b : J, a • U.x = b • U.x ↔ ζ a • x.val = ζ b • x.val) ∧
      (∃ t : J, (t:G) ∈ U.H ∧ t • U.x = U.y ∧ ζ t • x.val = y.val) ∧
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) ∧
      J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup ∧
      ∀ α : MulAut (U.H ⊓ U.vertexGroup : Subgroup G),
        (∀ u : (J.pCoreIn 2).subgroupOf (U.H ⊓ U.vertexGroup), α u = u) →
        ∃ u : (J.pCoreIn 2).subgroupOf (U.H ⊓ U.vertexGroup),
          α = MulAut.conj (u : (U.H ⊓ U.vertexGroup : Subgroup G)) := by
  obtain ⟨J,hJ,hKJ,U,ζ,hx,hv,he0,hUJ,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,horbit,ht,hrigid⟩ :=
    d.linear_nonmaximal_rigid_coset_system h hH hp F hm hF he hnonmax
  have hcoreEdge : J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup := by
    rintro g ⟨u,hu,rfl⟩
    have hz : ζ u ∈ heptadKernel := hcore ▸ mem_map_of_mem ζ.toMonoidHom hu
    have hm : ζ u ∈ ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom := by
      rw [hedgeM]
      exact heptadKernelAmbient_le_twoPair ⟨ζ u,hz,rfl⟩
    exact (mem_map_iff_mem (f := ζ.toMonoidHom) ζ.injective).mp hm
  exact ⟨J,hJ,hKJ,U,ζ,hx,hv,he0,hUJ,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,
    (heptad_marked_core_correction J (U.H ⊓ U.vertexGroup)
      (inf_le_left.trans hUJ) ζ hcore hvM).2⟩

/-- The correction applies to the original source vertex and edge groups.
The initial core-compatible vertex comparison is still to be constructed. -/
theorem Preparation.linear_nonmaximal_vertex_correction
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J : Subgroup G, J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer)
        (hUJ : U.H ≤ J),
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) ∧
      ∀ β : U.vertexGroup ≃* pairStabilizer,
        ((U.H ⊓ U.vertexGroup).subgroupOf U.vertexGroup).map β.toMonoidHom =
          fourPairStabilizer.subgroupOf pairStabilizer →
        (∀ r : (U.H ⊓ U.vertexGroup : Subgroup G), (r : G) ∈ J.pCoreIn 2 →
          (β ⟨r,r.property.2⟩ : Sporadic.Mathieu.M23) =
            (ζ ⟨r,hUJ r.property.1⟩ : Sporadic.Mathieu.M23)) →
        (∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
          (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) →
        ∃ β' : U.vertexGroup ≃* pairStabilizer,
          (∀ r : (U.H ⊓ U.vertexGroup : Subgroup G),
            (β' ⟨r,r.property.2⟩ : Sporadic.Mathieu.M23) =
              (ζ ⟨r,hUJ r.property.1⟩ : Sporadic.Mathieu.M23)) ∧
          ∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
            (β' a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup := by
  obtain ⟨J,hJ,hKJ,U,ζ,hx,hv,he0,hUJ,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,hcorr⟩ :=
    d.linear_nonmaximal_coset_core_correction h hH hp F hm hF he hnonmax
  refine ⟨J,hJ,hKJ,U,ζ,hUJ,hv,he0,hrigid,?_⟩
  intro β hβR hβcore hβedge
  exact heptad_marked_vertex_correction J (U.H ⊓ U.vertexGroup)
    U.vertexGroup U.edgeGroup (inf_le_left.trans hUJ) inf_le_right ζ hcore hvM
    (hcoreEdge.trans inf_le_right) β hβR hβcore hβedge

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
