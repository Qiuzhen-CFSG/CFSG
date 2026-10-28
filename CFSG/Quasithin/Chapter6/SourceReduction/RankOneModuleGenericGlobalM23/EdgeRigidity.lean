module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.System
public import Theory.GroupTheory.Recognition.QuasithinM23.EdgeRigidity
public import Theory.GroupTheory.Recognition.QuasithinM23.SemilinearQuotient
public import Theory.Mathieu.M23.QuasithinGeometry.SourceRecognition.LocalEdgeCard

/-!
# Rigidity of the original M23-shaped coset edge fixer

The compatible heptad marking puts O₂(J) inside the actual local edge fixer
I ∩ L = UB and gives |UB| = 48. This elementary sixteen-group differs from
O₂(L), since their original ambient normalizers are J and M and the residual
escapes M. Transporting the affine rigidity theorem through the original
linear comparison therefore proves C_Aut(L)(UB) = 1.

The resulting coset system retains every original subgroup marking and all
three generation identities. This discharges hypothesis (1) in the final
uniqueness-system argument of Aschbacher--Smith 5.2.10, printed p.657.
The compatible vertex marking from 5.2.20(5) and the ambient recognition
application remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem coset_edge_rigid
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
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer)
    (hUEdge : U.edgeGroup = L) (hUle : U.H ≤ J)
    (hcore : (pCore 2 J).map ζ.toMonoidHom = heptadKernel)
    (hmark : ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom =
      fourTwoPairStabilizer.subgroupOf heptadStabilizer) :
    AutomorphismRigid (U.H.subgroupOf U.edgeGroup) := by
  have hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G) :=
    fun hk => hKJ.ne (hk.2 J hJ.1 hKJ.le).symm
  obtain ⟨_,hn,hF4,hcores,_,hNV,_⟩ :=
    d.linear_nonmaximal_core_geometry h hH hp F hm hF he hnonmax
  obtain ⟨_,_,_,_,hNU,_,_,_⟩ := d.linear_exceptional_local h hH hp F hm hF he hJ hKJ
  rw [hUEdge] at hmark ⊢
  have hUL : J.pCoreIn 2 ≤ U.H ⊓ L := by
    rintro _ ⟨u,hu,rfl⟩
    have hz : ζ u ∈ heptadKernel := hcore ▸ mem_map_of_mem ζ.toMonoidHom hu
    have hm : ζ u ∈ ((U.H ⊓ L).subgroupOf J).map ζ.toMonoidHom := by
      rw [hmark]
      exact heptadKernelAmbient_le_twoPair ⟨ζ u,hz,rfl⟩
    have hu' : u ∈ (U.H ⊓ L).subgroupOf J :=
      (mem_map_iff_mem (f := ζ.toMonoidHom) ζ.injective).mp hm
    exact hu'
  have hUJ : U.H ⊓ L ≤ J := inf_le_left.trans hUle
  have hnative : fourTwoPairStabilizer ≤ heptadStabilizer :=
    inf_le_left.trans fourPairStabilizer_le_heptad
  have hcard : Nat.card (U.H ⊓ L : Subgroup G) = 48 := by
    have hh := congrArg (fun R : Subgroup heptadStabilizer => Nat.card R) hmark
    rw [card_map_of_injective ζ.injective,
      Nat.card_congr (subgroupOfEquivOfLe hUJ).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hnative).toEquiv] at hh
    exact hh.trans fourTwoPairStabilizer_card
  have hRcard : Nat.card (U.H.subgroupOf L) = 48 := by
    rw [←inf_subgroupOf_right U.H L,
      Nat.card_congr (subgroupOfEquivOfLe (show U.H ⊓ L ≤ L from inf_le_right)).toEquiv,hcard]
  let V := (J.pCoreIn 2).subgroupOf L
  obtain ⟨ha,hVcard,_⟩ := d.linear_overcomponent_action h hH.1.1.2 hp F hm hF he hJ.1 hKJ.le
  rw [hn] at hVcard
  let := ha
  let : IsElementaryAbelian 2 (J.pCoreIn 2) := IsElementaryAbelian.map J.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe (hUL.trans inf_le_right)).toMonoidHom
    (subgroupOfEquivOfLe (hUL.trans inf_le_right)).injective
  have hVc : Nat.card V = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hUL.trans inf_le_right)).toEquiv]
    exact (card_map_of_injective J.subtype_injective).trans hVcard
  have hne : V ≠ pCore 2 L := by
    intro hh
    have heq := congrArg (fun R : Subgroup L => R.map L.subtype) hh
    change ((J.pCoreIn 2).subgroupOf L).map L.subtype = L.pCoreIn 2 at heq
    rw [map_subgroupOf_eq_of_le (hUL.trans inf_le_right)] at heq
    have hJM : J = normalizer (L : Set G) := by rw [←hNU,heq,hNV]
    exact d.right_outside (hJM ▸ hKJ.le)
  have heL : Nonempty (L ≃* Matrix.SL2.Affine F) := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 true e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.pointLocalEquivAffine F)⟩
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 false e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.lineLocalEquivAffine F)⟩
  let := Fintype.ofFinite F
  let f : F ≃+* Representation.SL2FourNatural.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF4,Representation.SL2FourNatural.card_field])
  exact QuasithinM23.rigid_of_affine_four_elementary_overgroup
    (heL.some.trans (QuasithinM23.affineFieldEquiv f)) (U.H.subgroupOf L) V
    hRcard hVc (fun v hv => (hUL hv).1) hne

/-- The original coset system has the pointwise edge-fixer rigidity required
by the uniqueness-system recognition theorem. All heptad markings are retained. -/
theorem Preparation.linear_nonmaximal_rigid_coset_system
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
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) := by
  obtain ⟨J,hJ,hKJ,U,ζ,hx,hv,he0,hUJ,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,horbit,ht⟩ :=
    d.linear_nonmaximal_coset_system h hH hp F hm hF he hnonmax
  refine ⟨J,hJ,hKJ,U,ζ,hx,hv,he0,hUJ,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,horbit,ht,?_⟩
  exact coset_edge_rigid d h hH hp F hm hF he hJ hKJ U ζ he0 hUJ hcore hedgeM

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
