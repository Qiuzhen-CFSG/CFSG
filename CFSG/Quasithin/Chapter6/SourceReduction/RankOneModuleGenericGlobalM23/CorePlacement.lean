module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.VertexCoordinates
public import Theory.GroupTheory.Recognition.QuasithinM23.ElementaryPlacement
public import Theory.Mathieu.M23.QuasithinGeometry.SourceRecognition.CorePlacement

/-!
# Placing the full original exceptional core in the vertex coordinates

Pull the native heptad kernel back through the existing vertex equivalence.
It is an elementary subgroup of order sixteen inside the original L, different
from O₂(L). Sylow conjugacy inside L and the two-plane calculation therefore
carry it to O₂(J). Precomposing the same vertex map by this conjugation preserves
the original edge fixer and the entire linear subgroup. Relative normalizers
then give the image of the original H, using (L join H) intersect J = H.

The coset system, heptad marking and every original embedding are retained.
The full sixteen-core is mapped onto the native kernel; pointwise agreement
with the fixed heptad marking and the image of Ix remain further obligations.
Source: Aschbacher--Smith 5.2.20(5), printed pp.656--657.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G]

private theorem core_placement
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
    (β : (L ⊔ H : Subgroup G) ≃* pairStabilizer)
    (hβedge : ∀ a : (L ⊔ H : Subgroup G), (a : G) ∈ L ↔
      (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) :
    ∃ l : L,
      ((J.pCoreIn 2).subgroupOf (L ⊔ H)).map
        (((MulAut.conj (⟨l,mem_sup_left l.property⟩ : (L ⊔ H : Subgroup G))⁻¹).trans β).toMonoidHom) =
          heptadKernelAmbient.subgroupOf pairStabilizer := by
  let X := L ⊔ H
  let U₀ := heptadKernelAmbient.subgroupOf pairStabilizer
  have hUE : heptadKernelAmbient ≤ standardSystem.edgeGroup := by
    intro g hg
    have hh := heptadKernelAmbient_le_twoPair hg
    rw [standardSystem_edgeGroup]
    exact ⟨hh.1.2,hh.2⟩
  have hUP : heptadKernelAmbient ≤ pairStabilizer := by
    intro g hg
    have hh := hUE hg
    rw [standardSystem_edgeGroup] at hh
    exact hh.1
  let QX := U₀.map β.symm.toMonoidHom
  let Q := QX.map X.subtype
  have hQL : Q ≤ L := by
    rintro _ ⟨a,⟨u,hu,rfl⟩,rfl⟩
    exact (hβedge (β.symm u)).mpr (by rw [β.apply_symm_apply]; exact hUE hu)
  let : IsElementaryAbelian 2 heptadKernelAmbient := heptadKernelAmbient_elementary
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUP).toMonoidHom (subgroupOfEquivOfLe hUP).injective
  let : IsElementaryAbelian 2 QX := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map _
  have hQcard : Nat.card Q = 16 := by
    rw [card_map_of_injective X.subtype_injective,
      card_map_of_injective β.symm.injective,
      Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv]
    exact (card_map_of_injective heptadStabilizer.subtype_injective).trans heptadKernel_card
  have hQne : Q ≠ L.pCoreIn 2 := by
    intro heq
    apply heptadKernelAmbient_not_normalized_by_edge
    apply le_normalizer_iff.mpr
    intro a ha u hu
    have haP : a ∈ pairStabilizer := by
      rw [standardSystem_edgeGroup] at ha
      exact ha.1
    let aX := β.symm ⟨a,haP⟩
    let uX := β.symm ⟨u,hUP hu⟩
    have haL : (aX : G) ∈ L := (hβedge aX).mpr (by
      change (β (β.symm ⟨a,haP⟩) : Sporadic.Mathieu.M23) ∈ _
      rw [β.apply_symm_apply]; exact ha)
    have huQ : (uX : G) ∈ Q := ⟨uX,⟨⟨u,hUP hu⟩,hu,rfl⟩,rfl⟩
    have hn : L ≤ normalizer (Q : Set G) := by
      rw [heq]
      exact L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
    have hcQ : ((aX * uX * aX⁻¹ : X) : G) ∈ Q :=
      (mem_normalizer_iff.mp (hn haL) _).mp huQ
    obtain ⟨b,hb,hbval⟩ := hcQ
    have hbX : b = aX * uX * aX⁻¹ := Subtype.ext hbval
    rw [hbX] at hb
    have hm : β (aX * uX * aX⁻¹) ∈ U₀ := by
      obtain ⟨v,hv,hvEq⟩ := hb
      rw [←hvEq]
      change β (β.symm v) ∈ U₀
      rw [β.apply_symm_apply]
      exact hv
    change (β (aX * uX * aX⁻¹) : Sporadic.Mathieu.M23) ∈ heptadKernelAmbient at hm
    simpa only [map_mul,map_inv,aX,uX,β.apply_symm_apply,Subgroup.coe_mul,
      Subgroup.coe_inv] using hm
  obtain ⟨_,_,_,hall,_,_⟩ := d.linear_exceptional_sylow_planes h hH hp F hm hF he hJ hKJ
  have hs := d.sylow 0
  change ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = sourceS L H ⊓ L at hs
  obtain ⟨P,hP⟩ := hs
  have hSL : sourceS L H ≤ L := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 0
  rw [inf_eq_left.mpr hSL] at hP
  obtain ⟨l,hl⟩ := QuasithinM23.conjugate_elementary_of_two_planes L (sourceS L H)
    (L.pCoreIn 2) (J.pCoreIn 2) Q P hP
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    hall hQL hQcard hQne
  refine ⟨l,?_⟩
  let lx : X := ⟨l,mem_sup_left l.property⟩
  have hQX : Q.subgroupOf X = QX := comap_map_eq_self_of_injective X.subtype_injective QX
  have hconj : (Q.subgroupOf X).map (MulAut.conj lx).toMonoidHom =
      (J.pCoreIn 2).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_map]
    have hc : X.subtype.comp (MulAut.conj lx).toMonoidHom =
        (MulAut.conj (l : G)).toMonoidHom.comp X.subtype := by ext g; rfl
    rw [hc,←map_map,map_subgroupOf_eq_of_le (hQL.trans le_sup_left),hl,
      map_subgroupOf_eq_of_le]
    exact ((show J.pCoreIn 2 ≤ L.pCoreIn 2 ⊔ J.pCoreIn 2 from le_sup_right).trans_eq
      (d.linear_exceptional_sylow_planes h hH hp F hm hF he hJ hKJ).1).trans
      (hSL.trans le_sup_left)
  have hcInv : ((J.pCoreIn 2).subgroupOf X).map (MulAut.conj lx⁻¹).toMonoidHom = QX := by
    rw [←hconj,map_map]
    have hc : (MulAut.conj lx⁻¹).toMonoidHom.comp (MulAut.conj lx).toMonoidHom = MonoidHom.id X := by
      apply MonoidHom.ext
      intro g
      change lx⁻¹ * (lx*g*lx⁻¹) * (lx⁻¹)⁻¹ = g
      group
    rw [hc,map_id,hQX]
  change ((J.pCoreIn 2).subgroupOf X).map
    (β.toMonoidHom.comp (MulAut.conj lx⁻¹).toMonoidHom) = _
  rw [←map_map,hcInv]
  change (U₀.map β.symm.toMonoidHom).map β.toMonoidHom = U₀
  rw [map_map]
  have hi : β.toMonoidHom.comp β.symm.toMonoidHom = MonoidHom.id pairStabilizer := by
    apply MonoidHom.ext
    intro g
    exact β.apply_symm_apply g
  rw [hi,map_id]


omit [Finite G] in
private theorem mapped_core_normalizer
    (X J H : Subgroup G) (hUX : J.pCoreIn 2 ≤ X)
    (hNJ : normalizer (J.pCoreIn 2 : Set G) = J)
    (hXJ : X ⊓ J = H) (β : X ≃* pairStabilizer)
    (hcore : ((J.pCoreIn 2).subgroupOf X).map β.toMonoidHom =
      heptadKernelAmbient.subgroupOf pairStabilizer) :
    (H.subgroupOf X).map β.toMonoidHom = heptadStabilizer.subgroupOf pairStabilizer := by
  have hHP : heptadKernelAmbient ≤ pairStabilizer :=
    heptadKernelAmbient_le_twoPair.trans (inf_le_left.trans inf_le_right)
  have hHJ : H.subgroupOf X = J.subgroupOf X := by
    ext g
    change (g : G) ∈ H ↔ (g : G) ∈ J
    rw [←hXJ]
    exact and_iff_right g.property
  rw [hHJ,←hNJ,subgroupOf_normalizer_eq hUX,map_equiv_normalizer_eq,hcore,
    ←subgroupOf_normalizer_eq hHP,heptadKernelAmbient_normalizer]


/-- The original coset vertex map preserves L, the whole linear subgroup,
O₂(J) as a subgroup, and its relative normalizer H, with the same heptad marking. -/
theorem Preparation.linear_nonmaximal_coset_core_placement
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
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer) (_hUJ : U.H ≤ J)
        (β : U.vertexGroup ≃* pairStabilizer),
      U.x = ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ∧
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧
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
      (∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
        (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) ∧
      ((L ⊔ residual H).subgroupOf U.vertexGroup).map β.toMonoidHom =
        pointwisePairStabilizer ∧
      ((J.pCoreIn 2).subgroupOf U.vertexGroup).map β.toMonoidHom =
        heptadKernelAmbient.subgroupOf pairStabilizer ∧
      (H.subgroupOf U.vertexGroup).map β.toMonoidHom =
        heptadStabilizer.subgroupOf pairStabilizer := by
  obtain ⟨J,hJ,hKJ,U,ζ,hx,hv,he0,hUJ,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid⟩ :=
    d.linear_nonmaximal_rigid_coset_system h hH hp F hm hF he hnonmax
  have hcoreEdge : J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup := by
    rintro _ ⟨u,hu,rfl⟩
    have hz : ζ u ∈ heptadKernel := hcore ▸ mem_map_of_mem ζ.toMonoidHom hu
    have hm : ζ u ∈ ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom := by
      rw [hedgeM]
      exact heptadKernelAmbient_le_twoPair ⟨ζ u,hz,rfl⟩
    exact (mem_map_iff_mem (f := ζ.toMonoidHom) ζ.injective).mp hm
  obtain ⟨_,_,β₀,_,_,hβedge,hβlinear,_⟩ :=
    d.linear_nonmaximal_edge_marked_vertex h hH hp F hm hF he hnonmax
  have hβedgeIff (a : (L ⊔ H : Subgroup G)) : (a : G) ∈ L ↔
      (β₀ a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup := by
    have hh := mem_map_iff_mem (f := β₀.toMonoidHom) β₀.injective
      (K := L.subgroupOf (L ⊔ H)) (x := a)
    rw [hβedge] at hh
    exact hh.symm
  obtain ⟨l,hl⟩ := core_placement d h hH hp F hm hF he hJ hKJ β₀ hβedgeIff
  let lx : (L ⊔ H : Subgroup G) := ⟨l,mem_sup_left l.property⟩
  let a := MulAut.conj lx⁻¹
  let β₁ := a.trans β₀
  have hβ₁core : ((J.pCoreIn 2).subgroupOf (L ⊔ H)).map β₁.toMonoidHom =
      heptadKernelAmbient.subgroupOf pairStabilizer := hl
  have hβ₁edge (g : (L ⊔ H : Subgroup G)) : (g : G) ∈ L ↔
      (β₁ g : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup := by
    have hh := hβedgeIff (a g)
    change (lx.val⁻¹ * g.val * (lx.val⁻¹)⁻¹ ∈ L) ↔ _ at hh
    exact (mem_normalizer_iff.mp (L.le_normalizer (L.inv_mem l.property)) g.val).trans hh
  have hβ₁linear : ((L ⊔ residual H).subgroupOf (L ⊔ H)).map β₁.toMonoidHom =
      pointwisePairStabilizer := by
    change ((L ⊔ residual H).subgroupOf (L ⊔ H)).map
      (β₀.toMonoidHom.comp a.toMonoidHom) = _
    rw [←map_map]
    have hm : ((L ⊔ residual H).subgroupOf (L ⊔ H)).map a.toMonoidHom =
        (L ⊔ residual H).subgroupOf (L ⊔ H) :=
      mem_normalizer_iff_map_conj_eq.mp
        (((L ⊔ residual H).subgroupOf (L ⊔ H)).le_normalizer
          (show lx⁻¹ ∈ (L ⊔ residual H).subgroupOf (L ⊔ H) from
            mem_sup_left (L.inv_mem l.property)))
    rw [hm,hβlinear]
  have hUL : J.pCoreIn 2 ≤ L := by simpa only [he0] using hcoreEdge.trans inf_le_right
  have hβ₁H := mapped_core_normalizer (L ⊔ H) J H (hUL.trans le_sup_left)
    (d.linear_exceptional_local h hH hp F hm hF he hJ hKJ).2.2.2.2.1
    (d.linear_exceptional_pair_intersection h hH hp F hm hF he hJ hKJ) β₁ hβ₁core
  let c := MulEquiv.subgroupCongr hv
  let β := c.trans β₁
  have hmap (R : Subgroup G) : (R.subgroupOf U.vertexGroup).map β.toMonoidHom =
      (R.subgroupOf (L ⊔ H)).map β₁.toMonoidHom := by
    change (R.subgroupOf U.vertexGroup).map (β₁.toMonoidHom.comp c.toMonoidHom) = _
    rw [←map_map]
    congr 1
    ext g
    rw [mem_map_equiv]
    rfl
  refine ⟨J,hJ,hKJ,U,ζ,hUJ,β,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,?_,?_,?_,?_⟩
  · intro g
    rw [he0]
    exact hβ₁edge (c g)
  · rw [hmap,hβ₁linear]
  · rw [hmap,hβ₁core]
  · rw [hmap,hβ₁H]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
