module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedEndpoint
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedPair

/-!
# The original fixed dihedral pair and its faithful normalizer quotient

The compatible binary fixed amalgam transports both actual residual cores
through the whole common middle. Their D8 join and failure to lie in the
opposite endpoint core force both cores to avoid a two-subgroup normalized
by the fixed endpoints. This uses the already established minimality of
each residual four-group, with normality taken inside its own A4.

Every nontrivial normal subgroup of D8 contains its central half-turn.
Consequently the entire join avoids the two-core of the conjugate full
root normalizer containing the original outer-involution centralizer.
Restriction of the literal quotient map therefore gives an injection of
this same D8, retaining the root witness, conjugator and both endpoint marks.

Source: Aschbacher--Smith F.4.37, printed p.293 of refs/quasithin.pdf,
in the prepared symplectic pair of 5.3.1--3, pp.658--659. The next step must
place this image in the marked PSL2(4) section, handling the field and odd
scalar factors. No q=4 contradiction, unconditional S=T, or ambient order
bound is asserted here. The whole residual and both orientations remain.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
private theorem dihedral_join_disjoint {G : Type*} [Group G] (U V Q : Subgroup G)
    (e : (U⊔V : Subgroup G)≃*DihedralGroup 4)
    (hU : U≠⊥) (hnU : U⊔V≤normalizer (U : Set G))
    (hnQ : U⊔V≤normalizer (Q : Set G)) (hd : Disjoint U Q) :
    Disjoint (U⊔V) Q := by
  let J := U⊔V
  have hUn : (U.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hnU
  have hQn : (Q.subgroupOf J).Normal := ⟨fun x hx g => by
    change g.val*x.val*g.val⁻¹∈Q
    exact (hnQ g.property x.val).mp hx⟩
  have hU0 : U.subgroupOf J≠⊥ := by
    intro hh
    have hh' := congrArg (fun A : Subgroup J => A.map J.subtype) hh
    rw [map_subgroupOf_eq_of_le (show U≤J from le_sup_left),Subgroup.map_bot] at hh'
    exact hU hh'
  have hd' : Disjoint (U.subgroupOf J) (Q.subgroupOf J) := by
    apply disjoint_def.mpr
    intro x hx hy
    exact Subtype.ext (disjoint_def.mp hd hx hy)
  have hbot := SourceFusionOrder.dihedral_normal_disjoint_eq_bot e
    (U.subgroupOf J) (Q.subgroupOf J) hUn hQn hU0 hd'
  apply disjoint_def.mpr
  intro x hx hy
  have hh : (⟨x,hx⟩ : J)∈Q.subgroupOf J := hy
  rw [hbot,mem_bot] at hh
  exact congrArg Subtype.val hh


/-- The actual fixed residual four-groups generate D8 through the one common
middle, and each avoids containment in the opposite full endpoint core. -/
theorem Preparation.symplectic_outer_fixed_residual_pair
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) :
    let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
    let D : Fin 2 → Subgroup G := fun i => P i ⊓ centralizer ({f.val} : Set G)
    let U : Fin 2 → Subgroup G := fun i => ((pResidual 2 (D i)).map (D i).subtype).pCoreIn 2
    U 0≤D 0⊓D 1 ∧ U 1≤D 0⊓D 1 ∧
      Nonempty (↥(U 0⊔U 1)≃*DihedralGroup 4) ∧ U 0⊓U 1≠⊥ ∧
      ¬ U 0≤(D 1).pCoreIn 2 ∧ ¬ U 1≤(D 0).pCoreIn 2 := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := centralizer ({f.val} : Set G)
  have hC : ((P 0⊓P 1)⊓C)≤(P 0⊓C)⊓(P 1⊓C) := by
    intro x hx
    exact ⟨⟨hx.1.1,hx.2⟩,⟨hx.1.2,hx.2⟩⟩
  have hBP : ((P 0⊓P 1)⊓C)≤P 0⊓C := inf_le_inf inf_le_left le_rfl
  have hBQ : ((P 0⊓P 1)⊓C)≤P 1⊓C := inf_le_inf inf_le_right le_rfl
  rcases d.symplectic_outer_fixed_binary_amalgam h hH hp F hm hF he f hf ho with hs | hs
  · obtain ⟨e⟩ := hs
    obtain ⟨hU,hV,hj,hi⟩ := SourceFusionOrder.binary_amalgam_residual_core_pair (hBP := hBP) (hBQ := hBQ) e
    exact ⟨hU.trans hC,hV.trans hC,hj,hi,
      SourceFusionOrder.binary_amalgam_residual_core_noncontainment (hBP := hBP) (hBQ := hBQ) e⟩
  · obtain ⟨e⟩ := hs
    obtain ⟨hV,hU,hj,hi⟩ := SourceFusionOrder.binary_amalgam_residual_core_pair (hBP := hBQ) (hBQ := hBP) e.reverse
    obtain ⟨hnV,hnU⟩ := SourceFusionOrder.binary_amalgam_residual_core_noncontainment (hBP := hBQ) (hBQ := hBP) e.reverse
    exact ⟨hU.trans hC,hV.trans hC,by rw [sup_comm]; exact hj,
      by rw [inf_comm]; exact hi,hnU,hnV⟩

/-- Both original residual cores avoid any two-subgroup normalized by the
two fixed endpoints. This is applied below to the conjugate normalizer core. -/
theorem Preparation.symplectic_outer_fixed_cores_disjoint
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hnQ : ∀ i : Fin 2,
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
        centralizer ({f.val} : Set G) ≤ normalizer (Q : Set G)) :
    ∀ i : Fin 2,
      Disjoint (((pResidual 2 (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
        centralizer ({f.val} : Set G) : Subgroup G)).map
        (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
          centralizer ({f.val} : Set G)).subtype).pCoreIn 2) Q := by
  obtain ⟨hU,hV,_,_,hnU,hnV⟩ :=
    d.symplectic_outer_fixed_residual_pair h hH hp F hm hF he f hf ho
  intro i
  fin_cases i
  · exact SourceFusionOrder.residual_core_disjoint_of_minimal _ _ Q hQ (hnQ 0) (hnQ 1)
      (d.symplectic_outer_fixed_endpoint_core h hH hp F hm hF he f hf ho 0).2
      (hU.trans inf_le_right) hnU
  · exact SourceFusionOrder.residual_core_disjoint_of_minimal _ _ Q hQ (hnQ 1) (hnQ 0)
      (d.symplectic_outer_fixed_endpoint_core h hH hp F hm hF he f hf ho 1).2
      (hV.trans inf_le_left) hnV

/-- The same original fixed D8 embeds through the literal quotient of a
conjugate full root normalizer by its two-core. All kernels and endpoint
placements are proved here; restricting its image to the PSL2 section remains. -/
theorem Preparation.symplectic_outer_fixed_dihedral_normalizer_quotient
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) :
    ∃ i : Fin 2, ∃ z : G, orderOf z=2 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      ∃ g : G, g*z*g⁻¹=f.val ∧
      let M := (normalizer (![L,residual H] i : Set G)).map (MulAut.conj g).toMonoidHom
      let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
      let D : Fin 2 → Subgroup G := fun j => P j ⊓ centralizer ({f.val} : Set G)
      let U : Fin 2 → Subgroup G := fun j => ((pResidual 2 (D j)).map (D j).subtype).pCoreIn 2
      let J := U 0⊔U 1
      centralizer ({f.val} : Set G)≤M ∧
        ∃ hJM : J≤M, Nonempty (J≃*DihedralGroup 4) ∧ Disjoint J (M.pCoreIn 2) ∧
          Function.Injective ((QuotientGroup.mk' (pCore 2 M)).comp (inclusion hJM)) := by
  obtain ⟨i,z,hz,hzR,g,hg,hC⟩ :=
    d.symplectic_outer_centralizer_le_conjugate_normalizer h hH hp F hm hF he f hf ho
  let M := (normalizer (![L,residual H] i : Set G)).map (MulAut.conj g).toMonoidHom
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let D : Fin 2 → Subgroup G := fun j => P j ⊓ centralizer ({f.val} : Set G)
  let U : Fin 2 → Subgroup G := fun j => ((pResidual 2 (D j)).map (D j).subtype).pCoreIn 2
  let J := U 0⊔U 1
  have hDM (j : Fin 2) : D j≤M := inf_le_right.trans hC
  obtain ⟨hU,hV,⟨e⟩,hi,_,_⟩ :=
    d.symplectic_outer_fixed_residual_pair h hH hp F hm hF he f hf ho
  have hJD : J≤D 0 := sup_le (hU.trans inf_le_left) (hV.trans inf_le_left)
  have hJM : J≤M := hJD.trans (hDM 0)
  have hMQ : M≤normalizer (M.pCoreIn 2 : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hdis := d.symplectic_outer_fixed_cores_disjoint h hH hp F hm hF he f hf ho
    (M.pCoreIn 2) (isPGroup_pCoreIn 2 M) (fun j => (hDM j).trans hMQ) 0
  have hU0 : U 0≠⊥ := by
    intro hh
    exact hi (by change U 0⊓U 1=⊥; rw [hh,bot_inf_eq])
  have hDU : D 0≤normalizer (U 0 : Set G) :=
    (le_normalizer_embedded_pResidual 2 (D 0)).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 ((pResidual 2 (D 0)).map (D 0).subtype)))
  have hJQ : Disjoint J (M.pCoreIn 2) :=
    dihedral_join_disjoint (U 0) (U 1) (M.pCoreIn 2) e hU0
      (hJD.trans hDU) (hJM.trans hMQ) hdis
  refine ⟨i,z,hz,hzR,g,hg,hC,hJM,⟨e⟩,hJQ,?_⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxQ : x.val∈M.pCoreIn 2 := by
    refine ⟨inclusion hJM x,?_,rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hx
  exact mem_bot.mpr (Subtype.ext (disjoint_def.mp hJQ x.property hxQ))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
