module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortGeometry
public import Theory.GroupTheory.TwoLocalUniquenessControl
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortGeometry
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortOrbits
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow

/-!
# The actual G₂ common stabilizer and unique fixed coset

For one compatible comparison, the full stabilizer of the marked A- and C-roots
normalizes the A–B plane. This plane is literally the derived subgroup of
O₂(L), is nontrivial, and is normalized by L. Original uniqueness over L
therefore places its full normalizer in N_G(L). This proves the common-stabilizer
bound without identifying the original S with T.

When S=T, the local Sylow orbit argument gives the marked long root's unique
fixed coset in C_G(v)/(N_G(L) intersect C_G(v)). The previously proved perfect
affine action and I.8.5 now yield C_G(v) <= N_G(L), including field four.
The stronger export retains the same involution representatives and their
class catalogue for ambient generation. Both maps, the whole overlap, original
uniqueness and concrete comparison are retained. The all-degree discharge of
S=T and ambient generation are supplied by the LocalSylow and Generation
extensions; exhaustive comparison and concrete completion recognition remain
duties of the generic-global assembly.

Source: Aschbacher–Smith F.4.42, printed p.295, and its use in 5.3.3,
p.659 (`refs/quasithin.pdf`). Internal imports retain the existing private
inverse-Sylow and commuting-pair calculations within this source family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- Retain the actual two-class catalogue alongside the fixed-coset proof,
so the ambient order argument uses exactly the same marked roots.
The common stabilizer lies in N_G(L) before assuming S=T. At S=T,
the marked long root has a unique fixed coset and the full short-root
centralizer lies in N_G(L), through the same compatible comparison. -/
theorem Preparation.g2_short_fixed_coset_classes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      ∃ z v : (L ⊔ residual H : Subgroup G),
        z.val = (e.right.symm (G2CompletionFusion.long (1:F))).val ∧
        v.val = (e.right.symm (G2CompletionFusion.short (1:F))).val ∧
        z.val ∈ (center (residual H)).map (residual H).subtype ∧
        orderOf z=2 ∧ orderOf v=2 ∧ ¬ IsConj z.val v.val ∧
        (∀ x : (L ⊔ residual H : Subgroup G), x.val∈sourceS L H → orderOf x=2 →
          IsConj z x ∨ IsConj v x) ∧
      let l := (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom
      centralizer ({l G2ShortAction.short} : Set G) ⊓
        centralizer ({l G2ShortAction.long} : Set G) ≤ normalizer (L : Set G) ∧
      (sourceS L H=(T : Subgroup G) →
        (∃! q : centralizer ({l G2ShortAction.short} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({l G2ShortAction.short} : Set G)),
          G2ShortAction.longMark l • q=q) ∧
        centralizer ({l G2ShortAction.short} : Set G) ≤ normalizer (L : Set G)) := by
  obtain ⟨e,z,v,hz,hv,hzK,hz2,hv2,hn,hclasses⟩ := d.g2_completion_involution_classes h hH hp F he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic₂ (F := F) →* G := Q.subtype.comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  have ha (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂) :
      f ⟨x,hx⟩=l ⟨x,hy⟩ := by
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨x,hx,hy⟩
    exact (congrArg Subtype.val (e.symm.right_commutes b)).trans
      (congrArg Subtype.val (e.symm.left_commutes b)).symm
  have hz' : l G2ShortAction.long=f (G2CompletionFusion.long 1) := (ha _ _ _).symm
  have hv' : l G2ShortAction.short=f (G2CompletionFusion.short 1) := (ha _ _ _).symm
  have hn' : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1)) := by
    change ¬ IsConj (e.right.symm (G2CompletionFusion.long (1:F))).val
      (e.right.symm (G2CompletionFusion.short (1:F))).val
    rwa [←hz,←hv]
  have hzC : centralizer ({f (G2CompletionFusion.long 1)} : Set G) ≤
      normalizer (residual H : Set G) := by
    have hc := d.g2_central_involution_centralizers h hH hp F he 1 z.val hzK
      ((Subgroup.orderOf_coe z).trans hz2)
    change centralizer ({(e.right.symm (G2CompletionFusion.long (1:F))).val} : Set G) ≤ _
    rw [←hz]
    exact hc
  have hq : 2 < Nat.card F := by
    rw [(d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  let J := (local₁ (F := F)).subgroupOf parabolic₁
  have hJ : J=solvableResidual (parabolic₁ (F := F)) := by
    apply map_injective (parabolic₁ (F := F)).subtype_injective
    rw [map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),
      HigherFieldResiduals.parabolic₁_residual hq]
  have hJf : J.map f=residual H := by
    rw [hJ,show f=P.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hH.1.1.2 hp 1
  have hQ : ((radical₁ (F := F)).subgroupOf parabolic₁).map f=(residual H).pCoreIn 2 := by
    have hh := map_pCoreIn_of_injective 2 J f hf
    rw [hJf,pCoreIn_subgroupOf 2 local₁ parabolic₁ (le_sup_left.trans_eq local₁_sup_borel),
      local₁_pCoreIn] at hh
    exact hh
  have hC : centralizer ({f (G2CompletionFusion.long 1)} : Set G) ≤
      normalizer (((radical₁ (F := F)).subgroupOf parabolic₁).map f : Set G) := by
    rw [hQ]
    exact hzC.trans (normalizer_le_normalizer_characteristic_image (residual H)
      (pCore 2 (residual H)))
  have hsep := G2ShortOrbits.compatible_orbits_distinct f hf l ha hC
  have hS : (unipotent.subgroupOf parabolic₁).map f=sourceS L H :=
    source_g2_inverse_sylow_image d h hH.1.1.2 e
  have hKC : residual H ⊓ centralizer ({l G2ShortAction.short} : Set G)=
      (unipotent.subgroupOf parabolic₁).map f ⊓ centralizer ({l G2ShortAction.short} : Set G) := by
    rw [hS,hv']
    exact d.g2_short_factor_centralizer h hH.1.1.2 hp F e
  have hcommon := G2ShortGeometry.common_stabilizer_le_plane_normalizer f hf l ha hn' hsep
    (residual H) (hz'.symm ▸ hzC) hKC
  have hplane : G2ShortAction.plane l=⁅L.pCoreIn 2,L.pCoreIn 2⁆ :=
    (d.g2_short_centralizer_of_long_unique_fixed h hH.1.1.2 hp F e).2.2.1
  have hVS : G2ShortAction.plane l ≤ sourceS L H :=
    (G2ShortGeometry.plane_le_sylow_image f l ha).trans_eq hS
  have hVN : normalizer (G2ShortAction.plane l : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal d.unique_left
      ((pCore_isPGroup.map _).to_le hVS)
    · intro hbot
      have hm : l G2ShortAction.long ∈ G2ShortAction.plane l :=
        mem_map_of_mem l (rootA_mem_longRootLocal 1)
      have hh : z.val=1 := hz.trans (hz'.symm.trans (by simpa [hbot] using hm))
      have ho := (Subgroup.orderOf_coe z).trans hz2
      simp [hh] at ho
    · rw [hplane,←map_subtype_commutator]
      exact (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))).trans
        (normalizer_le_normalizer_characteristic_image (L.pCoreIn 2) (commutator (L.pCoreIn 2)))
  have hbound := hcommon.trans hVN
  have hQN : Q ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show L ≤ Q from le_sup_left.trans le_sup_left)).mp
      ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 0)
  have hN : l.range ≤ normalizer (L : Set G) := by
    rintro _ ⟨x,rfl⟩
    exact hQN (e.left.symm x).property
  refine ⟨e,z,v,hz,hv,hzK,hz2,hv2,hn,hclasses,hbound,?_⟩
  intro hST
  have hfix := G2ShortGeometry.long_unique_fixed f hf l ha hn' hsep
    (normalizer (L : Set G)) hN hbound T (hS.trans hST)
  exact ⟨hfix,(d.g2_short_centralizer_of_long_unique_fixed h hH.1.1.2 hp F e).2.2.2 hfix⟩

/-- The common stabilizer lies in N_G(L) before assuming S=T. At S=T,
the marked long root has a unique fixed coset and the full short-root
centralizer lies in N_G(L), through the same compatible comparison. -/
theorem Preparation.g2_short_fixed_coset_geometry
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      let l := (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom
      centralizer ({l G2ShortAction.short} : Set G) ⊓
        centralizer ({l G2ShortAction.long} : Set G) ≤ normalizer (L : Set G) ∧
      (sourceS L H=(T : Subgroup G) →
        (∃! q : centralizer ({l G2ShortAction.short} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({l G2ShortAction.short} : Set G)),
          G2ShortAction.longMark l • q=q) ∧
        centralizer ({l G2ShortAction.short} : Set G) ≤ normalizer (L : Set G)) := by
  obtain ⟨e,_,_,_,_,_,_,_,_,_,hbound,hfixed⟩ :=
    d.g2_short_fixed_coset_classes h hH hp F he
  exact ⟨e,hbound,hfixed⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
