module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Dimension.CubicPlanes
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.SeedGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.CubicSpan

/-!
# Excluding fixed-point-free three-cycles on the original local quotient

The two explicit cubics lift through the original two-core quotient. Both
source cubic orbits lie in the image of the original seed plane, while the
original flag line contains a nonzero Sylow-fixed vector. The incompatible
cubic-plane calculation therefore excludes every target action in which
three-cycles have no nonzero fixed vector. In particular this excludes the
eight-dimensional four-plus-dual alternative once its marking is supplied.

Source: Aschbacher–Smith 14.7.2(2) and 14.7.50, pp.1043 and 1064.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open BinaryPermutation.SevenSourceCubics
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
universe u v w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem local_threeCycle_fixedPointFree_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* Equiv.Perm (Fin 7)) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hT : ((T : Subgroup G).subgroupOf I).map π = standardTwo)
    {W : Type v} {X : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    {ρ : Representation (ZMod 2) I W}
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 7)) X)
    (hfree : ∀ g : Equiv.Perm (Fin 7), g.IsThreeCycle →
      ∀ x : X, σ g x = x → x = 0)
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap (σ.comp π)) (hp : p.toLinearMap.ker ≠ ⊤) : False := by
  let S := (c.imageSpace V).map p.toLinearMap
  let E := (c.imageSpace (F.Vi 2)).map p.toLinearMap
  have hS : Module.finrank (ZMod 2) S = 2 := local_quotient_seed_finrank h hI c p hp
  have hE : Module.finrank (ZMod 2) E = 1 := local_quotient_plane_finrank h hI c p hp
  obtain ⟨s, hs⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < Module.finrank (ZMod 2) E by omega)
  have hs0 : (s : X) ≠ 0 := fun he => hs (Subtype.ext he)
  have hsS : (s : X) ∈ S :=
    (Submodule.map_mono (c.imageSpace_mono (F.le_seed 2))) s.property
  have hfix : ∀ t ∈ standardTwo, σ t (s : X) = s := by
    intro t ht
    obtain ⟨a,ha,rfl⟩ := hT.symm ▸ ht
    exact local_quotient_plane_sylow_fixed c p a ha s s.property
  obtain ⟨w,hw,hwS⟩ := s.property
  obtain ⟨z,hz,hzW⟩ := (c.mem_imageSpace_iff (F.Vi 2) w).mp hw
  have hzs : p (c.coordinates z).toAdd = (s : X) := hzW ▸ hwS
  have orbit_in_seed (r : Equiv.Perm (Fin 7)) (hr : Nat.card (zpowers r) = 3)
      (he : Nonempty (((zpowers r ⊔ standardTwo : Subgroup (Equiv.Perm (Fin 7))) ⧸
        pCore 2 (zpowers r ⊔ standardTwo : Subgroup (Equiv.Perm (Fin 7)))) ≃*
          Equiv.Perm (Fin 3))) : σ r (s : X) ∈ S := by
    obtain ⟨A,hAp,hAB,hq⟩ := cubic_lift_with_sylow_join I hI π hπ hk (zpowers r) hr
      (by rw [hT]; exact he)
    let Y := A.map I.subtype
    have hYp : IsPPerfect 2 Y := hAp.of_surjective
      (I.subtype.subgroupMap A) (I.subtype.subgroupMap_surjective A)
    have horbit : conjugateSpanBy (F.Vi 2) Y ≤ V :=
      cubic_plane_span_le_seed_at h hab structural previous faithful Y
        ((map_subtype_le A).trans hI.2.1) hYp hq
    obtain ⟨g,hg,hgπ⟩ := (show r ∈ A.map π from hAB.symm ▸ mem_zpowers r)
    let gz : F.UH I := ⟨g.val*z.val*g.val⁻¹,
      (mem_normalizer_iff.mp (c.normalized g.property) z.val).mp z.property⟩
    have hgz : (gz : G) ∈ V := horbit (subset_closure
      ⟨g.val,mem_map_of_mem I.subtype hg,z.val,hz,rfl⟩)
    have hm : p (c.coordinates gz).toAdd ∈ S :=
      ⟨_,(c.mem_imageSpace_iff V _).mpr ⟨gz,hgz,rfl⟩,rfl⟩
    have heq : p (c.coordinates gz).toAdd = σ r (s : X) := by
      rw [show (c.coordinates gz).toAdd = ρ g (c.coordinates z).toAdd
        from c.equivariant g z,p.isIntertwining]
      change σ (π g) (p (c.coordinates z).toAdd) = _
      rw [hgπ,hzs]
    rwa [heq] at hm
  exact Dimension.no_common_seed_plane σ hfree s hs0 hfix S hS hsS
    (orbit_in_seed first first_card first_join_quotient)
    (orbit_in_seed second second_card second_join_quotient)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
