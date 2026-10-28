module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.OddNormalizerReduction
public import Theory.GroupTheory.CentralProductMovedProjection
public import Theory.GroupTheory.PerfectNormalizerInner
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleModels

/-!
# The literal Hall residual projects into the moved ordinary component

The fixed perfect residual F contains the original module V in its two-core
and satisfies V=[V,F]. Since N_G(V)=M, a component outside M cannot centralize
V. Any inner action of F on that component therefore produces an actual
perfect coordinate subgroup with noncentral two-core. All maps remain in the
original odd normalizer. This does not assume that F alone has a unique
maximal two-local overgroup, or that the component is normal.

Source: Aschbacher--Smith 4.4.10--11, printed p.621, used for the nonnormal
A5 pair in 10.2.3. Soluble outer action is explicit in the inner-action lemma;
the concrete model consumers discharge it on their marked components.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original fixed residual is perfect on its literal normalizer carrier. -/
theorem source_oddNormalizer_residual_perfect (B : Subgroup G) :
    Group.IsPerfect (((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G))) := by
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  have hFN : F ≤ normalizer (B : Set G) :=
    ((map_subtype_le _).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  let : Group.IsPerfect F := Group.IsPerfect.map C.subtype
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFN).symm.surjective

/-- Soluble outer action places the unchanged residual in the actual inner product. -/
theorem source_oddNormalizer_component_inner (B : Subgroup G)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    [Group.IsSolvable (MulAut.Outer K)] :
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let : IsQuasisimple K := hK.2
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) B
  exact perfect_le_sup_centralizer_of_solvable_outer K _ hFK

/-- Inner action produces a noncentral two-core in an actual perfect subgroup
of the selected component, without any component normality or module placement. -/
theorem source_oddNormalizer_component_projection
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    ∃ P Q : Subgroup (normalizer (B : Set G)), P ≤ K ∧
      Q ≤ centralizer (K : Set (normalizer (B : Set G))) ∧
      Group.IsPerfect P ∧ Group.IsPerfect Q ∧
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ P ⊔ Q ∧
      P ≤ ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ⊔ Q ∧
      ⁅P.pCoreIn 2,P⁆ ≠ ⊥ := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let U := D.fullModule.subgroupOf N
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,hm,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hUF : U ≤ F.subgroupOf N := subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))
  have hmove : U = ⁅U,F.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVN,map_subgroupOf_eq_of_le hFN]
    exact hm
  have hnc : ¬ U ≤ centralizer (K : Set N) := by
    intro hc
    apply houtK
    rw [←source_fullModule_normalizer D]
    apply (show K.map N.subtype ≤ centralizer (D.fullModule : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    rintro _ ⟨k,hk,rfl⟩ v hv
    exact congrArg Subtype.val (hc (show (⟨v,hVN hv⟩ : N) ∈ U from hv) k hk).symm
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) B
  have hp : IsPGroup 2 U := (isPGroup_pCoreIn 2 F).to_le hVF |>.comap_subtype
  obtain ⟨P,Q,hPK,hQC,hP,hQ,hAP,hPA,hnc,_⟩ :=
    exists_perfect_projection_with_noncentral_core K (centralizer (K : Set N))
      (F.subgroupOf N) U (le_centralizer_iff.mp le_rfl) hinner hUF hp hmove hnc
  exact ⟨P,Q,hPK,hQC,hP,hQ,hAP,hPA,hnc⟩

include D in
/-- The complete Theorem B list applies to the actual detected component. -/
theorem source_oddNormalizer_component_theoremB
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) :
    ChapterA.Section02.IsTheoremBModel (K ⧸ center K) := by
  let : IsQuasisimple K := hK.2
  obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK D.simpleQTKE B hne
  exact ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
    (hqt.subgroup K) (hkg.subgroup K)

end CFSG.Quasithin.Chapter10
