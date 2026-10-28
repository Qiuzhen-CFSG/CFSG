module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.NonnormalProjection
public import Theory.SpecificGroups.PSL2.OddPerfectCore

/-!
# Odd-field PSL₂ components in the original Hall normalizer

The actual fixed residual projects into the selected component with a
noncentral two-core. Every perfect subgroup of odd-field PSL₂ has trivial
two-core, so the literal central-quotient marking makes the projection
impossible. For a nonnormal component the previously proved soluble outer
action supplies the inner-action premise on the original residual.

Source: Aschbacher--Smith 4.4.11, printed p.621. This includes the odd
square-field row and imposes no prime-field or ambient SQTK assumption.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- An odd-field PSL₂ central quotient contradicts the actual perfect
projection with noncentral two-core in the Hall normalizer. -/
theorem source_oddNormalizer_no_odd_psl2_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {F : Type*} [Field F] [Finite F] (ho : Odd (Nat.card F))
    (e : K ⧸ center K ≃* PSL(2,F))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) : False := by
  obtain ⟨P,Q,hPK,_,hP,_,_,_,hnc⟩ :=
    source_oddNormalizer_component_projection D B hBC hodd hBV K houtK hinner
  let : Group.IsPerfect P := hP
  let q : P →* PSL(2,F) :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
  have hcore := Theory.PSL2.odd_perfect_hom_twoCore_le_ker ho q
  apply hnc
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨u,hu,rfl⟩ y hy
  have he : e (QuotientGroup.mk (inclusion hPK u)) = 1 := hcore hu
  have hz : inclusion hPK u ∈ center K :=
    (QuotientGroup.eq_one_iff (inclusion hPK u)).mp
      (e.injective (by simpa only [map_one] using he))
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hPK hy⟩)

/-- The original nonnormal component supplies the inner action, so every
odd-field PSL₂ marking is excluded on the unchanged source data. -/
theorem source_oddNormalizer_no_odd_psl2_nonnormal_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {F : Type*} [Field F] [Finite F] (ho : Odd (Nat.card F))
    (e : K ⧸ center K ≃* PSL(2,F))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) : False := by
  exact source_oddNormalizer_no_odd_psl2_component D B hBC hodd hBV K houtK ho e
    (source_oddNormalizer_nonnormal_component_inner D B hne K hK hnK hFK)

/-- The literal `IsPSL` marking supplies odd cardinality and the central
quotient equivalence; odd square fields require no further premise. -/
theorem source_oddNormalizer_no_odd_psl2_model_nonnormal_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {q : ℕ} (ho : Odd q) (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 2 q)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  exact source_oddNormalizer_no_odd_psl2_nonnormal_component D B hne hBC hodd hBV
    K hK hnK houtK (by simpa only [hF] using ho) e hFK

end CFSG.Quasithin.Chapter10
