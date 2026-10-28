module

public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentProjection
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.LinearTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.KnownCases
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.SpecificGroups.Janko1.PerfectSubgroupCore
public import Theory.SpecificGroups.SL2.PerfectImageCore
public import Theory.SpecificGroups.Suzuki.NormalSubgroups
public import Theory.SpecificGroups.PSL2.PrimePerfectCore
public import Theory.SpecificGroups.PSL2.OuterSolvable.Semilinear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

/-!
# Rank-one marked components in the odd Hall normalizer

The literal fixed residual projects to a perfect subgroup of a moved component
with noncentral two-core.  The four nonnormal component models have central
quotient maps whose defining-characteristic perfect-subgroup two-core is
central, so each marked row is impossible.  This is the component inspection
in Aschbacher--Smith 4.4.11, printed p.621.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter1.Section02 Chapter3.Section02 Chapter4 Chapter4.Section04

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem projected_core_central
    {N : Type*} [Group N] [Finite N]
    (K P : Subgroup N) (hPK : P ≤ K)
    (hcentral : pCore 2 P ≤ (center K).comap (inclusion hPK)) :
    ⁅P.pCoreIn 2, P⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨u, hu, rfl⟩ y hy
  have hz : inclusion hPK u ∈ center K := hcentral hu
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hPK hy⟩)

private theorem no_marked_model_of_core_central
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G))))
    (hcore : ∀ (P : Subgroup (normalizer (B : Set G))), P ≤ K →
      Group.IsPerfect P → ⁅P.pCoreIn 2, P⁆ = ⊥) : False := by
  obtain ⟨P, Q, hPK, hQC, hP, hQ, hPF, hFP, hnc⟩ :=
    source_oddNormalizer_component_projection D B hBC hodd hBV K houtK hinner
  exact hnc (hcore P hPK hP)

/-- A characteristic-two PSL₂ central quotient is excluded from the actual
odd Hall normalizer component inspection. -/
theorem source_oddNormalizer_no_sl2_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Theory.PSL2.Group F)
    (_hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) : False := by
  apply no_marked_model_of_core_central D B hBC hodd hBV K houtK hinner
  intro P hPK hP
  let q : P →* Theory.PSL2.Group F :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
  have hker : q.ker ≤ (center K).comap (inclusion hPK) := by
    intro x hx
    change e (QuotientGroup.mk (inclusion hPK x)) = 1 at hx
    have hz := (QuotientGroup.eq_one_iff (inclusion hPK x)).mp
      (e.injective (by simpa only [map_one] using hx))
    exact hz
  let qsl : P →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm.toMonoidHom.comp q
  have hqsl : pCore 2 P ≤ qsl.ker :=
    Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker qsl
  exact projected_core_central K P hPK (hqsl.trans (by
    intro x hx
    exact hker (by simpa [qsl] using hx)))

private theorem suzuki_perfect_core_le_ker
    {A : Type*} [Group A] [Group.IsPerfect A]
    {m : ℕ} (hm : 0 < m)
    (f : A →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : pCore 2 A ≤ f.ker := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hbot : pCore 2 f.range = ⊥ := by
    by_contra hne
    let : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
      intro he
      have : Subsingleton f.range := by rw [he]; infer_instance
      exact hne (Subsingleton.elim _ _))
    let : Group.IsNilpotent (pCore 2 f.range) := pCore_isNilpotent
    have hs := BenderSuzuki.MatrixGroups.suzukiSubgroup_isSolvable_of_solvable_normal
      hm f.range (pCore 2 f.range) hne
    exact Group.IsPerfect.not_isSolvable f.range hs
  have him : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f.rangeRestrict
      f.rangeRestrict_surjective, pCore_isPGroup.map f.rangeRestrict⟩
  rw [hbot] at him
  have hk := (Subgroup.map_eq_bot_iff _).mp (bot_unique him)
  intro a ha
  exact congrArg Subtype.val (hk ha)


/-- A Suzuki central quotient is excluded from the actual odd Hall normalizer
component inspection. -/
theorem source_oddNormalizer_no_suzuki_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m)
    (e : K ⧸ center K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (_hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) : False := by
  apply no_marked_model_of_core_central D B hBC hodd hBV K houtK hinner
  intro P hPK hP
  let q : P →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
  have hker : q.ker ≤ (center K).comap (inclusion hPK) := by
    intro x hx
    change e (QuotientGroup.mk (inclusion hPK x)) = 1 at hx
    have hz := (QuotientGroup.eq_one_iff (inclusion hPK x)).mp
      (e.injective (by simpa only [map_one] using hx))
    exact hz
  exact projected_core_central K P hPK (by
    exact (suzuki_perfect_core_le_ker hm q).trans hker)

/-- An odd prime-field PSL₂ central quotient is excluded from the actual
odd Hall normalizer component inspection. -/
theorem source_oddNormalizer_no_prime_psl2_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 2 p)
    (_hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  apply no_marked_model_of_core_central D B hBC hodd hBV K houtK hinner
  intro P hPK hP
  let q : P →* Theory.PSL2.Group F :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
  have hker : q.ker ≤ (center K).comap (inclusion hPK) := by
    intro x hx
    change e (QuotientGroup.mk (inclusion hPK x)) = 1 at hx
    have hz := (QuotientGroup.eq_one_iff (inclusion hPK x)).mp
      (e.injective (by simpa only [map_one] using hx))
    exact hz
  exact projected_core_central K P hPK (by
    exact (Theory.PSL2.prime_perfect_hom_twoCore_le_ker ho hF q).trans hker)

/-- The J₁ central quotient is excluded from the actual odd Hall normalizer
component inspection. -/
theorem source_oddNormalizer_no_janko_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (e : K ⧸ center K ≃* Janko1.Model)
    (_hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) : False := by
  apply no_marked_model_of_core_central D B hBC hodd hBV K houtK hinner
  intro P hPK hP
  let q : P →* Janko1.Model :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp (inclusion hPK)
  have hk : q.ker ≤ (center K).comap (inclusion hPK) := by
    intro p hp
    have heq : e (QuotientGroup.mk (inclusion hPK p)) = 1 := hp
    have hz := (QuotientGroup.eq_one_iff (inclusion hPK p)).mp
      (e.injective (by simpa only [map_one] using heq))
    exact hz
  let f : PerfectCentralCovering.Cover P q.range := {
    toMonoidHom := q.rangeRestrict
    surjective := q.rangeRestrict_surjective
    isPerfect := hP
    ker_le_center := by
      intro p hp
      have hz := hk (congrArg Subtype.val hp)
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      simpa using congrArg Subtype.val (mem_center_iff.mp hz (inclusion hPK y))
  }
  let : Group.IsPerfect q.range := Group.IsPerfect.range q
  have hm : (pCore 2 P).map q.rangeRestrict ≤ pCore 2 q.range :=
    le_sSup ⟨(inferInstance : (pCore 2 P).Normal).map q.rangeRestrict
      q.rangeRestrict_surjective, pCore_isPGroup.map q.rangeRestrict⟩
  have hc : pCore 2 P ≤ center P := by
    rw [← f.comap_center]
    exact map_le_iff_le_comap.mp
      (hm.trans (Janko1.perfect_subgroup_pCore_two_le_center q.range))
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨u, hu, rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp (hc hu) ⟨y, hy⟩)

end CFSG.Quasithin.Chapter10
