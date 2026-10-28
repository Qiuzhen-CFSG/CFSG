module
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.Centered
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.UnitaryComponents

/-!
# The original escaping nonnormal component is centerless

The source covering uniqueness supplies the trivial two-core of the literal
odd normalizer. Its quasithin and K-group hypotheses classify a nontrivial
component center by an actual binary unitary quotient. The proved unitary
perfect-core exclusion then contradicts the original residual projection.
The surviving centerless component has the additive local-plus-ordinary
rank budget needed for its remaining simple-model inspection.

Source: Aschbacher–Smith4.4.9–11, p.621, using A.3.8(1–2), pp.45–46.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original escaping nonnormal component is centerless. -/
theorem source_a5_oddNormalizer_nonnormal_component_center_eq_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    center K = ⊥ := by
  obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK D.simpleQTKE B hne
  have hout : ¬ normalizer (B : Set G) ≤ D.maximalLocal :=
    fun hh => houtK ((map_subtype_le K).trans hh)
  have hcore := source_a5_oddPrimeNormalizer_twoCore_eq_bot D e hn hp B hB hBC hBV hperm hout
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,hnn⟩ := hB.exists_card_eq
    rw [hnn]
    exact hp.pow
  by_contra hz
  obtain ⟨n,hnn,_,hm⟩ := ChapterA.QTComponents.nonnormal_centered_projectiveUnitary
    hqt hkg hcore K hK hnK hz
  exact source_oddNormalizer_no_binary_unitary_nonnormal_component D B hne
    hBC hodd hBV K hK hnK houtK (by omega) hm hFK

/-- The remaining centerless component satisfies the exact local plus ordinary
rank budget needed by the simple-model inspection. -/
theorem source_a5_oddNormalizer_nonnormal_component_rank_budget
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    center K = ⊥ ∧ ∀ r : ℕ, r.Prime → Odd r →
      twoLocalPrimeRank r K + primeRank r K ≤ 2 := by
  have hz := source_a5_oddNormalizer_nonnormal_component_center_eq_bot
    D e hn hp B hne hB hBC hBV hperm K hK hnK houtK hFK
  have hqt := (oddNormalizer_properQTK D.simpleQTKE B hne).2.1
  exact ⟨hz,fun r hr ho =>
    hK.local_add_ordinary_rank_le_two_of_nonnormal_centerless hqt hnK hz r hr ho⟩

end CFSG.Quasithin.Chapter10
