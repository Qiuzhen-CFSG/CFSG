module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.OddNormalizerReduction
public import Theory.GroupTheory.ComponentSaturatedSylow

/-!
# Two-subgroup saturation in the actual odd-normalizer overlap

Covering uniqueness is used on F N_T(B), retaining both factors. A two-group
normalized by M intersect N_G(B) has normalizer contained in M, so lies in
the two-core of that actual overlap. Component-orbit saturation therefore
controls stabilizer-invariant two-subgroups inside any ordinary component.

Source: Aschbacher--Smith 4.4.7 and 4.4.10, printed pp.620--621. No SQTK
hypothesis on the odd normalizer or uniqueness for F alone is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original covering uniqueness saturates the literal overlap. -/
theorem source_a5_oddNormalizer_overlap_saturation
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (P : Subgroup (normalizer (B : Set G))) (hP : IsPGroup 2 P)
    (hMP : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (P : Set (normalizer (B : Set G)))) :
    P ≤ (D.maximalLocal.subgroupOf (normalizer (B : Set G))).pCoreIn 2 := by
  let N := normalizer (B : Set G)
  let Y := D.maximalLocal.subgroupOf N
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  have hPY : P ≤ Y := by
    by_cases hb : P = ⊥
    · rw [hb]; exact bot_le
    have hne : P.map N.subtype ≠ ⊥ := fun he =>
      hb ((P.map_eq_bot_iff_of_injective N.subtype_injective).mp he)
    have hodd : Odd (Nat.card B) := by
      obtain ⟨n,he⟩ := hB.exists_card_eq
      rw [he]
      exact hp.pow
    obtain ⟨hIM,hIN,_,_⟩ := source_oddActor_normalizerJoin_input D B hBC hodd hBV
    have hIP : I ≤ normalizer (P.map N.subtype : Set G) := by
      intro i hi
      exact P.le_normalizer_map N.subtype
        ⟨⟨i,hIN hi⟩,hMP (show (⟨i,hIN hi⟩ : N) ∈ Y from hIM hi),rfl⟩
    have hu := source_a5_oddPrimeNormalizer_covering_uniqueness D e hn hp B hB hBC hBV hperm
    have hNM := normalizer_le_of_unique_maximalTwoLocal hu.2.2 (hP.map N.subtype) hne hIP
    intro x hx
    exact hNM ((P.map N.subtype).le_normalizer (mem_map_of_mem N.subtype hx))
  exact le_pCoreIn_of_normalizes hP hPY hMP

/-- The overlap's component stabilizer controls the same component two-group. -/
theorem source_a5_oddNormalizer_component_core_saturation
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (P : Subgroup (normalizer (B : Set G))) (hPK : P ≤ K) (hP : IsPGroup 2 P)
    (hMP : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ⊓
      normalizer (K : Set (normalizer (B : Set G))) ≤
      normalizer (P : Set (normalizer (B : Set G)))) :
    P ≤ (D.maximalLocal.subgroupOf (normalizer (B : Set G))).pCoreIn 2 := by
  exact hK.stabilizer_saturation
    (fun Q hQ hMQ => source_a5_oddNormalizer_overlap_saturation D e hn hp B hB hBC hBV hperm Q hQ hMQ)
    P hPK hP hMP

end CFSG.Quasithin.Chapter10
