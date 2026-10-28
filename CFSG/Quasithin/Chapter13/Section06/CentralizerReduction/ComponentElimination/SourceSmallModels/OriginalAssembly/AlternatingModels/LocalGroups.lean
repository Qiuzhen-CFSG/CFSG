module
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Action
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.PrimeRankCubeFree

/-!
# The original A₇ plus component as classifier input

The complete K-group hypothesis descends from the actual involution
centralizer to the actual component image. The A₇ order 2520 has no odd
prime cube, giving the required strongly quasithin rank bounds.
Relative normalization and Lᵥ containment identify the plus actor with
KTᵥ; its quotient by the normal component is consequently a two-group.
The component is nonabelian simple, so its centralizer embeds in that
two-group quotient and vanishes under the original trivial two-core input.

These inputs prepare B.5.1 on the literal plus action before any short-block
recognition. No classification conclusion or module model is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
paragraph preceding 13.6.14, printed p.929, and 13.6.22, printed p.932.
-/

public section
open Subgroup Theory.GroupTheory CFSG.Quasithin
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels
universe u
variable {G : Type u} [Group G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- The full K-class descends along the source projection, and the actual
A₇ order supplies every odd-prime rank bound. -/
theorem component_sqtk [Finite G] {Ξ : GroupClass.{u}}
    (hY : K ∈ Yz L T z v)
    (hsource : IsKGroup Ξ (Gv v))
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 7)) :
    IsSQTK Ξ (plusImage K L T z v hL hz K) := by
  have hcard : Nat.card (plusImage K L T z v hL hz K) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  refine ⟨?_, ?_⟩
  · intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    apply primeRank_le_two_of_cube_not_dvd
    rw [hcard]
    intro hd
    have hpd : p ∣ 2 ^ 3 * 3 ^ 2 * 5 * 7 :=
      (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
    have hsmall : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 7 := by
      rcases hp.dvd_mul.mp hpd with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact .inl (hp.dvd_of_dvd_pow h)
          · exact .inr (.inl (hp.dvd_of_dvd_pow h))
        · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
    have heq (q : ℕ) (hq : q.Prime) (h : p ∣ q) : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    rcases hsmall with h | h | h | h
    · have he := heq 2 (by decide) h
      subst p
      exact ho.not_two_dvd_nat (dvd_refl 2)
    · have he := heq 3 (by decide) h
      subst p
      norm_num at hd
    · have he := heq 5 (by decide) h
      subst p
      norm_num at hd
    · have he := heq 7 (by decide) h
      subst p
      norm_num at hd
  · exact (hsource.of_injective (inclusion hY.1.1) (inclusion_injective hY.1.1)).of_surjective
      (imageProjection K L T z v hL hz K (K_le_plusActor K L T v))
      (imageProjection_surjective K L T z v hL hz K (K_le_plusActor K L T v))

/-- Relative normalization and the original residual containment generate
the whole plus actor from the component and the Sylow image. -/
theorem component_plus_generation
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K) :
    plusImage K L T z v hL hz K ⊔ plusImage K L T z v hL hz (Tv T v) = ⊤ := by
  rw [plusImage, plusImage, ← Subgroup.map_sup, ← subgroupOf_sup
    (K_le_plusActor K L T v)
    (show Tv T v ≤ plusActor K L T v from le_sup_right),
    ← ComponentElimination.SourceOrthogonal.LocalAction.plusActor_eq K L T v hn hLK, subgroupOf_self,
    map_top_of_surjective _ (plusMk_surjective K L T z v hL hz)]

/-- The original simple component is self-centralizing in the actual plus
actor under its earlier two-reducedness hypothesis. -/
theorem component_centralizer_eq_bot [Finite G]
    (hY : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 7)) :
    centralizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) = ⊥ := by
  let C := plusImage K L T z v hL hz K
  let : C.Normal := component_image_normal K L T z v hL hz hn hLK
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  let : IsQuasisimple C := plusImage_K_quasisimple K L T z v hL hz hY hR
  obtain ⟨S, hS⟩ := hSylow
  have hT : IsPGroup 2 (Tv T v) := hS ▸ S.isPGroup'.map (Gv v).subtype
  have hquot : IsPGroup 2 (Gplus K L T z v hL hz ⧸ C) :=
    isPGroup_quotient_of_sup_eq_top C (plusImage K L T z v hL hz (Tv T v))
      (hT.comap_subtype.map _) (component_plus_generation K L T z v hL hz hn hLK)
  exact centralizer_eq_bot_of_simple_two_quotient C
    (Group.IsPerfect.not_isMulCommutative C) hquot hR

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels
