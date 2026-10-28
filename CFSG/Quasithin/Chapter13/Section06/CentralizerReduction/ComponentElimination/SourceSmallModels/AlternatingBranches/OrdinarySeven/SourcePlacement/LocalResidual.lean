module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual.Normalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual.ResidualLift
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual.Permutation
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# The ordinary A₇ local residual and its six-point application

The actual normalizer maps onto the even three-pair normalizer. By 13.6.5
it lies in Mᵥ, so relative normality of Lᵥ gives normalization of its image.
The finite permutation theorem places that solvable image in the
normalizer with two-power index. Baumann heredity lifts containment, and the
two-group kernel and two-perfectness of Lᵥ identify the original residual.
The final source theorem applies this identity to the existing six-point construction.

The finite permutation statement is proved in the imported `Permutation` module
and discharged in `source_residual_eq` and `source_le_replacement`. The compatible
marking remains an explicit input supplied by the independent marking argument.
The full block hypothesis is retained at the source boundary; this calculation
uses its compatible quotient coordinates. The Sylow information comes from
literal Y_z membership. All normality used for Lᵥ is relative to Mᵥ.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932 (PDF p.949).
-/

public section
open Subgroup Equiv
open CFSG.Quasithin
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem actionImage_component (K H : Subgroup G) (hKH : K ≤ H)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (ρ : H →* Perm (Fin 7))
    (hρ : ∀ k : K, ρ ⟨k, hKH k.property⟩ = (blockProjection K e k : Perm (Fin 7))) :
    actionImage H ρ K = alternatingGroup (Fin 7) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [hρ ⟨k, hk⟩]
    exact (blockProjection K e ⟨k, hk⟩).property
  · intro hx
    obtain ⟨k, hk⟩ := blockProjection_surjective K e ⟨x, hx⟩
    exact ⟨⟨k, hKH k.property⟩, k.property, (hρ k).trans (congrArg Subtype.val hk)⟩

/-- Conditional source assembly, retaining the precise finite permutation premise.
The action kernel, normalizer comparison and residual lifting are discharged here. -/
theorem source_residual_of_permutation_local
    (hfinite : PermutationLocalStatement)
    (K L T M S : Subgroup G) (z v : G)
    (_hblock : ChapterC.IsAlternatingBlock K 7)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hS : S = ChapterB.baumann (Tv T v))
    (hLM : Lv L v ≤ Mv M v) (hLn : ((Lv L v).subgroupOf (Mv M v)).Normal)
    (h65 : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hφ : Function.Injective φ)
    (hcompat : ∀ k : K,
      φ (plusMk K L T z v hL hz ⟨k, component_le_actor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7)))
    (hJ : (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
      threeTranspositions)
    (hSJ : plusImage K L T z v hL hz S =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)))
    (h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card (plusImage K L T z v hL hz (Lv L v)) →
      p = 2 ∨ p = 3)
    (P3 : Sylow 3 (plusImage K L T z v hL hz (Lv L v))) (hP3 : Nat.card P3 = 3) :
    Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
      (K ⊓ normalizer (S : Set G)).subtype := by
  let H := plusActor K L T v
  let q := plusMk K L T z v hL hz
  let ρ := φ.comp q
  let N := K ⊓ normalizer (S : Set G)
  let D := actionImage H ρ (Lv L v)
  have hKH : K ≤ H := component_le_actor K L T v
  have hLH : Lv L v ≤ H := hLK.trans hKH
  have hNH : N ≤ H := inf_le_left.trans hKH
  have hTH : Tv T v ≤ H := le_sup_right
  have hSH : S ≤ H := (show S ≤ Tv T v from hS ▸ inf_le_left).trans hTH
  have hplus (A : Subgroup G) : actionImage H ρ A = (plusImage K L T z v hL hz A).map φ :=
    (map_map _ _ _).symm
  have hmark : actionImage H ρ S = threeTranspositions := by rw [hplus, hSJ, hJ]
  have hKimage : actionImage H ρ K = alternatingGroup (Fin 7) :=
    actionImage_component K H hKH e ρ hcompat
  have hNimage : actionImage H ρ N = evenPairNormalizer := by
    rw [hplus, plus_normalizer_comparison K L T S z v hL hz hY hK hLK hS e φ hφ hcompat,
      map_relative_normalizer_of_injective _ _ φ hφ]
    rw [← hplus K, ← hplus S, hKimage, hmark]
    rfl
  have hNM : N ≤ Mv M v :=
    (inf_le_inf_right _ hY.1.1).trans h65
  have hnormal : N ≤ normalizer (Lv L v : Set G) :=
    hNM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
  have hDn : evenPairNormalizer ≤ normalizer (D : Set (Perm (Fin 7))) := by
    rw [← hNimage]
    rintro x ⟨n, hn, rfl⟩
    exact actionImage_normalizer H (Lv L v) ρ hLH n (hnormal hn)
  have hDalt : D ≤ alternatingGroup (Fin 7) := by
    rw [← hKimage]
    exact map_mono (subgroupOf_mono H hLK)
  have hDcard : Nat.card D = Nat.card (plusImage K L T z v hL hz (Lv L v)) := by
    change Nat.card (actionImage H ρ (Lv L v)) = _
    rw [hplus]
    exact (Nat.card_congr ((plusImage K L T z v hL hz (Lv L v)).equivMapOfInjective φ hφ).toEquiv).symm
  have hsolv : Group.IsSolvable D := by
    apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hd
    rw [hDcard] at hd
    exact h23 p hp hd
  have hthree : 3 ∣ Nat.card D := by
    rw [hDcard, ← hP3]
    exact P3.toSubgroup.card_subgroup_dvd_card
  obtain ⟨hDN, hindex⟩ := hfinite D hDalt hsolv hthree hDn
  have hSyl : Chapter1.IsSylowIn 2 (Tv T v) (K ⊔ Tv T v) := hY.1.2.2.1
  have hT : IsPGroup 2 (Tv T v) := (Chapter1.isSylowIn_iff.mp hSyl).1
  have hqker := plus_kernel_isPGroup K L T z v hL hz hK hLK hT e φ hφ hcompat
  have hρker : IsPGroup 2 ρ.ker := by
    rw [MonoidHom.ker_comp_of_injective q φ hφ]
    exact hqker
  rw [← actor_eq K L T v hK hLK] at hSyl
  obtain ⟨P, hP⟩ := hSyl
  have hkT : ρ.ker ≤ (Tv T v).subgroupOf H := by
    intro x hx
    change (x : G) ∈ Tv T v
    rw [← hP]
    exact ⟨x, hρker.le_sylow_of_normal P hx, rfl⟩
  have hLN : Lv L v ≤ N := by
    intro l hl
    refine ⟨hLK hl, ?_⟩
    apply mem_normalizer_of_image H (Tv T v) S ρ hTH hS hkT ⟨l, hLH hl⟩
    change ρ ⟨l, hLH hl⟩ ∈ normalizer (actionImage H ρ S : Set _)
    rw [hmark]
    exact (hDN ⟨⟨l, hLH hl⟩, hl, rfl⟩).2
  have hLnN : ((Lv L v).subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLN).mpr hnormal
  apply residual_eq_of_action_index H (Lv L v) N hLH hNH hLN hLnN ρ hρker
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v))
  change ∃ n, D.relIndex (actionImage H ρ N) = 2 ^ n
  rwa [hNimage]
/-- Apply the derived residual identity to the actual six-point replacement.
The final export below supplies the finite permutation theorem. -/
theorem source_placement_of_permutation_local
    (hfinite : PermutationLocalStatement)
    (K L T M S : Subgroup G) (z v : G)
    (_hblock : ChapterC.IsAlternatingBlock K 7)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hS : S = ChapterB.baumann (Tv T v))
    (hLM : Lv L v ≤ Mv M v) (hLn : ((Lv L v).subgroupOf (Mv M v)).Normal)
    (h65 : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hφ : Function.Injective φ)
    (hcompat : ∀ k : K,
      φ (plusMk K L T z v hL hz ⟨k, component_le_actor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7)))
    (hJ : (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
      threeTranspositions)
    (hSJ : plusImage K L T z v hL hz S =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)))
    (h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card (plusImage K L T z v hL hz (Lv L v)) →
      p = 2 ∨ p = 3)
    (P3 : Sylow 3 (plusImage K L T z v hL hz (Lv L v))) (hP3 : Nat.card P3 = 3) :
    Lv L v ≤ replacement K e 6 := by
  have hr := source_residual_of_permutation_local hfinite K L T M S z v _hblock
    hL hz hY hK hLK hS hLM hLn h65 e φ hφ hcompat hJ hSJ h23 P3 hP3
  rw [hr]
  apply residual_le_replacement K e 6
  let H := plusActor K L T v
  let ρ := φ.comp (plusMk K L T z v hL hz)
  have hSH : S ≤ H := (show S ≤ Tv T v from hS ▸ inf_le_left).trans le_sup_right
  apply normalizer_le_preimage_of_marking K H S (component_le_actor K L T v) hSH e ρ hcompat
  change ((S.subgroupOf H).map (φ.comp (plusMk K L T z v hL hz))) = _
  rw [← map_map]
  change (plusImage K L T z v hL hz S).map φ = _
  rw [hSJ, hJ]

/-- The ordinary A₇ local residual identity, with all branch-specific normalizer,
permutation placement and quotient premises discharged. The marking and genuine
earlier source inputs remain the responsibility of their source producers. -/
theorem source_residual_eq
    (K L T M S : Subgroup G) (z v : G)
    (_hblock : ChapterC.IsAlternatingBlock K 7)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hS : S = ChapterB.baumann (Tv T v))
    (hLM : Lv L v ≤ Mv M v) (hLn : ((Lv L v).subgroupOf (Mv M v)).Normal)
    (h65 : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hφ : Function.Injective φ)
    (hcompat : ∀ k : K,
      φ (plusMk K L T z v hL hz ⟨k, component_le_actor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7)))
    (hJ : (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
      threeTranspositions)
    (hSJ : plusImage K L T z v hL hz S =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)))
    (h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card (plusImage K L T z v hL hz (Lv L v)) →
      p = 2 ∨ p = 3)
    (P3 : Sylow 3 (plusImage K L T z v hL hz (Lv L v))) (hP3 : Nat.card P3 = 3) :
    Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
      (K ⊓ normalizer (S : Set G)).subtype :=
  source_residual_of_permutation_local permutation_local_statement
    K L T M S z v _hblock hL hz hY hK hLK hS hLM hLn h65 e φ hφ hcompat hJ hSJ h23 P3 hP3

/-- The source local residual lies in the actual six-point residual lift. -/
theorem source_le_replacement
    (K L T M S : Subgroup G) (z v : G)
    (_hblock : ChapterC.IsAlternatingBlock K 7)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hS : S = ChapterB.baumann (Tv T v))
    (hLM : Lv L v ≤ Mv M v) (hLn : ((Lv L v).subgroupOf (Mv M v)).Normal)
    (h65 : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hφ : Function.Injective φ)
    (hcompat : ∀ k : K,
      φ (plusMk K L T z v hL hz ⟨k, component_le_actor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7)))
    (hJ : (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
      threeTranspositions)
    (hSJ : plusImage K L T z v hL hz S =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)))
    (h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card (plusImage K L T z v hL hz (Lv L v)) →
      p = 2 ∨ p = 3)
    (P3 : Sylow 3 (plusImage K L T z v hL hz (Lv L v))) (hP3 : Nat.card P3 = 3) :
    Lv L v ≤ replacement K e 6 :=
  source_placement_of_permutation_local permutation_local_statement
    K L T M S z v _hblock hL hz hY hK hLK hS hLM hLn h65 e φ hφ hcompat hJ hSJ h23 P3 hP3

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual

end
