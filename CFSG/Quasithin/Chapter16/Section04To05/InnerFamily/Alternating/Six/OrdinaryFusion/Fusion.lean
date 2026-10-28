module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Action
public import Theory.SpecificGroups.SymmetricSix.SylowElementaryPair
public import CFSG.Quasithin.Chapter5.Section03CentralizerGeneric
public import Stellmacher.ElementaryAbelianMaxDefs
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.AbelianWeakClosureFusion
import Mathlib.Tactic
/-!
# Weak closure and normalizer fusion in the ordinary A₆ case

An actual Sylow subgroup of S₆ × C₂ is D₈ × C₂ × C₂. Its two elementary
sixteen-groups exhaust the maximal elementary family. Transporting this pair
to T gives relative index two and hence normality in T. Sylow-normalizer
fusion, with its odd action on the pair, proves weak closure. Burnside fusion
then gives transitivity of N_G(A) on the actual conjugacy intersection β.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209), using A.1.35.
-/

@[expose] public section
open Subgroup Equiv Equiv.Perm
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Six.OrdinaryFusion
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z r : G} {T : Sylow 2 G}

noncomputable def ordinarySylowEquiv (M : AlternatingProductModel L z r 6)
    (hLT : L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r) :
    SymmetricSix.SylowElementaryPair.Model ≃* T := by
  have hT : (T : Subgroup G) ≤ AlternatingOvergroup L z r := hLT ▸ le_sup_right
  let S := T.subtype hT
  let P : Sylow 2 Product := S.mapSurjective (f := M.equiv.toMonoidHom) M.equiv.surjective
  let e : T ≃* P := (subgroupOfEquivOfLe hT).symm.trans
    (M.equiv.subgroupMap (S : Subgroup (AlternatingOvergroup L z r)))
  exact (SymmetricSix.SylowElementaryPair.sylowEquiv P).trans e.symm

/-- Construct the second elementary sixteen-group in the actual ambient T. -/
theorem exists_elementary_pair (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ (T : Subgroup G))
    (hLT : L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r) :
    ∃ B : Subgroup G, elementary M ≠ B ∧ B ≤ (T : Subgroup G) ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧
      ((elementary M).subgroupOf (T : Subgroup G)).index = 2 ∧
      (B.subgroupOf (T : Subgroup G)).index = 2 ∧
      ∀ E : Subgroup G, E ≤ (T : Subgroup G) → IsElementaryAbelian 2 E →
        E ≤ elementary M ∨ E ≤ B := by
  let e := ordinarySylowEquiv M hLT
  obtain ⟨C, D, hCD, hCe, hDe, hCc, hDc, hCi, hDi, hcover⟩ :=
    SymmetricSix.SylowElementaryPair.pair_of_equiv e
  let A := (elementary M).subgroupOf (T : Subgroup G)
  have hAe : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hAT
  have hAc : Nat.card A = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans (elementary_card M)
  have hAC : A = C ∨ A = D := by
    rcases hcover A hAe with hC | hD
    · exact Or.inl (eq_of_le_of_card_ge hC (by rw [hAc, hCc]))
    · exact Or.inr (eq_of_le_of_card_ge hD (by rw [hAc, hDc]))
  have assemble (C D : Subgroup T) (hCD : C ≠ D)
      (hDe : IsElementaryAbelian 2 D) (hDc : Nat.card D = 16)
      (hCi : C.index = 2) (hDi : D.index = 2)
      (hcover : ∀ E : Subgroup T, IsElementaryAbelian 2 E → E ≤ C ∨ E ≤ D)
      (hAC : A = C) :
      ∃ B : Subgroup G, elementary M ≠ B ∧ B ≤ (T : Subgroup G) ∧
        IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧
        ((elementary M).subgroupOf (T : Subgroup G)).index = 2 ∧
        (B.subgroupOf (T : Subgroup G)).index = 2 ∧
        ∀ E : Subgroup G, E ≤ (T : Subgroup G) → IsElementaryAbelian 2 E →
          E ≤ elementary M ∨ E ≤ B := by
    let B := D.map (T : Subgroup G).subtype
    let := hDe
    have hBsub : B.subgroupOf (T : Subgroup G) = D := by
      ext x
      change (∃ y : T, y ∈ D ∧ (y : G) = (x : G)) ↔ x ∈ D
      constructor
      · rintro ⟨y, hy, he⟩
        exact (Subtype.ext he : y = x) ▸ hy
      · exact fun hx => ⟨x, hx, rfl⟩
    refine ⟨B, ?_, map_subtype_le _, IsElementaryAbelian.map_subtype,
      (card_map_of_injective (T : Subgroup G).subtype_injective).trans hDc,
      (by change A.index = 2; rw [hAC]; exact hCi), (by rw [hBsub]; exact hDi), ?_⟩
    · intro he
      have hh := congrArg (fun H : Subgroup G => H.subgroupOf (T : Subgroup G)) he
      exact hCD (hAC.symm.trans (hh.trans hBsub))
    · intro E hET hEe
      let := hEe
      have hE : IsElementaryAbelian 2 (E.subgroupOf (T : Subgroup G)) :=
        IsElementaryAbelian.subgroupOf hET
      have hCA : C.map (T : Subgroup G).subtype = elementary M := by
        rw [← hAC, map_subgroupOf_eq_of_le hAT]
      rcases hcover _ hE with hEC | hED
      · have hh := map_mono (f := (T : Subgroup G).subtype) hEC
        rw [map_subgroupOf_eq_of_le hET, hCA] at hh
        exact Or.inl hh
      · have hh := map_mono (f := (T : Subgroup G).subtype) hED
        rw [map_subgroupOf_eq_of_le hET] at hh
        exact Or.inr hh
  rcases hAC with hAC | hAD
  · exact assemble C D hCD hDe hDc hCi hDi hcover hAC
  · exact assemble D C hCD.symm hCe hCc hDi hCi (fun E hE => (hcover E hE).symm) hAD

/-- A(T) is exactly a pair, for the actual maximal-order elementary family. -/
theorem maximal_family_pair (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ (T : Subgroup G))
    (hLT : L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r) :
    ∃ B : Subgroup G, elementary M ≠ B ∧
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) = {elementary M, B} ∧
      (T : Subgroup G) ≤ normalizer (elementary M : Set G) ∧
      (T : Subgroup G) ≤ normalizer (B : Set G) := by
  obtain ⟨B, hAB, hBT, hBe, hBc, hAi, hBi, hcover⟩ := exists_elementary_pair M hAT hLT
  have hncA : (T : Subgroup G) ≤ normalizer (elementary M : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAT).mp
      (((elementary M).subgroupOf (T : Subgroup G)).normal_of_index_eq_two hAi)
  have hncB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hBT).mp
      ((B.subgroupOf (T : Subgroup G)).normal_of_index_eq_two hBi)
  have hbound (E : Subgroup G) (hET : E ≤ (T : Subgroup G)) (hEe : IsElementaryAbelian 2 E) :
      Nat.card E ≤ 16 := by
    rcases hcover E hET hEe with hE | hE
    · simpa only [elementary_card] using card_le_of_le hE
    · simpa only [hBc] using card_le_of_le hE
  refine ⟨B, hAB, ?_, hncA, hncB⟩
  ext E
  change (E ≤ (T : Subgroup G) ∧ IsElementaryAbelian 2 E ∧
    ∀ F : Subgroup G, F ≤ (T : Subgroup G) → IsElementaryAbelian 2 F →
      Nat.card F ≤ Nat.card E) ↔ E ∈ ({elementary M, B} : Set (Subgroup G))
  constructor
  · rintro ⟨hET, hEe, hmax⟩
    have h16 : 16 ≤ Nat.card E := by
      simpa only [elementary_card] using hmax _ hAT inferInstance
    rcases hcover E hET hEe with hE | hE
    · exact Or.inl (eq_of_le_of_card_ge hE (by simpa only [elementary_card] using h16))
    · exact Or.inr (eq_of_le_of_card_ge hE (by simpa only [hBc] using h16))
  · rintro (rfl | hE)
    · exact ⟨hAT, inferInstance, by simpa only [elementary_card] using hbound⟩
    · have he : E = B := hE
      subst E
      exact ⟨hBT, hBe, by simpa only [hBc] using hbound⟩

/-- The two normal members of A(T) cannot fuse: Sylow-normalizer fusion and
its odd action on this two-point family force both to be weakly closed. -/
theorem elementary_weakly_closed (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ (T : Subgroup G))
    (hLT : L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r) :
    ∀ g : G, (elementary M).conjBy g ≤ (T : Subgroup G) →
      (elementary M).conjBy g = elementary M := by
  obtain ⟨B, hAB, hBT, hBe, hBc, hAi, hBi, hcover⟩ := exists_elementary_pair M hAT hLT
  have hncA : (T : Subgroup G) ≤ normalizer (elementary M : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAT).mp
      (((elementary M).subgroupOf (T : Subgroup G)).normal_of_index_eq_two hAi)
  have hncB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hBT).mp
      ((B.subgroupOf (T : Subgroup G)).normal_of_index_eq_two hBi)
  have hp : ∀ V ∈ ({elementary M, B} : Set (Subgroup G)), ∀ g : G,
      V.conjBy g ≤ (T : Subgroup G) → V.conjBy g ∈ ({elementary M, B} : Set (Subgroup G)) := by
    intro V hV g hg
    have hVe : IsElementaryAbelian 2 V := by
      rcases hV with rfl | hV
      · infer_instance
      · exact hV ▸ hBe
    have hVc : Nat.card V = 16 := by
      rcases hV with rfl | hV
      · exact elementary_card M
      · exact hV ▸ hBc
    let := hVe
    have hconje : IsElementaryAbelian 2 (V.conjBy g) := IsElementaryAbelian.map _
    have hconjc : Nat.card (V.conjBy g) = 16 :=
      (card_map_of_injective (MulAut.conj g).injective).trans hVc
    rcases hcover _ hg hconje with ha | hb
    · exact Or.inl (eq_of_le_of_card_ge ha (by rw [hconjc, elementary_card]))
    · exact Or.inr (eq_of_le_of_card_ge hb (by rw [hconjc, hBc]))
  exact CFSG.Quasithin.Chapter5.Section03.weakly_closed_normal_pair T
    (elementary M) B hAB hAT hBT hncA hncB hp _ (Or.inl rfl)
/-- Burnside fusion acts on the corrected set β = zᴳ ∩ A. -/
theorem normalizer_transitive (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ (T : Subgroup G))
    (hLT : L ⊔ (T : Subgroup G) = AlternatingOvergroup L z r) :
    NormalizerTransitive M := by
  intro a ha
  exact T.normalizer_fuses_of_abelian_weakly_closed (elementary M) hAT
    (elementary_weakly_closed M hAT hLT)
    (by simpa only [generator_three] using generator_mem M 3) ha.1 ha.2

end CFSG.Quasithin.Chapter16.Intersections.Six.OrdinaryFusion
