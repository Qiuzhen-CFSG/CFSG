module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Numerics
/-!
# The common involution image in the non-Omega branch

The original four action alternatives already give a cyclic Sylow image
outside the Omega row. A cyclic group has a unique subgroup of order two;
the no-FF quadratic-actor bound therefore identifies all the source images.
This argument precedes the exclusion of the cubic-centralizer rows and does
not yet prove the characterization using the odd core.

Source: Aschbacher--Smith 15.2.13(2), printed pp.1111--1112,
combined manuscript of 1 March 2004, refs/quasithin.pdf.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- A cyclic finite group has at most one subgroup of order two. -/
private theorem two_subgroups_eq [IsCyclic G] (A B : Subgroup G)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2) : A = B := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let F := Finset.univ.filter (fun x : G => x ^ 2 = 1)
  have hc : F.card ≤ 2 := IsCyclic.card_pow_eq_one_le (by decide : 0 < 2)
  have he (C : Subgroup G) (hC : Nat.card C = 2) : (C : Set G).toFinset = F := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      rw [←hC]
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,Set.mem_toFinset.mp hx⟩ : C)))
    · rw [Set.toFinset_card,←Nat.card_eq_fintype_card]
      change F.card ≤ Nat.card C
      rw [hC]
      exact hc
  ext x
  have hh := (he A hA).trans (he B hB).symm
  simpa only [Set.mem_toFinset,SetLike.mem_coe] using (Finset.ext_iff.mp hh x)

/-- Removing the Omega row makes the actual Sylow image cyclic, even before
excluding the cubic-centralizer rows. -/
theorem sylow_image_cyclic {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (ho : letI := h.prepared.elementary
      ¬ SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    IsCyclic (actor M V (T : Subgroup G) h.prepared.normalized) := by
  let := h.prepared.elementary
  let P : Sylow 2 (internalActionImage M V h.prepared.normalized) :=
    (T.subtype h.maximal.1.2).mapSurjective
    (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have hsmall (hc : Nat.card (internalActionImage M V h.prepared.normalized) = 6 ∨
      Nat.card (internalActionImage M V h.prepared.normalized) = 18) : IsCyclic P := by
    have hh := P.card_eq_multiplicity
    rcases hc with hc | hc
    all_goals
      rw [hc] at hh
      norm_num [show (Nat.factorization 6) 2 = 1 from by decide +kernel,
        show (Nat.factorization 18) 2 = 1 from by decide +kernel] at hh
      exact isCyclic_of_prime_card (p := 2) hh
  rcases ha with ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩ | hω | ⟨_,hs,_⟩
  · apply hsmall
    left
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  · apply hsmall
    right
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  · exact (ho hω).elim
  · rcases hs with he | he
    all_goals obtain ⟨e⟩ := he
    all_goals exact isCyclic_of_injective e.toMonoidHom e.injective

/-- Order two determines a subgroup of the literal cyclic Sylow image. -/
theorem order_two_images_eq {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (ho : letI := h.prepared.elementary
      ¬ SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    {A B : Subgroup (internalActionImage M V h.prepared.normalized)}
    (hAP : A ≤ actor M V (T : Subgroup G) h.prepared.normalized)
    (hBP : B ≤ actor M V (T : Subgroup G) h.prepared.normalized)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2) : A = B := by
  let P := actor M V (T : Subgroup G) h.prepared.normalized
  let := sylow_image_cyclic h ha ho
  have he := two_subgroups_eq (A.subgroupOf P) (B.subgroupOf P)
    ((Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv).trans hA)
    ((Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv).trans hB)
  have hm := congrArg (Subgroup.map P.subtype) he
  exact (map_subgroupOf_eq_of_le (show A ≤ P from hAP)).symm.trans
    (hm.trans (map_subgroupOf_eq_of_le (show B ≤ P from hBP)))

/-- All nontrivial quadratic elementary images inside the source Sylow image
coincide in the non-Omega branch. -/
theorem quadratic_images_eq {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (ho : letI := h.prepared.elementary
      ¬ SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    letI := h.prepared.elementary
    ∀ A B : Subgroup (internalActionImage M V h.prepared.normalized),
      A ≤ actor M V (T : Subgroup G) h.prepared.normalized →
      B ≤ actor M V (T : Subgroup G) h.prepared.normalized →
      IsElementaryTwo A → IsElementaryTwo B →
      IsQuadratic (imageRepresentation M V h.prepared.normalized) A →
      IsQuadratic (imageRepresentation M V h.prepared.normalized) B → A = B := by
  let := h.prepared.elementary
  intro A B hAP hBP hA hB hqA hqB
  have hc (C : Subgroup (internalActionImage M V h.prepared.normalized))
      (hC : IsElementaryTwo C)
      (hq : IsQuadratic (imageRepresentation M V h.prepared.normalized) C) : Nat.card C = 2 := by
    have hr := (h.quadratic_actor C hC hq).1
    simpa only [hr,pow_one] using hC.card_eq_two_pow_rank
  exact order_two_images_eq h ha ho hAP hBP (hc A hA hqA) (hc B hB hqB)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
