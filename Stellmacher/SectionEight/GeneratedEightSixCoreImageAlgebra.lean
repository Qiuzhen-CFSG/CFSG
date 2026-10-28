module

public import Stellmacher.SectionEight.GeneratedEightSixCoreGenerationTools

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven
open scoped commutatorElement Pointwise

universe u

public theorem eight_six_commutator_card_of_disjoint_conjugate
    {G : Type u} [Group G] [Finite G]
    (A P Q R : Subgroup G) (hAP : A ≤ P) (hAQ : A ≤ Q)
    (actor : G) (hactor : actor ∈ R)
    (hdisjoint : P ⊓ P.map (MulAut.conj actor).toMonoidHom = ⊥) :
    Nat.card A ≤ Nat.card (⁅Q, R⁆ : Subgroup G) := by
  let displacement : A → (⁅Q, R⁆ : Subgroup G) := fun element =>
    ⟨⁅(element : G), actor⁆, Subgroup.commutator_mem_commutator
      (hAQ element.property) hactor⟩
  apply Nat.card_le_card_of_injective displacement
  intro first second heq
  have hcomm : ⁅(first : G), actor⁆ = ⁅(second : G), actor⁆ :=
    congrArg Subtype.val heq
  have hfix : (MulAut.conj actor) ((second : G)⁻¹ * first) =
      (second : G)⁻¹ * first := by
    change actor * ((second : G)⁻¹ * first) * actor⁻¹ = _
    calc
      actor * ((second : G)⁻¹ * first) * actor⁻¹ =
          (second : G)⁻¹ * ⁅(second : G), actor⁆ *
            ⁅(first : G), actor⁆⁻¹ * first := by
        simp only [commutatorElement_def]
        group
      _ = (second : G)⁻¹ * first := by rw [hcomm]; group
  have hmem : (second : G)⁻¹ * first ∈ P :=
    P.mul_mem (P.inv_mem (hAP second.property)) (hAP first.property)
  have hone : (second : G)⁻¹ * first = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hdisjoint]
    exact ⟨hmem, Subgroup.mem_map.mpr ⟨_, hmem, hfix⟩⟩
  exact Subtype.ext ((inv_mul_eq_one.mp hone).symm)

public theorem eight_six_commutator_eq_of_disjoint_conjugate
    {G : Type u} [Group G] [Finite G]
    (A B P Q R : Subgroup G) (hAP : A ≤ P) (hAQ : A ≤ Q)
    (hbound : ⁅Q, R⁆ ≤ B) (hcard : Nat.card A = Nat.card B)
    (actor : G) (hactor : actor ∈ R)
    (hdisjoint : P ⊓ P.map (MulAut.conj actor).toMonoidHom = ⊥) :
    ⁅Q, R⁆ = B := by
  apply Subgroup.eq_of_le_of_card_ge hbound
  rw [← hcard]
  exact eight_six_commutator_card_of_disjoint_conjugate A P Q R hAP hAQ
    actor hactor hdisjoint

public theorem eight_six_map_inf_of_kernel_le
    {G F : Type*} [Group G] [Group F]
    (projection : G →* F) (hsurjective : Function.Surjective projection)
    (P R : Subgroup G) (hP : projection.ker ≤ P) (hR : projection.ker ≤ R) :
    (P ⊓ R).map projection = P.map projection ⊓ R.map projection := by
  apply Subgroup.comap_injective hsurjective
  rw [Subgroup.comap_map_eq_self (le_inf hP hR), Subgroup.comap_inf,
    Subgroup.comap_map_eq_self hP, Subgroup.comap_map_eq_self hR]

public theorem eight_six_card_map_eq_of_kernel_le
    {G F : Type*} [Group G] [Finite G] [Group F]
    (projection : G →* F) (A B : Subgroup G)
    (hA : projection.ker ≤ A) (hB : projection.ker ≤ B)
    (hcard : Nat.card A = Nat.card B) :
    Nat.card (A.map projection) = Nat.card (B.map projection) := by
  have hfirst := (projection.ker.subgroupOf A).card_mul_index
  have hsecond := (projection.ker.subgroupOf B).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv] at hfirst
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv] at hsecond
  change Nat.card projection.ker * projection.ker.relIndex A = Nat.card A at hfirst
  change Nat.card projection.ker * projection.ker.relIndex B = Nat.card B at hsecond
  rw [Subgroup.relIndex_ker] at hfirst hsecond
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hfirst.trans (hcard.trans hsecond.symm))

public theorem eight_six_map_conjugate
    {G F : Type*} [Group G] [Group F]
    (projection : G →* F) (P : Subgroup G) (actor : G) :
    (P.map (MulAut.conj actor).toMonoidHom).map projection =
      (P.map projection).map (MulAut.conj (projection actor)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext element
  simp

public theorem eight_six_commutator_sup_eq_of_conjugate_intersection
    {G : Type u} [Group G] [Finite G]
    (D A B P Q R : Subgroup G) [D.Normal]
    (hDA : D ≤ A) (hDB : D ≤ B)
    (hAP : A ≤ P) (hAQ : A ≤ Q)
    (hbound : ⁅Q, R⁆ ≤ B) (hcard : Nat.card A = Nat.card B)
    (actor : G) (hactor : actor ∈ R)
    (hintersection : P ⊓ P.map (MulAut.conj actor).toMonoidHom ≤ D) :
    ⁅Q, R⁆ ⊔ D = B := by
  let projection := QuotientGroup.mk' D
  have hker : projection.ker = D := QuotientGroup.ker_mk' D
  have hDP : D ≤ P := hDA.trans hAP
  have hDconjugate : D ≤ P.map (MulAut.conj actor).toMonoidHom := by
    intro element helement
    refine Subgroup.mem_map.mpr ⟨actor⁻¹ * element * actor, ?_, ?_⟩
    · apply hDP
      simpa only [inv_inv] using
        (inferInstance : D.Normal).conj_mem element helement actor⁻¹
    · change actor * (actor⁻¹ * element * actor) * actor⁻¹ = element
      group
  have hdisjoint : P.map projection ⊓
      (P.map projection).map (MulAut.conj (projection actor)).toMonoidHom = ⊥ := by
    rw [← eight_six_map_conjugate, ← eight_six_map_inf_of_kernel_le projection
      (QuotientGroup.mk'_surjective D) P _ (hker.le.trans hDP)
        (hker.le.trans hDconjugate)]
    exact (Subgroup.map_eq_bot_iff _).mpr (hintersection.trans_eq hker.symm)
  have heq := eight_six_commutator_eq_of_disjoint_conjugate
    (A.map projection) (B.map projection) (P.map projection)
    (Q.map projection) (R.map projection)
    (Subgroup.map_mono hAP) (Subgroup.map_mono hAQ)
    (by rw [← Subgroup.map_commutator]; exact Subgroup.map_mono hbound)
    (eight_six_card_map_eq_of_kernel_le projection A B
      (hker.le.trans hDA) (hker.le.trans hDB) hcard)
    (projection actor) (Subgroup.mem_map_of_mem projection hactor) hdisjoint
  rw [← Subgroup.map_commutator, Subgroup.map_eq_map_iff, hker,
    sup_eq_left.mpr hDB] at heq
  exact heq

public theorem eight_six_sup_inter_eq_of_normalizes
    {G : Type u} [Group G] (A B R : Subgroup G)
    (hnormal : A ≤ Subgroup.normalizer (B : Set G))
    (hBR : B ≤ R) (hinter : A ⊓ R ≤ B) :
    (A ⊔ B) ⊓ R = B := by
  apply le_antisymm ?_ (le_inf le_sup_right hBR)
  intro element helement
  have hproduct : element ∈ (A : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hnormal]
    exact helement.1
  obtain ⟨first, hfirst, second, hsecond, rfl⟩ := hproduct
  have hfirstR : first ∈ R := by
    have hmem := R.mul_mem helement.2 (R.inv_mem (hBR hsecond))
    simpa only [mul_inv_cancel_right] using hmem
  exact B.mul_mem (hinter ⟨hfirst, hfirstR⟩) hsecond

public theorem eight_six_commutator_sup_eq_in_ambient
    {G : Type u} [Group G] [Finite G]
    (ambient D A B P Q R : Subgroup G)
    (hnormal : NormalIn D ambient)
    (hPA : P ≤ ambient) (hQA : Q ≤ ambient) (hRA : R ≤ ambient)
    (hBA : B ≤ ambient)
    (hDA : D ≤ A) (hDB : D ≤ B)
    (hAP : A ≤ P) (hAQ : A ≤ Q)
    (hbound : ⁅Q, R⁆ ≤ B) (hcard : Nat.card A = Nat.card B)
    (actor : G) (hactor : actor ∈ R)
    (hintersection : P ⊓ P.map (MulAut.conj actor).toMonoidHom ≤ D) :
    ⁅Q, R⁆ ⊔ D = B := by
  let _ := hnormal.2
  let nativeActor : ambient := ⟨actor, hRA hactor⟩
  have hnativeBound : ⁅Q.subgroupOf ambient, R.subgroupOf ambient⁆ ≤
      B.subgroupOf ambient := by
    apply (Subgroup.map_le_map_iff_of_injective ambient.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQA,
      Subgroup.map_subgroupOf_eq_of_le hRA, Subgroup.map_subgroupOf_eq_of_le hBA]
    exact hbound
  have hnativeCard : Nat.card (A.subgroupOf ambient) =
      Nat.card (B.subgroupOf ambient) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAP.trans hPA)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv]
    exact hcard
  have hnativeInter : P.subgroupOf ambient ⊓
      (P.subgroupOf ambient).map (MulAut.conj nativeActor).toMonoidHom ≤
      D.subgroupOf ambient := by
    rintro element ⟨helement, other, hother, heq⟩
    apply hintersection
    refine ⟨helement, Subgroup.mem_map.mpr ⟨(other : G), hother, ?_⟩⟩
    exact congrArg Subtype.val heq
  have heq := eight_six_commutator_sup_eq_of_conjugate_intersection
    (D.subgroupOf ambient) (A.subgroupOf ambient) (B.subgroupOf ambient)
    (P.subgroupOf ambient) (Q.subgroupOf ambient) (R.subgroupOf ambient)
    (Subgroup.subgroupOf_mono _ hDA) (Subgroup.subgroupOf_mono _ hDB)
    (Subgroup.subgroupOf_mono _ hAP) (Subgroup.subgroupOf_mono _ hAQ)
    hnativeBound hnativeCard nativeActor hactor hnativeInter
  have hmapped := congrArg (fun subgroup : Subgroup ambient => subgroup.map ambient.subtype) heq
  rw [Subgroup.map_sup, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hQA, Subgroup.map_subgroupOf_eq_of_le hRA,
    Subgroup.map_subgroupOf_eq_of_le hnormal.1,
    Subgroup.map_subgroupOf_eq_of_le hBA] at hmapped
  exact hmapped

end Stellmacher.SectionEight
