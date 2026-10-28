module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Placements.LocalProducts
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Placements.Transport
/-!
# The actual component and Borel in the five-point tensor actors

Solvability of S₃ and perfectness of A₅ identify the terminal derived
subgroups of both actors. A product Sylow projects to a Sylow of the
five-point factor. Its restriction to A₅ selects a point whose even
stabilizer is its normalizer. The quotient transport then identifies the
literal component and Borel under the prescribed original equivalence.

Source: Aschbacher–Smith, Lemma 14.4.10, printed pp.1010–1011.
-/

public section
open Subgroup Theory.SpecificGroups.TensorThreeFive
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

private instance : Group.IsSolvable S3 := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [range_subtype, ← alternatingGroup_eq_sign_ker]

private instance : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩

theorem alternating_residual : solvableResidual (S3 × A5) =
    (⊥ : Subgroup S3).prod (⊤ : Subgroup A5) := by
  apply le_antisymm
  · apply le_prod_iff.mpr
    exact ⟨(map_solvableResidual_le _).trans (solvableResidual_eq_bot (G := S3)).le, le_top⟩
  · let e := (botProdEquiv (A := S3) (⊤ : Subgroup A5)).trans topEquiv
    let : Group.IsPerfect ((⊥ : Subgroup S3).prod (⊤ : Subgroup A5)) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact le_solvableResidual_of_isPerfect _

theorem symmetric_residual : solvableResidual (S3 × S5) =
    (⊥ : Subgroup S3).prod A5 := by
  apply le_antisymm
  · apply le_prod_iff.mpr
    refine ⟨(map_solvableResidual_le _).trans (solvableResidual_eq_bot (G := S3)).le, ?_⟩
    exact (map_solvableResidual_le _).trans
      ((solvableResidual_le_derivedSeries 1).trans (by
        rw [derivedSeries_one]
        exact alternatingGroup.commutator_perm_le))
  · let e := botProdEquiv (A := S3) A5
    let : Group.IsPerfect ((⊥ : Subgroup S3).prod A5) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact le_solvableResidual_of_isPerfect _

private theorem normalizer_bot_prod {D : Type*} [Group D] (B : Subgroup D) :
    normalizer ((⊥ : Subgroup S3).prod B : Set (S3 × D)) =
      (⊤ : Subgroup S3).prod (normalizer (B : Set D)) := by
  ext x
  change (∀ y : S3 × D, y ∈ (⊥ : Subgroup S3).prod B ↔
    x * y * x⁻¹ ∈ (⊥ : Subgroup S3).prod B) ↔ True ∧ x.2 ∈ normalizer (B : Set D)
  rw [true_and]
  constructor
  · intro h z
    have hh := h (1,z)
    change ((1 : S3) = 1 ∧ z ∈ B) ↔ (x.1 * 1 * x.1⁻¹ = 1 ∧ x.2 * z * x.2⁻¹ ∈ B) at hh
    change z ∈ B ↔ x.2 * z * x.2⁻¹ ∈ B
    simpa only [mul_one, mul_inv_cancel, true_and] using hh
  · intro h y
    change (y.1 = 1 ∧ y.2 ∈ B) ↔ (x.1 * y.1 * x.1⁻¹ = 1 ∧ x.2 * y.2 * x.2⁻¹ ∈ B)
    have hc : x.1 * y.1 * x.1⁻¹ = 1 ↔ y.1 = 1 := (MulAut.conj x.1).map_eq_one_iff
    have hy : y.2 ∈ B ↔ x.2 * y.2 * x.2⁻¹ ∈ B := h y.2
    rw [hc, ← hy]

private theorem product_relative_normalizer {D : Type*} [Group D] [Finite D]
    (P : Sylow 2 (S3 × D)) (A : Subgroup D) :
    (⊥ : Subgroup S3).prod A ⊓
      normalizer (((P : Subgroup (S3 × D)) ⊓ (⊥ : Subgroup S3).prod A : Subgroup (S3 × D)) : Set (S3 × D)) =
      (⊥ : Subgroup S3).prod
        (A ⊓ normalizer ((P.map (MonoidHom.snd S3 D) ⊓ A : Subgroup D) : Set D)) := by
  have hprod : (P : Subgroup (S3 × D)) =
      (P.map (MonoidHom.fst S3 D)).prod (P.map (MonoidHom.snd S3 D)) := by
    apply Eq.symm
    apply P.is_maximal'
    · obtain ⟨m, hm⟩ := (P.isPGroup'.map (MonoidHom.fst S3 D)).exists_card_eq
      obtain ⟨n, hn⟩ := (P.isPGroup'.map (MonoidHom.snd S3 D)).exists_card_eq
      apply IsPGroup.of_card (n := m + n)
      rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, hm, hn, pow_add]
    · intro x hx
      exact ⟨mem_map_of_mem _ hx, mem_map_of_mem _ hx⟩
  have hI : (P : Subgroup (S3 × D)) ⊓ (⊥ : Subgroup S3).prod A =
      (⊥ : Subgroup S3).prod (P.map (MonoidHom.snd S3 D) ⊓ A) := by
    nth_rw 1 [hprod]
    ext x
    change ((x.1 ∈ P.map (MonoidHom.fst S3 D) ∧ x.2 ∈ P.map (MonoidHom.snd S3 D)) ∧
      x.1 = 1 ∧ x.2 ∈ A) ↔ (x.1 = 1 ∧ x.2 ∈ P.map (MonoidHom.snd S3 D) ∧ x.2 ∈ A)
    constructor
    · rintro ⟨⟨_,hq⟩,h1,ha⟩
      exact ⟨h1,hq,ha⟩
    · rintro ⟨h1,hq,ha⟩
      exact ⟨⟨h1.symm ▸ (P.map (MonoidHom.fst S3 D)).one_mem,hq⟩,h1,ha⟩
  rw [hI, normalizer_bot_prod]
  ext x
  simp only [mem_inf, mem_prod, mem_top, true_and]
  tauto

theorem alternating_model_borel (P : Sylow 2 (S3 × A5)) : ∃ i : Fin 5,
    solvableResidual (S3 × A5) ⊓ normalizer
      (((P : Subgroup (S3 × A5)) ⊓ solvableResidual (S3 × A5) : Subgroup (S3 × A5)) : Set (S3 × A5)) =
      (⊥ : Subgroup S3).prod (MulAction.stabilizer A5 i) := by
  let Q := P.mapSurjective (f := MonoidHom.snd S3 A5) (fun x => ⟨(1,x),rfl⟩)
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Q
  refine ⟨i, ?_⟩
  rw [alternating_residual, product_relative_normalizer, inf_top_eq, top_inf_eq]
  exact congrArg (Subgroup.prod (⊥ : Subgroup S3)) hi

theorem symmetric_model_borel (P : Sylow 2 (S3 × S5)) : ∃ i : Fin 5,
    solvableResidual (S3 × S5) ⊓ normalizer
      (((P : Subgroup (S3 × S5)) ⊓ solvableResidual (S3 × S5) : Subgroup (S3 × S5)) : Set (S3 × S5)) =
      (⊥ : Subgroup S3).prod (A5 ⊓ MulAction.stabilizer S5 i) := by
  let Q := P.mapSurjective (f := MonoidHom.snd S3 S5) (fun x => ⟨(1,x),rfl⟩)
  obtain ⟨R, hR⟩ := Q.exists_sylow_map_eq_inf_of_normal A5
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  have hN : (normalizer (R : Set A5)).map (A5).subtype =
      A5 ⊓ normalizer (((Q : Subgroup S5) ⊓ A5 : Subgroup S5) : Set S5) := by
    have h : ((R : Subgroup A5).map (A5).subtype).subgroupOf A5 = (R : Subgroup A5) :=
      comap_map_eq_self_of_injective (A5).subtype_injective _
    change (normalizer ((R : Subgroup A5) : Set A5)).map (A5).subtype = _
    nth_rw 1 [← h]
    rw [← subgroupOf_normalizer_eq (map_subtype_le _), subgroupOf_map_subtype,
      hR, inf_comm]
  have hI : (MulAction.stabilizer A5 i).map (A5).subtype = A5 ⊓ MulAction.stabilizer S5 i := by
    ext x
    exact ⟨fun ⟨y, hy, he⟩ => he ▸ ⟨y.property,hy⟩,
      fun ⟨ha, hi⟩ => ⟨⟨x,ha⟩,hi,rfl⟩⟩
  refine ⟨i, ?_⟩
  rw [symmetric_residual, product_relative_normalizer]
  change (⊥ : Subgroup S3).prod (A5 ⊓ normalizer (((Q : Subgroup S5) ⊓ A5 : Subgroup S5) : Set S5)) = _
  rw [← hN, hi, hI]

variable {G : Type*} [Group G] [Finite G] {H T : Subgroup G}

/-- The actual component image in the prescribed alternating actor coordinates. -/
theorem alternating_component_image (e : coreQuotient H ≃* S3 × A5) :
    (star H (component H)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (⊤ : Subgroup A5) := by
  rw [map_star_component, alternating_residual]

/-- The actual component image in the prescribed symmetric actor coordinates. -/
theorem symmetric_component_image (e : coreQuotient H ≃* S3 × S5) :
    (star H (component H)).map e.toMonoidHom = (⊥ : Subgroup S3).prod A5 := by
  rw [map_star_component, symmetric_residual]

/-- The actual alternating Borel fixes the point selected by the component Sylow. -/
theorem alternating_borel_image
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × A5) : ∃ i : Fin 5,
    (star H (borel H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (MulAction.stabilizer A5 i) := by
  obtain ⟨⟨P,hP⟩, _, hB⟩ := actor_sylow_marks S hS e
  obtain ⟨i,hi⟩ := alternating_model_borel P
  refine ⟨i, ?_⟩
  rw [hB, ← hP]
  exact hi

/-- The actual symmetric Borel fixes the point selected by the component Sylow. -/
theorem symmetric_borel_image
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × S5) : ∃ i : Fin 5,
    (star H (borel H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (A5 ⊓ MulAction.stabilizer S5 i) := by
  obtain ⟨⟨P,hP⟩, _, hB⟩ := actor_sylow_marks S hS e
  obtain ⟨i,hi⟩ := symmetric_model_borel P
  refine ⟨i, ?_⟩
  rw [hB, ← hP]
  exact hi

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements
