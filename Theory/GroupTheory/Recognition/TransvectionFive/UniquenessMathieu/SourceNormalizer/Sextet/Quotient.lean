module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Transport
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Kernel
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.PointStabilizer

/-!
# The 45-point normalizer quotient and its six-point action

The fused orbit has 45 points and its stabilizer contains 48 distinct marked
centralizer transformations. Thus the actual quotient has order at least 2160.
The faithful exceptional-coordinate representation embeds it in a group whose
six-point kernel has order at most three and image has order at most 6!.
Equality follows throughout: the coordinate representation is onto, and the
literal six-point action has order-three kernel and full symmetric image.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4–40.5, pp.218–219.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code)
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

private theorem card_range_mul_ker {A B : Type*} [Group A] [Group B] (f : A →* B) :
    Nat.card f.range * Nat.card f.ker = Nat.card A := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact (card_eq_card_quotient_mul_card_subgroup f.ker).symm

private theorem perm_six_card : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

private theorem symmetry_card_le : Nat.card Sextet.symmetryGroup ≤ 2160 := by
  have hr := Nat.card_le_card_of_injective (fun x : Sextet.action.range => x.val) Subtype.val_injective
  rw [perm_six_card] at hr
  have hm := card_range_mul_ker Sextet.action
  have hk := Sextet.kernel_card_le
  calc
    Nat.card Sextet.symmetryGroup = Nat.card Sextet.action.range * Nat.card Sextet.action.ker := hm.symm
    _ ≤ 720 * 3 := Nat.mul_le_mul hr hk
    _ = 2160 := rfl

private theorem plane_quotient_card_ge (hcount : (F.fusion F.plane).ncard = 45) :
    2160 ≤ Nat.card (planeQuotient F) := by
  classical
  let Q := planeQuotient F
  let : MulAction Q Code := MulAction.compHom Code (quotientCodeAction F)
  have horbit : MulAction.orbit Q (4 : Code) = {x | Sextet.fused x = true} := by
    ext x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨q, rfl⟩
      apply (plane_fusion_iff_fused F hcount _).mp
      induction q using QuotientGroup.induction_on with
      | H n =>
        change IsConj z (element F (quotientCodeAction F (QuotientGroup.mk n) 4))
        rw [quotientCodeAction_mk, normalizerAction_element, element_point]
        exact isConj_iff.mpr ⟨n, rfl⟩
    · intro hx
      obtain ⟨n, hn, he⟩ := source_plane_fusion F (point_mem_plane F) (element_mem F x)
        ((plane_fusion_iff_fused F hcount x).mpr hx)
      refine ⟨QuotientGroup.mk (⟨n, hn⟩ : planeNormalizer F), ?_⟩
      change quotientCodeAction F (QuotientGroup.mk (⟨n, hn⟩ : planeNormalizer F)) 4 = x
      apply element_injective F
      rw [quotientCodeAction_mk, normalizerAction_element, element_point]
      exact he
  have hcOrbit : Nat.card (MulAction.orbit Q (4 : Code)) = 45 := by
    rw [horbit, Nat.card_eq_fintype_card]
    decide
  have hlift (i : Fin 48) : ∃ q : MulAction.stabilizer Q (4 : Code),
      quotientCodeAction F q.val = Sextet.pointSymmetry i := by
    obtain ⟨n, hn⟩ := exists_point_code_action F (Sextet.pointSymmetry i)
      (Sextet.pointSymmetry_rankOne i) (Sextet.pointSymmetry_point i)
    let q : Q := QuotientGroup.mk (⟨n, n.property.2⟩ : planeNormalizer F)
    have he : quotientCodeAction F q = Sextet.pointSymmetry i := by
      rw [quotientCodeAction_mk, ← pointCodeAction_apply, hn]
    refine ⟨⟨q, ?_⟩, he⟩
    change quotientCodeAction F q 4 = 4
    rw [he, Sextet.pointSymmetry_point]
  let lift : Fin 48 → MulAction.stabilizer Q (4 : Code) := fun i => (hlift i).choose
  have hli : Function.Injective lift := by
    intro i j hij
    apply Sextet.pointSymmetry_injective
    exact (hlift i).choose_spec.symm.trans
      ((congrArg (fun q : MulAction.stabilizer Q (4 : Code) => quotientCodeAction F q.val) hij).trans
        (hlift j).choose_spec)
  have hcStab : 48 ≤ Nat.card (MulAction.stabilizer Q (4 : Code)) := by
    simpa using Nat.card_le_card_of_injective lift hli
  have hm := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Q (4 : Code))
  rw [Nat.card_prod, hcOrbit] at hm
  change 2160 ≤ Nat.card Q
  rw [← hm]
  exact Nat.mul_le_mul_left 45 hcStab

/-- The 45-point rectangle has the source quotient order 3·6!. -/
theorem planeSextet_quotient_card (hcount : (F.fusion F.plane).ncard = 45) :
    Nat.card (planeQuotient F) = 2160 := by
  apply Nat.le_antisymm
  · exact (Nat.card_le_card_of_injective (planeSextetRepresentation F hcount)
      (planeSextetRepresentation_injective F hcount)).trans symmetry_card_le
  · exact plane_quotient_card_ge F hcount

/-- Every additive symmetry of the exceptional four-groups is induced by
the actual ambient normalizer quotient. -/
theorem planeSextetRepresentation_surjective (hcount : (F.fusion F.plane).ncard = 45) :
    Function.Surjective (planeSextetRepresentation F hcount) := by
  apply ((planeSextetRepresentation_injective F hcount).bijective_of_nat_card_le ?_).2
  rw [planeSextet_quotient_card F hcount]
  exact symmetry_card_le

/-- The order-three kernel and full symmetric image concern the literal
action on the six actual four-subgroups. -/
theorem planeSextetAction_structure (hcount : (F.fusion F.plane).ncard = 45) :
    Nat.card (planeSextetAction F hcount).ker = 3 ∧
      Function.Surjective (planeSextetAction F hcount) := by
  let f := planeSextetAction F hcount
  let lift : f.ker → Sextet.action.ker := fun q =>
    ⟨planeSextetRepresentation F hcount q.val, by
      change Sextet.action (planeSextetRepresentation F hcount q.val) = 1
      rw [← planeSextetAction_apply]
      exact q.property⟩
  have hi : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    exact planeSextetRepresentation_injective F hcount (congrArg Subtype.val hab)
  have hk : Nat.card f.ker ≤ 3 := (Nat.card_le_card_of_injective lift hi).trans Sextet.kernel_card_le
  have hr : Nat.card f.range ≤ 720 := by
    simpa only [perm_six_card] using
      Nat.card_le_card_of_injective (fun x : f.range => x.val) Subtype.val_injective
  have hm := card_range_mul_ker f
  rw [planeSextet_quotient_card F hcount] at hm
  have hk3 : Nat.card f.ker = 3 := by nlinarith
  have hr720 : Nat.card f.range = 720 := by rw [hk3] at hm; omega
  refine ⟨hk3, MonoidHom.range_eq_top.mp ?_⟩
  exact f.range.eq_top_of_card_eq (hr720.trans perm_six_card.symm)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
