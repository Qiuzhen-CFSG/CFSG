module

public import Theory.SpecificGroups.Suzuki.FieldTorus
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The literal Suzuki Borel quotient and its coefficient action

The root group and split torus are complementary in the standard Borel.
The explicit torus parameter identifies the quotient by the root group with
the defining field's units. Entrywise field automorphisms induce exactly
their unit action on this quotient; conjugation by Borel elements disappears
because the quotient is abelian.

Source: Huppert–Blackburn III, XI.3.1 and XI.3.3. The application is the
Cartan field-action argument in Aschbacher–Smith F.1.3(5), printed p.260.
-/

public section
noncomputable section
namespace BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient
open Subgroup PFAppendixIII

private theorem root_le (m : ℕ) : SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m := by
  rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_left

private theorem torus_le (m : ℕ) : SuzukiSplitTorus m ≤ SuzukiBorelSubgroup m := by
  rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_right

private def torusHom (m : ℕ) :
    (BinaryGaloisField (2 * m + 1))ˣ →* SuzukiSplitTorus m where
  toFun u := ⟨splitTorusElement m u, splitTorusElement_mem m u⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact External.suzukiTorusGL_one m
  map_mul' u v := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitTorusElement, SuzukiTorusGL, SuzukiTorusMatrix, Matrix.mul_apply,
        Fin.sum_univ_four, mul_pow, mul_comm]

private theorem torusHom_bijective (m : ℕ) : Function.Bijective (torusHom m) := by
  constructor
  · intro u v h
    apply Units.ext
    apply (iterateFrobenius_inj (BinaryGaloisField (2 * m + 1)) 2 m)
    have he := congrArg (fun t : SuzukiSplitTorus m => t.val.val (1 : Fin 4) (1 : Fin 4)) h
    simpa [torusHom, splitTorusElement, SuzukiTorusGL, SuzukiTorusMatrix,
      iterateFrobenius_def] using he
  · intro t
    obtain ⟨u, hu⟩ := (mem_suzukiSplitTorus_iff m t).mp t.property
    exact ⟨u, Subtype.ext (Subtype.ext hu.symm)⟩

private def torusEquiv (m : ℕ) :
    (BinaryGaloisField (2 * m + 1))ˣ ≃* SuzukiSplitTorus m :=
  MulEquiv.ofBijective (torusHom m) (torusHom_bijective m)

private instance root_normal (m : ℕ) :
    ((SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m)).Normal :=
  suzukiRootSubgroup_normal_in_borel m

private theorem root_complement (m : ℕ) (hm : 0 < m) :
    ((SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m)).IsComplement'
      ((SuzukiSplitTorus m).subgroupOf (SuzukiBorelSubgroup m)) := by
  apply isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_congr (subgroupOfEquivOfLe (root_le m)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (torus_le m)).toEquiv,
      suzukiRootSubgroup_card m hm, suzukiSplitTorus_card m hm,
      suzukiBorelSubgroup_card m hm]
  · apply disjoint_iff_inf_le.mpr
    intro x hx
    apply Subtype.ext
    exact disjoint_iff_inf_le.mp (suzukiRootSubgroup_disjoint_splitTorus m hm) hx

private def quotientEquiv (m : ℕ) (hm : 0 < m) :
    SuzukiBorelSubgroup m ⧸ (SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m) ≃*
      (BinaryGaloisField (2 * m + 1))ˣ :=
  (root_complement m hm).symm.QuotientMulEquiv.trans
    ((subgroupOfEquivOfLe (torus_le m)).trans (torusEquiv m).symm)

/-- The actual quotient by the standard root group, in explicit torus coordinates. -/
def projection (m : ℕ) (hm : 0 < m) :
    SuzukiBorelSubgroup m →* (BinaryGaloisField (2 * m + 1))ˣ :=
  (quotientEquiv m hm).toMonoidHom.comp
    (QuotientGroup.mk' ((SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m)))

theorem projection_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (projection m hm) :=
  (quotientEquiv m hm).surjective.comp (QuotientGroup.mk'_surjective _)

theorem projection_eq_one_iff (m : ℕ) (hm : 0 < m) (x : SuzukiBorelSubgroup m) :
    projection m hm x = 1 ↔ (x : SuzukiMatrixGroup m) ∈ SuzukiRootSubgroup m := by
  change quotientEquiv m hm (QuotientGroup.mk' _ x) = 1 ↔ _
  rw [map_eq_one_iff _ (quotientEquiv m hm).injective, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  rfl

theorem projection_ker (m : ℕ) (hm : 0 < m) :
    (projection m hm).ker = (SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m) := by
  ext x
  exact projection_eq_one_iff m hm x

private theorem projection_torus (m : ℕ) (hm : 0 < m)
    (u : (BinaryGaloisField (2 * m + 1))ˣ) :
    projection m hm ⟨splitTorusElement m u, torus_le m (splitTorusElement_mem m u)⟩ = u := by
  let t : (SuzukiSplitTorus m).subgroupOf (SuzukiBorelSubgroup m) :=
    ⟨⟨splitTorusElement m u, torus_le m (splitTorusElement_mem m u)⟩,
      splitTorusElement_mem m u⟩
  change (torusEquiv m).symm
    (subgroupOfEquivOfLe (torus_le m)
      ((root_complement m hm).symm.QuotientMulEquiv
        (QuotientGroup.mk' _ (t : SuzukiBorelSubgroup m)))) = u
  rw [quotientMulEquiv_mk_apply_of_isComplement']
  exact (torusEquiv m).symm_apply_apply u

private theorem field_root_mem (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (x : SuzukiMatrixGroup m) (hx : x ∈ SuzukiRootSubgroup m) :
    suzukiFieldAut m σ x ∈ SuzukiRootSubgroup m := by
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m x).mp hx
  apply (mem_suzukiRootSubgroup_iff m _).mpr
  refine ⟨σ a, σ b, ?_⟩
  ext i j
  rw [suzukiFieldAut_apply_entry, hab]
  fin_cases i <;> fin_cases j <;> simp [SuzukiRootGL, SuzukiRootMatrix]

theorem field_map_root (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) :
    (SuzukiRootSubgroup m).map (suzukiFieldAut m σ).toMonoidHom = SuzukiRootSubgroup m := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact field_root_mem m σ x hx
  · exact (Subgroup.card_map_of_injective (suzukiFieldAut m σ).injective).ge

private theorem field_map_torus (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) :
    (SuzukiSplitTorus m).map (suzukiFieldAut m σ).toMonoidHom = SuzukiSplitTorus m := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ := (mem_suzukiSplitTorus_iff m x).mp hx
    have hx' : x = splitTorusElement m u := Subtype.ext hu
    change suzukiFieldAut m σ x ∈ SuzukiSplitTorus m
    rw [hx', field_splitTorusElement]
    exact splitTorusElement_mem _ _
  · exact (Subgroup.card_map_of_injective (suzukiFieldAut m σ).injective).ge

private theorem field_map_borel (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) :
    (SuzukiBorelSubgroup m).map (suzukiFieldAut m σ).toMonoidHom = SuzukiBorelSubgroup m := by
  rw [suzukiBorelSubgroup_eq_sup, Subgroup.map_sup, field_map_root, field_map_torus]

private def fieldBorel (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) :
    MulAut (SuzukiBorelSubgroup m) :=
  ((suzukiFieldAut m σ).subgroupMap (SuzukiBorelSubgroup m)).trans
    (MulEquiv.subgroupCongr (field_map_borel m σ))

private theorem projection_field (m : ℕ) (hm : 0 < m)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (x : SuzukiBorelSubgroup m) :
    projection m hm (fieldBorel m σ x) =
      Units.map σ.toRingEquiv.toMonoidHom (projection m hm x) := by
  obtain ⟨⟨k, t⟩, he⟩ := (root_complement m hm).2 x
  change (k : SuzukiBorelSubgroup m) * t = x at he
  rw [← he, map_mul, map_mul, map_mul, map_mul]
  have hk : projection m hm (k : SuzukiBorelSubgroup m) = 1 :=
    (projection_eq_one_iff m hm _).mpr k.property
  have hfk : projection m hm (fieldBorel m σ (k : SuzukiBorelSubgroup m)) = 1 :=
    (projection_eq_one_iff m hm _).mpr (field_root_mem m σ _ k.property)
  obtain ⟨u, hu⟩ := (mem_suzukiSplitTorus_iff m (t : SuzukiBorelSubgroup m)).mp t.property
  have ht : (t : SuzukiBorelSubgroup m) =
      ⟨splitTorusElement m u, torus_le m (splitTorusElement_mem m u)⟩ :=
    Subtype.ext (Subtype.ext hu)
  rw [hk, hfk, map_one, one_mul, one_mul, ht, projection_torus]
  have hf : fieldBorel m σ
      ⟨splitTorusElement m u, torus_le m (splitTorusElement_mem m u)⟩ =
      ⟨splitTorusElement m (Units.map σ.toRingHom u),
        torus_le m (splitTorusElement_mem m _)⟩ :=
    Subtype.ext (field_splitTorusElement m σ u)
  rw [hf, projection_torus]
  rfl

/-- Restriction of the original inner–field actor to the actual Borel. -/
def borelActor (m : ℕ) (g : SuzukiBorelSubgroup m)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) :
    MulAut (SuzukiBorelSubgroup m) :=
  MulAut.conj g * fieldBorel m σ

theorem borelActor_apply (m : ℕ) (g : SuzukiBorelSubgroup m)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (x : SuzukiBorelSubgroup m) :
    (borelActor m g σ x : SuzukiMatrixGroup m) =
      (MulAut.conj (g : SuzukiMatrixGroup m) * suzukiFieldAut m σ) x := by
  change (g : SuzukiMatrixGroup m) * suzukiFieldAut m σ x * (g : SuzukiMatrixGroup m)⁻¹ = _
  rfl

theorem projection_borelActor (m : ℕ) (hm : 0 < m) (g : SuzukiBorelSubgroup m)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (x : SuzukiBorelSubgroup m) :
    projection m hm (borelActor m g σ x) =
      Units.map σ.toRingEquiv.toMonoidHom (projection m hm x) := by
  change projection m hm (g * fieldBorel m σ x * g⁻¹) = _
  rw [map_mul, map_mul, map_inv, mul_comm (projection m hm g), mul_assoc,
    mul_inv_cancel, mul_one, projection_field]

end BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient
