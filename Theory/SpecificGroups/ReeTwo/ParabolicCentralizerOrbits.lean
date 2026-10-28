module

public import Theory.SpecificGroups.ReeTwo.CoreParabolicOrbits
public import Theory.SpecificGroups.ReeTwo.Centralizer

/-!
# Centralizers and involution fusion in the concrete Ree local group

Inside the semidirect product `Centralizer`, the chosen cyclic-five subgroup
has cyclic order-four centralizer in the embedded core. The explicit core
orbit witnesses give conjugacy of all core involutions outside the derived
centralizer, and the first root supplies such an involution.

The proofs transport the kernel-checked coordinate identities through the
actual semidirect-product inclusions. These assertions concern this local
model; they do not assume its identification with a parabolic in an ambient
Ree group, or identify the core with its intrinsic two-core without proof.

Source: Aschbacher (1982), *The Tits group as a standard subgroup*,
Section 3, (3.2.7) and (3.2.11), using the verified root model from
Shinoda (1975), (2.3), pp.81–83.
-/

@[expose] public section
namespace ReeTwo.Centralizer

/-- The specified order-five element of the complement. -/
def fiveGenerator : Centralizer :=
  SemidirectProduct.inr (Core.complementA ^ 2 * Core.complementR)

/-- The specified complement element has exact order five. -/
theorem fiveGenerator_order : orderOf fiveGenerator = 5 := by
  rw [fiveGenerator, orderOf_injective _ SemidirectProduct.inr_injective,
    ← Subgroup.orderOf_coe]
  exact Core.orderOf_c

/-- Core involutions outside the derived centralizer are conjugate in the concrete local model. -/
theorem isConj_root_zero_of_involution (x : Core) (hx : x ^ 2 = 1)
    (hf : x ∉ Subgroup.centralizer (commutator Core : Set Core)) :
    IsConj (root 0) (SemidirectProduct.inl x : Centralizer) := by
  obtain ⟨h,k,_,hk⟩ := Core.involution_eq_conjugate_five_root x hx hf
  have hc := (SemidirectProduct.inl_aut (φ := Core.complement.subtype)
    ((Core.complementA ^ 2 * Core.complementR) ^ k.val) (Core.root 0)).symm
  have he : fiveGenerator ^ k.val * root 0 * (fiveGenerator ^ k.val)⁻¹ =
      SemidirectProduct.inl ((Core.c ^ k.val) (Core.root 0)) := by
    have hv : Core.complement.subtype ((Core.complementA ^ 2 * Core.complementR) ^ k.val) =
        Core.c ^ k.val := by
      rw [map_pow, map_mul, map_pow]
      rfl
    rw [hv] at hc
    simpa only [fiveGenerator, root, ← map_pow, ← map_inv] using hc
  apply isConj_iff.mpr
  refine ⟨SemidirectProduct.inl h * fiveGenerator ^ k.val, ?_⟩
  calc
    (SemidirectProduct.inl h * fiveGenerator ^ k.val) * root 0 *
        (SemidirectProduct.inl h * fiveGenerator ^ k.val)⁻¹ =
        SemidirectProduct.inl h * (fiveGenerator ^ k.val * root 0 *
          (fiveGenerator ^ k.val)⁻¹) * (SemidirectProduct.inl h)⁻¹ := by group
    _ = SemidirectProduct.inl x := by rw [he, ← map_inv, ← map_mul, ← map_mul, hk]

/-- The orbit in the previous theorem is nonempty. -/
theorem exists_core_involution_outside_derived_centralizer :
    ∃ x : Core, orderOf x = 2 ∧
      x ∉ Subgroup.centralizer (commutator Core : Set Core) := by
  refine ⟨Core.root 0, ?_, ?_⟩
  · exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  · rw [Core.mem_centralizer_derived_iff]
    decide +kernel

/-- Any two core involutions outside the derived centralizer are locally conjugate. -/
theorem core_involutions_isConj (x y : Core) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hfx : x ∉ Subgroup.centralizer (commutator Core : Set Core))
    (hfy : y ∉ Subgroup.centralizer (commutator Core : Set Core)) :
    IsConj (SemidirectProduct.inl x : Centralizer) (SemidirectProduct.inl y) :=
  (isConj_root_zero_of_involution x hx hfx).symm.trans
    (isConj_root_zero_of_involution y hy hfy)

set_option maxRecDepth 4096 in
/-- The centralizer in the embedded core of the chosen five-subgroup is cyclic of order four. -/
theorem centralizer_five_comap :
    (Subgroup.centralizer (Subgroup.zpowers fiveGenerator : Set Centralizer)).comap
      (SemidirectProduct.inl : Core →* Centralizer) = Subgroup.zpowers (Core.root 2) := by
  ext x
  change (SemidirectProduct.inl x : Centralizer) ∈
    Subgroup.centralizer (Subgroup.zpowers fiveGenerator : Set Centralizer) ↔ _
  rw [← Core.fixed_c_iff_mem_zpowers]
  have he : fiveGenerator * SemidirectProduct.inl x * fiveGenerator⁻¹ =
      SemidirectProduct.inl (Core.c x) :=
    (SemidirectProduct.inl_aut (φ := Core.complement.subtype)
      (Core.complementA ^ 2 * Core.complementR) x).symm
  constructor
  · intro hx
    have hh := Subgroup.mem_centralizer_iff.mp hx fiveGenerator (Subgroup.mem_zpowers _)
    apply SemidirectProduct.inl_injective (φ := Core.complement.subtype)
    rw [← he, hh, mul_inv_cancel_right]
  · intro hx
    have hc : Commute fiveGenerator (SemidirectProduct.inl x : Centralizer) :=
      mul_inv_eq_iff_eq_mul.mp (he.trans (congrArg SemidirectProduct.inl hx))
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨k,rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hc.zpow_left k).eq


/-- The fixed subgroup in the core has order four. -/
theorem centralizer_five_core_card :
    Nat.card ((Subgroup.centralizer (Subgroup.zpowers fiveGenerator : Set Centralizer)).comap
      (SemidirectProduct.inl : Core →* Centralizer)) = 4 := by
  rw [centralizer_five_comap, Nat.card_zpowers, Core.root_two_order]

/-- The fixed subgroup in the core is cyclic. -/
theorem centralizer_five_core_cyclic :
    IsCyclic ((Subgroup.centralizer (Subgroup.zpowers fiveGenerator : Set Centralizer)).comap
      (SemidirectProduct.inl : Core →* Centralizer)) := by
  rw [centralizer_five_comap]
  infer_instance

end ReeTwo.Centralizer
