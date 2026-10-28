module

public import Theory.SpecificGroups.ReeTwo.CoreParabolicOmega

/-!
# The derived subgroup of the characteristic index-two Ree core

Five explicit commutators inside the first omega subgroup generate the
derived tail of the full core. Consequently the same elementary subgroup
is characteristic and self-centralizing inside the order-512 subgroup.
These are the intrinsic properties needed to handle the additional
supplement in the repaired full-Ree argument. The tail is also the first
omega subgroup of its order-64 centralizer, hence characteristic there.

The proof uses the verified root multiplication from Shinoda (1975), (2.3),
pp.81–82. No identification with an ambient Tits core is assumed.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace ReeTwo.Core

private def omegaPairLeft : Fin 5 → Core := ![
  root 0,
  ⟨0,1,1,0,0,0,0,0,0,0⟩,
  ⟨1,1,1,0,0,0,0,0,0,0⟩,
  ⟨0,0,1,1,0,0,0,0,0,0⟩,
  root 0]
private def omegaPairRight : Fin 5 → Core := ![
  ⟨0,1,1,0,0,0,0,0,0,0⟩,
  ⟨0,1,0,1,1,0,0,0,0,0⟩,
  ⟨1,1,0,1,0,0,0,0,0,0⟩,
  root 4, root 8]

private theorem omega_pair_mem (i : Fin 5) :
    omegaPairLeft i ∈ omega₁ Core (p := 2) ∧ omegaPairRight i ∈ omega₁ Core (p := 2) := by
  rw [← binaryCharacter_ker_eq_omega]
  exact (by decide +kernel : ∀ i : Fin 5,
    binaryCharacter (omegaPairLeft i) = 1 ∧ binaryCharacter (omegaPairRight i) = 1) i

private theorem omega_pair_commutator (i : Fin 5) :
    rightComm (omegaPairLeft i) (omegaPairRight i) = root (i.natAdd 5) := by
  exact (by decide +kernel : ∀ i : Fin 5,
    rightComm (omegaPairLeft i) (omegaPairRight i) = root (i.natAdd 5)) i

/-- The commutator subgroup of the omega subgroup, viewed inside the full core. -/
theorem omega_commutator : ⁅omega₁ Core (p := 2), omega₁ Core (p := 2)⁆ = commutator Core := by
  apply le_antisymm
  · exact commutator_mono le_top le_top
  · intro x hx
    have ht (i : Fin 5) : root (i.natAdd 5) ∈
        ⁅omega₁ Core (p := 2), omega₁ Core (p := 2)⁆ := by
      rw [← omega_pair_commutator]
      simpa only [rightComm, commutatorElement_def, inv_inv] using
        commutator_mem_commutator (inv_mem (omega_pair_mem i).1) (inv_mem (omega_pair_mem i).2)
    obtain ⟨h0,h1,h2,h3,h4⟩ := (mem_derived_iff x).mp hx
    have hn := normal_form x
    rw [h0,h1,h2,h3,h4] at hn
    simp only [ZMod.val_zero, pow_zero, one_mul] at hn
    exact hn ▸ mul_mem (mul_mem (mul_mem (mul_mem
      (pow_mem (ht 0) _) (pow_mem (ht 1) _))
      (pow_mem (ht 2) _)) (pow_mem (ht 3) _)) (pow_mem (ht 4) _)

/-- The intrinsic derived subgroup of the omega subgroup is exactly the tail. -/
theorem omega_derived_eq : commutator (omega₁ Core (p := 2)) =
    (commutator Core).subgroupOf (omega₁ Core (p := 2)) := by
  apply Subgroup.map_injective (omega₁ Core (p := 2)).subtype_injective
  rw [Subgroup.map_subtype_commutator, omega_commutator]
  exact (Subgroup.map_subgroupOf_eq_of_le derived_lt_omega.le).symm

/-- The tail is characteristic in the characteristic index-two subgroup. -/
theorem omega_derived_characteristic : ((commutator Core).subgroupOf (omega₁ Core (p := 2))).Characteristic := by
  rw [← omega_derived_eq]
  infer_instance

/-- The derived subgroup is self-centralizing in the omega subgroup. -/
theorem omega_centralizer_derived :
    centralizer ((commutator (omega₁ Core (p := 2))) : Set (omega₁ Core (p := 2))) =
      commutator (omega₁ Core (p := 2)) := by
  rw [omega_derived_eq]
  ext x
  constructor
  · intro hx
    have hF : (x : Core) ∈ centralizer (commutator Core : Set Core) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      have h := mem_centralizer_iff.mp hx ⟨y, derived_lt_omega.le hy⟩ hy
      exact congrArg Subtype.val h
    have hi : (x : Core) ∈ omega₁ Core (p := 2) ⊓ centralizer (commutator Core : Set Core) :=
      ⟨x.property,hF⟩
    rw [omega_inf_centralizer_derived] at hi
    exact hi
  · intro hx
    have hF : (x : Core) ∈ centralizer (commutator Core : Set Core) := by
      obtain ⟨h0,h1,_,h3,h4⟩ := (mem_derived_iff (x : Core)).mp hx
      exact (mem_centralizer_derived_iff _).mpr ⟨h0,h1,h3,h4⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    apply Subtype.ext
    exact mem_centralizer_iff.mp hF (y : Core) hy


/-- The omega subgroup of the order-64 centralizer maps to the derived tail. -/
theorem centralizer_omega_map_eq_derived :
    (omega₁ (centralizer (commutator Core : Set Core)) (p := 2)).map
      (centralizer (commutator Core : Set Core)).subtype = commutator Core := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    intro x hx
    have hs : (x : Core) ^ 2 = 1 := by
      have h : x ^ 2 = 1 := by simpa only [Set.mem_ofPred_eq, pow_one] using hx
      exact congrArg Subtype.val h
    obtain ⟨h0,h1,h3,h4⟩ := (mem_centralizer_derived_iff (x : Core)).mp x.property
    apply (mem_derived_iff (x : Core)).mpr
    refine ⟨h0,h1,?_,h3,h4⟩
    rw [pow_two] at hs
    have h := congrArg Core.b9 hs
    change (mul x x).b9 = 0 at h
    simp only [mul,h0,h1,h3,h4,mul_zero,zero_mul,add_zero] at h
    exact (by decide : ∀ a b : ZMod 2, b+a*a+b=0 → a=0) _ _ h
  · intro x hx
    have hF : x ∈ centralizer (commutator Core : Set Core) := by
      obtain ⟨h0,h1,_,h3,h4⟩ := (mem_derived_iff x).mp hx
      exact (mem_centralizer_derived_iff x).mpr ⟨h0,h1,h3,h4⟩
    refine ⟨⟨x,hF⟩,?_,rfl⟩
    apply Subgroup.subset_closure
    change (⟨x,hF⟩ : centralizer (commutator Core : Set Core)) ^ (2 ^ 1) = 1
    apply Subtype.ext
    change x ^ (2 ^ 1) = 1
    let : IsElementaryAbelian 2 (commutator Core) := derived_elementary
    simpa only [pow_one] using elemPow_eq_one_of_isElementaryAbelian x hx

/-- Intrinsically, the derived tail is the omega subgroup of its centralizer. -/
theorem centralizer_omega_eq_derived_subgroupOf :
    omega₁ (centralizer (commutator Core : Set Core)) (p := 2) =
      (commutator Core).subgroupOf (centralizer (commutator Core : Set Core)) := by
  apply Subgroup.map_injective (centralizer (commutator Core : Set Core)).subtype_injective
  rw [centralizer_omega_map_eq_derived]
  apply (Subgroup.map_subgroupOf_eq_of_le _).symm
  intro x hx
  obtain ⟨h0,h1,_,h3,h4⟩ := (mem_derived_iff x).mp hx
  exact (mem_centralizer_derived_iff x).mpr ⟨h0,h1,h3,h4⟩

/-- The tail is also characteristic in the order-64 centralizer candidate. -/
theorem derived_characteristic_in_centralizer :
    ((commutator Core).subgroupOf (centralizer (commutator Core : Set Core))).Characteristic := by
  rw [← centralizer_omega_eq_derived_subgroupOf]
  exact omega₁_characteristic _

end ReeTwo.Core
