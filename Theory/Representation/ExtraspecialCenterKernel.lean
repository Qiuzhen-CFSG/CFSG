module
public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.Representation.NormalInvariants

/-!
# Irreducible actions detecting an extraspecial center

If a normal extraspecial subgroup contains its ambient centralizer, an
irreducible representation which detects its center is faithful on the
whole group. Normality makes the central fixed space invariant; its
vanishing makes the extraspecial restriction faithful. The remaining
kernel centralizes the extraspecial subgroup, so is trivial as well.

This retains the whole acting group, as needed for the chief factors in
Aschbacher–Smith 14.7.20(2), printed p.1049.
-/

public noncomputable section
open Subgroup Representation
namespace Representation
variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Detecting the center of a self-centralizing normal extraspecial group
makes an irreducible binary representation faithful on the entire overgroup. -/
theorem faithful_of_extraspecial_center_not_le_kernel
    (σ : Representation (ZMod 2) D W) [σ.IsIrreducible]
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hcentral : centralizer (P : Set D) ≤ P)
    (hne : ¬ (center P).map P.subtype ≤ σ.ker) :
    Function.Injective σ ∧
      invariants ((σ.comp P.subtype).comp (center P).subtype) = ⊥ := by
  let Z := (center P).map P.subtype
  let : Z.Normal := inferInstance
  have hfix : invariants (σ.comp Z.subtype) = ⊥ := by
    by_contra hz
    exact hne (le_ker_of_normal_invariants_ne_bot σ Z hz)
  have hPn : ¬ center P ≤ (σ.comp P.subtype).ker := by
    intro hc
    apply hne
    rintro _ ⟨z,hz,rfl⟩
    exact hc hz
  have hfP : Function.Injective (σ.comp P.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 3) _ hPn)
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hc : x ∈ centralizer (P : Set D) := by
      intro p hp
      have he : (⟨x*p*x⁻¹,(inferInstance : P.Normal).conj_mem p hp x⟩ : P) = ⟨p,hp⟩ := by
        apply hfP
        change σ (x*p*x⁻¹) = σ p
        rw [map_mul,map_mul,hx,show σ x⁻¹ = 1 from σ.ker.inv_mem hx,one_mul,mul_one]
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
    have he : (⟨x,hcentral hc⟩ : P) = 1 := hfP (hx.trans (map_one _).symm)
    exact congrArg Subtype.val he
  · apply bot_unique
    intro w hw
    have hw' : w ∈ invariants (σ.comp Z.subtype) := by
      rintro ⟨z,hz⟩
      obtain ⟨a,ha,rfl⟩ := hz
      exact hw ⟨a,ha⟩
    simpa only [hfix,Submodule.mem_bot] using hw'

end Representation
