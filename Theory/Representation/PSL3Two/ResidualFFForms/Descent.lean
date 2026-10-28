module

public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.EquivariantOffender

public import Theory.Representation.PSL3Two.ResidualFFForms.Criteria

/-!
# Descent of simple-module budgets through a two-group kernel

A normal two-subgroup kills every irreducible binary representation. Descending
through its actual quotient and transporting along the first isomorphism
therefore gives a representation of the specified image group on the original
vector space. Surjective inflation preserves irreducibility, duality and each
actor's fixed codimension.

Consequently the simple-constituent budget criterion transfers through any
surjection with two-group kernel. Only irreducible modules are descended;
the kernel may act nontrivially on nonsplit extensions.

This is the extension step for the constituent argument in
Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(1.4) and (3.8), printed pp.842 and 878.
-/

public section

set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender

namespace BinaryLinearThree.ResidualFFForms

universe u v w

variable {G : Type v} {Q : Type w} [Group G] [Group Q] [Finite G]
  {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The simple action descended to the prescribed image, on the same vector space. -/
noncomputable def irreducibleDescent (π : G →* Q) (hπ : Function.Surjective π)
    (hp : IsPGroup 2 π.ker) (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ] :
    Representation (ZMod 2) Q V :=
  (quotientOfLEKer ρ π.ker (normal_p_subgroup_le_ker ρ π.ker hp)).comp
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom

/-- Inflation along the prescribed map recovers the original action exactly. -/
theorem irreducibleDescent_comp (π : G →* Q) (hπ : Function.Surjective π)
    (hp : IsPGroup 2 π.ker) (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ] :
    (irreducibleDescent π hπ hp ρ).comp π = ρ := by
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have he (g : G) : e.symm (π g) = QuotientGroup.mk' π.ker g :=
    e.symm_apply_eq.mpr rfl
  ext g v
  change quotientOfLEKer ρ π.ker (normal_p_subgroup_le_ker ρ π.ker hp)
    (e.symm (π g)) v = ρ g v
  rw [he]
  rfl

/-- Descent preserves irreducibility. -/
theorem irreducibleDescent_irreducible (π : G →* Q) (hπ : Function.Surjective π)
    (hp : IsPGroup 2 π.ker) (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ] :
    IsIrreducible (irreducibleDescent π hπ hp ρ) := by
  apply (irreducible_comp_surjective_iff π hπ _).mp
  rw [irreducibleDescent_comp]
  infer_instance

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Contragredient duality commutes with pullback of the acting group. -/
theorem dual_comp (σ : Representation (ZMod 2) Q V) (π : G →* Q) :
    Representation.dual (σ.comp π) = σ.dual.comp π := by
  ext g f v
  change f (σ (π g⁻¹) v) = f (σ (π g)⁻¹ v)
  rw [map_inv]

/-- A two-group kernel does not change the simple-constituent budget criterion. -/
theorem simpleBudget_of_surjective (π : G →* Q) (hπ : Function.Surjective π)
    (hp : IsPGroup 2 π.ker) (A : Subgroup G) (d : ℕ)
    (hbudget : SimpleBudget.{u} (A.map π) d) : SimpleBudget.{u} A d := by
  intro W _ _ _ ρ hirr hnon hcost
  let : IsIrreducible ρ := hirr
  let σ := irreducibleDescent π hπ hp ρ
  have he : σ.comp π = ρ := irreducibleDescent_comp π hπ hp ρ
  have hd : σ.dual.comp π = ρ.dual := by rw [← dual_comp, he]
  have hc : fixedCodim σ (A.map π) = fixedCodim ρ A := by
    rw [← he]
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  have hcd : fixedCodim σ.dual (A.map π) = fixedCodim ρ.dual A := by
    rw [← hd]
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  have hn : σ ≠ 1 := by
    intro hs
    apply hnon
    rw [← he, hs]
    rfl
  obtain ⟨hself, hsum⟩ := hbudget W σ (irreducibleDescent_irreducible π hπ hp ρ)
    hn (by simpa only [hc] using hcost)
  refine ⟨?_, by simpa only [hc, hcd] using hsum⟩
  intro h
  apply hself
  obtain ⟨e⟩ := h
  have e' : Nonempty (Representation.Equiv (σ.comp π) (σ.dual.comp π)) := by
    rw [he, hd]
    exact ⟨e⟩
  exact ⟨inflationEquiv π hπ σ σ.dual e'.some⟩

end BinaryLinearThree.ResidualFFForms
