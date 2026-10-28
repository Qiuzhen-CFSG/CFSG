module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Bounds and restriction for the fixed-space parameter

Emptiness of the next fixed-space family characterizes an upper bound on `a`.
An actor embedding transports every subgroup and preserves its relative index;
an intertwining linear equivalence transports the corresponding fixed spaces.
Thus restriction cannot increase `a`. This is the implication used to pass
from the M₂₄ modules to the M₂₃ modules in E.4.3(3); constructing the concrete
modules and their intertwining maps is a separate obligation.

The hyperplane witness at the end is the form used by the solvable applications
in §15.3. No faithfulness or finite-dimensionality is needed for transport.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.3.8–9,
E.4.1–3, printed pp. 232, 240–242.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- A finite numerical bound is equivalent to emptiness of the next fixed-space family. -/
theorem moduleA_le_iff_next_family_empty (ρ : Representation (ZMod 2) G V) (k : ℕ) :
    moduleA ρ ≤ (k : ℕ∞) ↔ fixedSpaceFamily ρ (k + 1) = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro A hA
    have hle := (le_moduleA_of_mem ρ hA).trans h
    have := ENat.natCast_le_natCast.mp hle
    omega
  · intro h
    apply iSup_le
    intro j
    apply iSup_le
    rintro ⟨A, hA⟩
    apply ENat.natCast_le_natCast.mpr
    by_contra hj
    have hm := fixedSpaceFamily_mono ρ (by omega : 0 < k + 1)
      (by omega : k + 1 ≤ j) hA
    rw [h] at hm
    exact hm

/-- An embedding of actors and an intertwining linear equivalence preserve the fixed-space family. Subgroups of the image lift with the same relative index. -/
theorem fixedSpaceFamily_map_of_equivariant
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (f : G →* D) (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {k : ℕ} {A : Subgroup G} (hA : A ∈ fixedSpaceFamily ρ k) :
    A.map f ∈ fixedSpaceFamily σ k := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2.1.2
  refine ⟨hA.1, ⟨?_, IsElementaryAbelian.map f⟩, ?_⟩
  · intro hb
    apply hA.2.1.1
    apply Subgroup.map_injective hf
    simpa only [Subgroup.map_bot] using hb
  · intro B hBA hB
    let C := B.comap f
    have hCA : C ≤ A := by
      have h := Subgroup.comap_mono (f := f) hBA
      simpa only [Subgroup.comap_map_eq_self_of_injective hf] using h
    have hCmap : C.map f = B :=
      Subgroup.map_comap_eq_self (hBA.trans (Subgroup.map_le_range f A))
    have heq := hA.2.2 C hCA (by
      simpa only [C, Subgroup.relIndex_comap] using hB)
    calc
      fixedSpace σ (A.map f) = (fixedSpace ρ A).map E.toLinearMap :=
        (fixedSpace_map_equivariant ρ σ f E hE A).symm
      _ = (fixedSpace ρ C).map E.toLinearMap := congrArg _ heq
      _ = fixedSpace σ (C.map f) := fixedSpace_map_equivariant ρ σ f E hE C
      _ = fixedSpace σ B := congrArg _ hCmap

/-- Restriction along an embedding cannot increase the parameter, including an actual equivariant change of module coordinates. -/
theorem moduleA_le_of_equivariant_injective
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (f : G →* D) (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v)) : moduleA ρ ≤ moduleA σ := by
  apply iSup_le
  intro k
  apply iSup_le
  rintro ⟨A, hA⟩
  exact le_moduleA_of_mem σ (fixedSpaceFamily_map_of_equivariant ρ σ f hf E hE hA)

/-- The parameter of a restricted representation is bounded by that of the original representation. -/
theorem moduleA_comp_le (σ : Representation (ZMod 2) D W)
    (f : G →* D) (hf : Function.Injective f) : moduleA (σ.comp f) ≤ moduleA σ :=
  moduleA_le_of_equivariant_injective (σ.comp f) σ f hf
    (LinearEquiv.refl (ZMod 2) W) (fun _ _ => rfl)

/-- The parameter is invariant under actual group and module isomorphisms. -/
theorem moduleA_eq_of_equivariant_equiv
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (e : G ≃* D) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (e g) (E v)) : moduleA ρ = moduleA σ := by
  apply le_antisymm (moduleA_le_of_equivariant_injective ρ σ e.toMonoidHom e.injective E hE)
  apply moduleA_le_of_equivariant_injective σ ρ e.symm.toMonoidHom e.symm.injective E.symm
  intro d w
  apply E.injective
  simp only [E.apply_symm_apply]
  change σ d w = E (ρ (e.symm d) (E.symm w))
  simpa only [E.apply_symm_apply, e.apply_symm_apply] using (hE (e.symm d) (E.symm w)).symm

/-- If a ≤ 1, every nontrivial elementary abelian two-subgroup has a hyperplane with a strictly larger fixed space. This is the form consumed in §15.3. -/
theorem exists_hyperplane_fixedSpace_lt_of_moduleA_le_one [Finite G]
    (ρ : Representation (ZMod 2) G V) (ha : moduleA ρ ≤ 1)
    {A : Subgroup G} (hA : IsElementaryTwo A) :
    ∃ B ≤ A, Nat.log 2 (B.relIndex A) = 1 ∧ fixedSpace ρ A < fixedSpace ρ B := by
  have hnot : A ∉ fixedSpaceFamily ρ 2 := by
    rw [(moduleA_le_iff_next_family_empty ρ 1).mp ha]
    exact Set.notMem_empty _
  have hex : ∃ B ≤ A, Nat.log 2 (B.relIndex A) < 2 ∧ fixedSpace ρ A ≠ fixedSpace ρ B := by
    by_contra! hh
    exact hnot ⟨by decide, hA, hh⟩
  obtain ⟨B, hBA, hB, hne⟩ := hex
  refine ⟨B, hBA, ?_, lt_of_le_of_ne (fixedSpace_antitone ρ hBA) hne⟩
  have hzero : Nat.log 2 (B.relIndex A) ≠ 0 := by
    intro hz
    exact hne (((mem_fixedSpaceFamily_one_iff ρ A).mpr hA).2.2 B hBA (by omega))
  omega
end CFSG.Quasithin.ChapterE
