module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.Supports.Models

/-!
# The precise fixed-kernel inputs for singleton supports

For a native S₃ factor, its natural quotient plane and a disjointness proof
lift the fixed-free cubic to the original moved space. The cubic displacement
map is then surjective, so the moved space is its own commutator and has
rank two. The hyperplane case uses its own fixed quotient, rather than the
global quotient used by the ordinary two-factor case.

These are conditional lifting lemmas. Offender generation must discharge the
stated fixed-kernel disjointness; the natural quotient clause alone does not.
The actual star-action applications are in the parent Supports module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3),(5), printed p.105, and 13.6.13, printed p.929.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) D V)

private theorem commutator_eq_of_fixed_free (U : Subrepresentation ρ) (A : Subgroup D)
    (r : A) (hr : ∀ u : U.toSubmodule, U.toRepresentation r u = u → u = 0) :
    subspaceCommutator ρ U.toSubmodule A = U.toSubmodule := by
  let f : U.toSubmodule →ₗ[ZMod 2] U.toSubmodule := U.toRepresentation r - LinearMap.id
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro u hu
    exact hr u (sub_eq_zero.mp hu)
  have hs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hi
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, _, u, hu, rfl⟩
    exact U.toSubmodule.sub_mem (U.apply_mem_toSubmodule a hu) hu
  · intro u hu
    obtain ⟨w, hw⟩ := hs ⟨u, hu⟩
    have he : ρ r (w : V) - (w : V) = u := congrArg Subtype.val hw
    rw [← he]
    exact Submodule.subset_span ⟨r, r.property, w, w.property, rfl⟩

/-- Once the original moved space is disjoint from the global fixed kernel,
the native factor quotient gives both rank two and the singleton support. -/
theorem factor_plane_of_disjoint {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) (e : A ≃* Equiv.Perm (Fin 3))
    (hd : Disjoint (moved ρ A) ρ.invariants) :
    subspaceCommutator ρ (moved ρ A) A = moved ρ A ∧
      Module.finrank (ZMod 2) (moved ρ A) = 2 := by
  obtain ⟨hm, hdim, r, _, hf⟩ := factor_quotient_plane ρ h e
  let f := ρ.invariants.mkQ.comp U.toSubmodule.subtype
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro u hu
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hd _ (hm ▸ u.property)
      ((Submodule.Quotient.mk_eq_zero _).mp hu)
  have hr (u : U.toSubmodule) (hu : U.toRepresentation r u = u) : u = 0 := by
    apply hi
    rw [map_zero]
    have he := hf ⟨ρ.invariants.mkQ u, ⟨u, u.property, rfl⟩⟩ (by
      apply Subtype.ext
      change ρ.invariants.mkQ (ρ r u) = ρ.invariants.mkQ u
      exact congrArg ρ.invariants.mkQ (congrArg Subtype.val hu))
    exact congrArg Subtype.val he
  constructor
  · simpa only [hm] using commutator_eq_of_fixed_free ρ U A r hr
  · have heq := (LinearEquiv.ofInjective f hi).finrank_eq
    have he : LinearMap.range f = ((fixed ρ).quotientImage U).toSubmodule := by
      change (ρ.invariants.mkQ.comp U.toSubmodule.subtype).range = _
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    rw [he] at heq
    exact (congrArg (fun W : Submodule (ZMod 2) V => Module.finrank (ZMod 2) W)
      hm.symm).trans (heq.trans hdim)

/-- The hyperplane calculation uses the second factor's own fixed kernel.
Its disjointness is the extra lifting input, not a conclusion of the quotient
natural-module clause alone. -/
theorem hyperplane_plane_of_disjoint {A : Subgroup D} {U : Subrepresentation ρ}
    (hm : U.toSubmodule = moved ρ A) (h : HyperplaneSecondCase ρ A U)
    (e : A ≃* Equiv.Perm (Fin 3)) (hd : Disjoint (moved ρ A) (fixedSpace ρ A)) :
    subspaceCommutator ρ (moved ρ A) A = moved ρ A ∧
      Module.finrank (ZMod 2) (moved ρ A) = 2 := by
  obtain ⟨hdim, r, _, hf⟩ := hyperplane_quotient_plane ρ h e
  let K := Representation.invariants (U.toRepresentation.comp A.subtype)
  have hK : K = ⊥ := by
    apply le_bot_iff.mp
    intro u hu
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hd _ (hm ▸ u.property)
      (fun a => congrArg Subtype.val (hu a))
  have hr (u : U.toSubmodule) (hu : U.toRepresentation r u = u) : u = 0 := by
    have hq : K.mkQ u = 0 := hf (K.mkQ u) (by
      change K.mkQ (U.toRepresentation r u) = K.mkQ u
      rw [hu])
    have hk : u ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hq
    simpa only [hK, Submodule.mem_bot] using hk
  constructor
  · simpa only [hm] using commutator_eq_of_fixed_free ρ U A r hr
  · have heq := Submodule.finrank_quotient_add_finrank K
    have hk : Module.finrank (ZMod 2) K = 0 := by rw [hK]; exact finrank_bot _ _
    rw [hk, add_zero] at heq
    exact (congrArg (fun W : Submodule (ZMod 2) V => Module.finrank (ZMod 2) W)
      hm.symm).trans (heq.symm.trans hdim)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
