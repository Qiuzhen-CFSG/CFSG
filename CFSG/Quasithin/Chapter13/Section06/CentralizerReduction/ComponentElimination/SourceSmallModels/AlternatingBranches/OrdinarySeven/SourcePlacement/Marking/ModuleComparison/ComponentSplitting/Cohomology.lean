module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Summand
public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.Representation.FirstCohomologyDuality.Indecomposable
public import Mathlib.LinearAlgebra.Projection

/-!
# Splitting an ordinary seven-point natural section

The odd-degree natural A₇ module and its dual have vanishing first cohomology.
A central cover therefore has zero kernel. For a natural subrepresentation
with trivial quotient, the connecting cocycle shows that fixed vectors
supplement the subrepresentation. Choosing a complement inside the fixed
vectors gives an equivariant inclusion and retraction. A cyclic generator
bounds this fixed complement by one dimension.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.3(1),
printed p.84/PDF95, used in Lemma 13.6.22, printed p.932/PDF949.
-/

@[expose] public section

open Representation Representation.OneCohomology BinaryPermutation
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting
variable {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

abbrev naturalAction (e : H ≃* alternatingGroup (Fin 7)) :
    Representation (ZMod 2) H (natural (Fin 7)) :=
  (naturalRepresentation (Fin 7)).comp ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom)

omit [Finite H] in
private theorem natural_H1 (e : H ≃* alternatingGroup (Fin 7)) :
    Module.finrank (ZMod 2) (H1 (naturalAction e)) = 0 := by
  let E := H1Congr (naturalAction e) (alternatingNaturalRepresentation (Fin 7))
    e (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl)
  exact E.finrank_eq.trans alternatingSeven_natural_finrank_H1

omit [Finite H] in
private theorem natural_dual_H1 (e : H ≃* alternatingGroup (Fin 7)) :
    Module.finrank (ZMod 2) (H1 (naturalAction e).dual) = 0 := by
  let E := H1Congr (naturalAction e) (naturalAction e).dual
    (MulEquiv.refl _) (naturalDualEquiv (Fin 7))
    (fun g v => by
      have h := naturalDualEquiv_equivariant (Fin 7) (e g).val v
      apply LinearMap.ext
      intro w
      have hh := LinearMap.congr_fun h w
      change naturalDualEquiv (Fin 7) (naturalRepresentation (Fin 7) (e g).val v) w =
        naturalDualEquiv (Fin 7) v (naturalRepresentation (Fin 7) (e g⁻¹).val w)
      rw [map_inv]
      exact hh)
  exact E.finrank_eq.symm.trans (natural_H1 e)

/-- A central cover of the natural A₇ module has zero kernel. -/
theorem cover_injective (e : H ≃* alternatingGroup (Fin 7))
    (σ : Representation (ZMod 2) H V)
    (p : σ.IntertwiningMap (naturalAction e))
    (hp : IsCover p) : Function.Injective p := by
  have h := finrank_ker_le_H1_of_cover p hp
  rw [natural_dual_H1 e] at h
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero h))

private theorem split_of_equiv (e : H ≃* alternatingGroup (Fin 7))
    {ρ : Representation (ZMod 2) H V} (U : Subrepresentation ρ)
    (E : U.toSubmodule ≃ₗ[ZMod 2] natural (Fin 7))
    (hE : ∀ g u, E (U.toRepresentation g u) = naturalAction e g (E u))
    (hquot : HasTrivialQuotient U) :
    Nonempty (NaturalSummand ρ ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom)) := by
  have hEi (g : H) (u : natural (Fin 7)) :
      U.toRepresentation g (E.symm u) = E.symm (naturalAction e g u) := by
    apply E.injective
    rw [hE, E.apply_symm_apply, E.apply_symm_apply]
  have hH : Module.finrank (ZMod 2) (H1 U.toRepresentation) = 0 :=
    (H1Congr U.toRepresentation (naturalAction e) (MulEquiv.refl _) E hE).finrank_eq.trans
      (natural_H1 e)
  let : Subsingleton (H1 U.toRepresentation) := Module.finrank_zero_iff.mp hH
  have hsup : U.toSubmodule ⊔ fixed ρ = ⊤ := by
    apply top_unique
    intro w _
    exact (extensionClass_eq_zero_iff U hquot w).mp (Subsingleton.elim _ _)
  obtain ⟨C, hC, hcompl⟩ :=
    (show Codisjoint (fixed ρ) U.toSubmodule from
      codisjoint_iff.mpr (by simpa only [sup_comm] using hsup)).exists_isCompl
  let P := U.toSubmodule.projectionOnto C hcompl.symm
  have hPid (u : U) : P u = u := Submodule.projectionOnto_apply_left hcompl.symm u
  have hrem (w : V) : w - (P w : V) ∈ C := by
    rw [← Submodule.ker_projectionOnto hcompl.symm]
    change P (w - (P w : V)) = 0
    rw [map_sub, hPid, sub_self]
  have hPe (g : H) (w : V) : P (ρ g w) = U.toRepresentation g (P w) := by
    have hf := hC (hrem w) g
    have he : ρ g w = ρ g (P w) + (w - (P w : V)) := by
      rw [map_sub] at hf
      have he := sub_eq_iff_eq_add.mp hf
      simpa only [add_comm] using he
    rw [he, map_add]
    have hzero : P (w - (P w : V)) = 0 := by rw [map_sub, hPid, sub_self]
    rw [hzero, add_zero]
    exact hPid (U.toRepresentation g (P w))
  refine ⟨{
    inclusion := U.toSubmodule.subtype.comp E.symm.toLinearMap
    projection := E.toLinearMap.comp P
    retraction := ?_
    inclusion_equivariant := ?_
    projection_equivariant := ?_
    remainder_fixed := ?_ }⟩
  · intro w
    exact (congrArg E (hPid (E.symm w))).trans (E.apply_symm_apply w)
  · intro g w
    exact congrArg Subtype.val (hEi g w)
  · intro g w
    exact (congrArg E (hPe g w)).trans (hE g (P w))
  · intro g w
    change ρ g (w - (E.symm (E (P w)) : V)) = w - (E.symm (E (P w)) : V)
    rw [E.symm_apply_apply]
    exact hC (hrem w) g



/-- An embedded natural module containing all displacements has a fixed complement. -/
theorem split_of_injective (e : H ≃* alternatingGroup (Fin 7))
    {ρ : Representation (ZMod 2) H V}
    (i : natural (Fin 7) →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (he : ∀ g w, ρ g (i w) = i (naturalAction e g w))
    (hm : ∀ g w, ρ g w - w ∈ i.range) :
    Nonempty (NaturalSummand ρ ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom)) := by
  let U : Subrepresentation ρ :=
    { toSubmodule := i.range
      apply_mem_toSubmodule g := by
        rintro _ ⟨w, rfl⟩
        exact ⟨naturalAction e g w, (he g w).symm⟩ }
  let E : natural (Fin 7) ≃ₗ[ZMod 2] U.toSubmodule := LinearEquiv.ofInjective i hi
  have hE (g : H) (u : U) : E.symm (U.toRepresentation g u) =
      naturalAction e g (E.symm u) := by
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    change ρ g u.val = i (naturalAction e g (E.symm u))
    have hu : i (E.symm u) = u.val := congrArg Subtype.val (E.apply_symm_apply u)
    rw [← hu, he]
  exact split_of_equiv e U E.symm hE hm

omit [Finite H] [FiniteDimensional (ZMod 2) V] in
/-- A single orbit generator bounds the fixed complement by one dimension. -/
theorem seed_bound {ρ : Representation (ZMod 2) H V} {φ : H →* Equiv.Perm (Fin 7)}
    (d : NaturalSummand ρ φ) (z : V)
    (hz : Submodule.span (ZMod 2) (Set.range (fun g => ρ g z)) = ⊤) :
    Module.finrank (ZMod 2) d.projection.ker ≤ 1 := by
  let R : V →ₗ[ZMod 2] V := LinearMap.id - d.inclusion.comp d.projection
  have hR (g : H) (w : V) : R (ρ g w) = R w := by
    change ρ g w - d.inclusion (d.projection (ρ g w)) = w - d.inclusion (d.projection w)
    rw [d.projection_equivariant, ← d.inclusion_equivariant, ← map_sub]
    exact d.remainder_fixed g w
  have hm : (Submodule.span (ZMod 2) (Set.range (fun g => ρ g z))).map R ≤
      Submodule.span (ZMod 2) {R z} := by
    apply (Submodule.map_span_le R _ _).mpr
    rintro _ ⟨g, rfl⟩
    rw [hR]
    exact Submodule.subset_span (Set.mem_singleton _)
  have hk : d.projection.ker ≤ Submodule.span (ZMod 2) {R z} := by
    intro w hw
    have hwR : R w = w := by
      change w - d.inclusion (d.projection w) = w
      rw [show d.projection w = 0 from hw, map_zero, sub_zero]
    rw [← hwR]
    exact hm ⟨w, hz ▸ Submodule.mem_top, rfl⟩
  exact (Submodule.finrank_mono hk).trans (by
    simpa using
      (finrank_span_le_card ({R z} : Set V)))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting
end
