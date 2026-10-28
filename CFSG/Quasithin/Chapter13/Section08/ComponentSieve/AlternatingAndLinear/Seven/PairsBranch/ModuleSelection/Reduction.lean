module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Basic

/-!
# Selecting the natural alternative from the rank-two seed

The kernel of a component intertwiner restricted to the seed is L₁-invariant.
Irreducibility makes each projection either zero or injective. Thus a
four-dimensional identification produces an invariant plane, and an
identification with four plus its dual does so in at least one constituent.
The projections only commute with K, so the source's possible exchange of
constituents by H is retained. All markings use the same seven-point map.

This proves the representation deduction from the explicitly named
`FourPlaneExclusion`. The importing `ModuleSelection` assembly discharges that
premise using `ModuleSelection.FourSpace`, retaining the earlier universal
classification input.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed p.959/PDF p.976 (1 March 2004 manuscript).
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E) (φ : H →* Equiv.Perm (Fin 7))
  (ι : A7 →* H) (hι : ∀ a : A7, φ (ι a) = a)
  (L : Subgroup H) (hL : L ≤ ι.range)
  (S : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible S.toRepresentation]
  (hdim : Module.finrank (ZMod 2) S.toSubmodule = 2)
  (hP : pairStabilizer.comap φ ≤ subspaceStabilizer ρ S.toSubmodule)

include hL in
private theorem image_injective_or_zero {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) A7 F) (f : E →ₗ[ZMod 2] F)
    (hf : ∀ a v, f (ρ (ι a) v) = σ a (f v)) :
    Function.Injective (f.domRestrict S.toSubmodule) ∨ f.domRestrict S.toSubmodule = 0 := by
  let R : Subrepresentation S.toRepresentation := {
    toSubmodule := (f.domRestrict S.toSubmodule).ker
    apply_mem_toSubmodule l v hv := by
      obtain ⟨a, ha⟩ := hL l.property
      change f (ρ l v) = 0
      rw [← ha, hf]
      change f (v : E) = 0 at hv
      rw [hv, map_zero] }
  rcases eq_bot_or_eq_top R with hR | hR
  · left
    apply LinearMap.ker_eq_bot.mp
    exact congrArg Subrepresentation.toSubmodule hR
  · right
    ext v
    exact (show v ∈ R from hR.symm ▸ Submodule.mem_top)

include hι hL hdim hP in
private theorem no_nonzero_four_image (hfour : FourPlaneExclusion)
    {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (σ : Representation (ZMod 2) A7 F) (hσ : Function.Injective σ)
    (hF : Module.finrank (ZMod 2) F = 4) (f : E →ₗ[ZMod 2] F)
    (hf : ∀ a v, f (ρ (ι a) v) = σ a (f v))
    (hne : f.domRestrict S.toSubmodule ≠ 0) : False := by
  have hinj := (image_injective_or_zero ρ ι L hL S σ f hf).resolve_right hne
  apply hfour F σ hσ hF (S.toSubmodule.map f)
  · rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
    exact hdim
  · apply le_subspaceStabilizer
    rintro a ha _ ⟨v, hv, rfl⟩
    have hia : ι a ∈ pairStabilizer.comap φ := by
      change φ (ι a) ∈ pairStabilizer
      rw [hι]
      exact ha
    exact ⟨ρ (ι a) v, (hP hia v).mpr hv, hf a v⟩

private theorem dual_faithful {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F]
    (σ : Representation (ZMod 2) A7 F) (hσ : Function.Injective σ) :
    Function.Injective σ.dual := by
  intro a b hab
  apply inv_injective
  apply hσ
  apply (Module.dualMap_dualMap_eq_iff (ZMod 2) F).mp
  exact congrArg LinearMap.dualMap hab

include hι hL hdim hP

/-- A faithful four-space cannot contain the invariant rank-two seed once the
finite stabilizer calculation has been supplied. -/
theorem not_four_of_plane_exclusion (hfour : FourPlaneExclusion) : ¬ IsFour ρ ι := by
  rintro ⟨σ, hσ, ⟨e⟩⟩
  apply no_nonzero_four_image ρ φ ι hι L hL S hdim hP hfour σ hσ
    (Module.finrank_fin_fun (ZMod 2)) e.symm.toLinearMap e.symm.toIntertwiningMap.isIntertwining
  intro hz
  have hzero : ∀ v : S.toSubmodule, v = 0 := by
    intro v
    apply Subtype.ext
    apply e.symm.injective
    exact (DFunLike.congr_fun hz v).trans (map_zero e.symm).symm
  let : Subsingleton S.toSubmodule := ⟨fun v w => (hzero v).trans (hzero w).symm⟩
  have h0 := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := S.toSubmodule)
  omega

/-- Both four-dimensional summands are retained. A nonzero projection of the
irreducible seed is injective; at least one projection is nonzero. The
projections need only commute with the component action. -/
theorem not_fourPlusDual_of_plane_exclusion (hfour : FourPlaneExclusion) :
    ¬ IsFourPlusDual ρ ι := by
  rintro ⟨σ, hσ, ⟨e⟩⟩
  let f : E →ₗ[ZMod 2] Four := (LinearMap.fst _ _ _).comp e.symm.toLinearMap
  let g : E →ₗ[ZMod 2] Module.Dual (ZMod 2) Four :=
    (LinearMap.snd _ _ _).comp e.symm.toLinearMap
  have hf (a : A7) (v : E) : f (ρ (ι a) v) = σ a (f v) :=
    congrArg Prod.fst (Representation.IntertwiningMap.isIntertwining (ρ.comp ι) (σ.prod σ.dual) e.symm.toIntertwiningMap a v)
  have hg (a : A7) (v : E) : g (ρ (ι a) v) = σ.dual a (g v) :=
    congrArg Prod.snd (Representation.IntertwiningMap.isIntertwining (ρ.comp ι) (σ.prod σ.dual) e.symm.toIntertwiningMap a v)
  by_cases hf0 : f.domRestrict S.toSubmodule = 0
  · apply no_nonzero_four_image ρ φ ι hι L hL S hdim hP hfour σ.dual
      (dual_faithful σ hσ) (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_fin_fun _)
      g hg
    intro hg0
    have hzero : ∀ v : S.toSubmodule, v = 0 := by
      intro v
      apply Subtype.ext
      apply e.symm.injective
      change e.symm (v : E) = e.symm (0 : E)
      rw [map_zero]
      exact Prod.ext (DFunLike.congr_fun hf0 v) (DFunLike.congr_fun hg0 v)
    let : Subsingleton S.toSubmodule := ⟨fun v w => (hzero v).trans (hzero w).symm⟩
    have h0 := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := S.toSubmodule)
    omega
  · exact no_nonzero_four_image ρ φ ι hι L hL S hdim hP hfour σ hσ
      (Module.finrank_fin_fun (ZMod 2)) f hf hf0

/-- The complete 4/6/(4+dual) alternatives select the equivariant natural model,
conditional only on the separately owned finite plane calculation. -/
theorem natural_of_alternatives (hfour : FourPlaneExclusion)
    (halt : SmallModuleAlternatives ρ φ ι) : IsNatural ρ φ := by
  rcases halt with h4 | h6 | h8
  · exact (not_four_of_plane_exclusion ρ φ ι hι L hL S hdim hP hfour h4).elim
  · exact h6
  · exact (not_fourPlusDual_of_plane_exclusion ρ φ ι hι L hL S hdim hP hfour h8).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
