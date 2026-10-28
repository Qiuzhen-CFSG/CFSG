module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The marked seed in natural and dual maximal quotients

The literal quotient map is injective on the generating two-space. Its image
therefore remains two-dimensional, invariant under the marked parabolic, and
fixed by the marked subgroup. A plane stabilizer has just one nonzero proper
invariant subspace in the natural module. Dual annihilators give the
corresponding assertion for the dual module.

If natural and dual quotients both occur, the marked subgroup fixes the plane
and its dual annihilator. It is then contained in the unipotent radical and is
a two-group. This is incompatible with the cubic part of the source L₀*.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed pp.960–961. The source application
must identify the actual L₁T parabolic and supply fixation by the actual L₀*.
The six-dimensional head is not excluded by this module.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
variable {H U E : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup E] [Module (ZMod 2) E]

/-- The image of the actual seed under a quotient identification. -/
def seedMap (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] E) :
    s.space.toSubmodule →ₗ[ZMod 2] E :=
  e.toLinearMap.comp (W.toSubmodule.mkQ.comp s.space.toSubmodule.subtype)

theorem seedMap_injective (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] E) :
    Function.Injective (seedMap ρ s W e) :=
  e.injective.comp (s.quotient_injective ρ W hW)

theorem seedMap_range_finrank (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] E) :
    Module.finrank (ZMod 2) (LinearMap.range (seedMap ρ s W e)) = 2 := by
  rw [LinearMap.finrank_range_of_inj (seedMap_injective ρ s W hW e)]
  exact s.dim_two

theorem seedMap_range_stable (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] E)
    (σ : Representation (ZMod 2) H E)
    (he : ∀ g q, e (W.quotientRepresentation g q) = σ g (e q)) :
    ∀ g ∈ s.parabolic, ∀ v ∈ LinearMap.range (seedMap ρ s W e),
      σ g v ∈ LinearMap.range (seedMap ρ s W e) := by
  rintro g hg v ⟨u, rfl⟩
  refine ⟨s.space.toRepresentation ⟨g, hg⟩ u, ?_⟩
  change e (W.toSubmodule.mkQ (ρ g u)) = σ g (e (W.toSubmodule.mkQ u))
  exact he g (W.toSubmodule.mkQ u)

theorem seedMap_range_fixed (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] E)
    (σ : Representation (ZMod 2) H E)
    (he : ∀ g q, e (W.quotientRepresentation g q) = σ g (e q))
    (R : Subgroup H) (hR : ∀ g ∈ R, ∀ v ∈ s.space, ρ g v = v) :
    ∀ g ∈ R, ∀ v ∈ LinearMap.range (seedMap ρ s W e), σ g v = v := by
  rintro g hg v ⟨u, rfl⟩
  change σ g (e (W.toSubmodule.mkQ u)) = e (W.toSubmodule.mkQ u)
  rw [← he, Subrepresentation.quotientRepresentation_mk, hR g hg u u.property]

private theorem natural_plane_unique
    (P S : Submodule (ZMod 2) NaturalSpace)
    (hS : Module.finrank (ZMod 2) S = 2)
    (hstable : ∀ g ∈ BinaryLinear.parabolic P, ∀ v ∈ S, g v ∈ S) : S = P := by
  have hS0 : S ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hS
    omega
  have hS1 : S ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hS
    norm_num [NaturalSpace] at hS
  apply (BinaryLinear.FourParabolicAction.parabolic_le_imp_eq hS0 hS1 ?_).symm
  intro g hg v
  constructor
  · intro hv
    simpa using hstable g⁻¹ ((BinaryLinear.parabolic P).inv_mem hg) (g v) hv
  · exact hstable g hg v

private theorem dual_plane_unique
    (P : Submodule (ZMod 2) NaturalSpace)
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) NaturalSpace))
    (hS : Module.finrank (ZMod 2) S = 2)
    (hstable : ∀ g ∈ BinaryLinear.parabolic P, ∀ f ∈ S, g.symm.dualMap f ∈ S) :
    S = P.dualAnnihilator := by
  have hdim : Module.finrank (ZMod 2) S.dualCoannihilator = 2 := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq S
    have hfour : Module.finrank (ZMod 2) NaturalSpace = 4 := by simp [NaturalSpace]
    omega
  have he : S.dualCoannihilator = P := natural_plane_unique P _ hdim (by
    intro g hg v hv
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro f hf
    have hf' := hstable g⁻¹ ((BinaryLinear.parabolic P).inv_mem hg) f hf
    have hz := (Submodule.mem_dualCoannihilator _).mp hv _ hf'
    change f ((g⁻¹)⁻¹ v) = 0 at hz
    simpa only [inv_inv] using hz)
  rw [← he, Subspace.dualCoannihilator_dualAnnihilator_eq]

theorem natural_seed_plane
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (P : Submodule (ZMod 2) NaturalSpace)
    (hP : s.parabolic.map eH.toMonoidHom = BinaryLinear.parabolic P)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] NaturalSpace)
    (he : ∀ g q, e (W.quotientRepresentation g q) = eH g (e q)) :
    LinearMap.range (seedMap ρ s W e) = P := by
  apply natural_plane_unique P _ (seedMap_range_finrank ρ s W hW e)
  intro g hg v hv
  rw [← hP] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  exact seedMap_range_stable ρ s W e (naturalAction eH) he h hh v hv

theorem dual_seed_plane
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (P : Submodule (ZMod 2) NaturalSpace)
    (hP : s.parabolic.map eH.toMonoidHom = BinaryLinear.parabolic P)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) NaturalSpace)
    (he : ∀ g q, e (W.quotientRepresentation g q) = (naturalAction eH).dual g (e q)) :
    LinearMap.range (seedMap ρ s W e) = P.dualAnnihilator := by
  apply dual_plane_unique P _ (seedMap_range_finrank ρ s W hW e)
  intro g hg f hf
  rw [← hP] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  have hs := seedMap_range_stable ρ s W e (naturalAction eH).dual he h hh f hf
  have heq : (eH h).symm.dualMap f = (naturalAction eH).dual h f := by
    apply LinearMap.ext
    intro v
    change f ((eH h).symm v) = f (eH h⁻¹ v)
    rw [map_inv]
    rfl
  change (eH h).symm.dualMap f ∈ LinearMap.range (seedMap ρ s W e)
  rw [heq]
  exact hs

/-- Fixing the two marked seed planes in opposite orientations would put the
whole marked subgroup into the binary unipotent radical. -/
theorem two_group_of_opposite_heads
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (P : Submodule (ZMod 2) NaturalSpace)
    (hP : s.parabolic.map eH.toMonoidHom = BinaryLinear.parabolic P)
    (R : Subgroup H) (hR : ∀ g ∈ R, ∀ v ∈ s.space, ρ g v = v)
    (W X : Subrepresentation ρ) (hW : W ≠ ⊤) (hX : X ≠ ⊤)
    (hN : IsNatural W.quotientRepresentation eH)
    (hD : ∃ e : (U ⧸ X.toSubmodule) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) NaturalSpace,
      ∀ g q, e (X.quotientRepresentation g q) = (naturalAction eH).dual g (e q)) :
    IsPGroup 2 R := by
  obtain ⟨e, he⟩ := hN
  obtain ⟨f, hf⟩ := hD
  have hfixP : ∀ g ∈ R, ∀ v ∈ P, eH g v = v := by
    rw [← natural_seed_plane ρ s eH P hP W hW e he]
    exact seedMap_range_fixed ρ s W e (naturalAction eH) he R hR
  have hfixD : ∀ g ∈ R, ∀ v ∈ P.dualAnnihilator,
      (naturalAction eH).dual g v = v := by
    rw [← dual_seed_plane ρ s eH P hP X hX f hf]
    exact seedMap_range_fixed ρ s X f (naturalAction eH).dual hf R hR
  have hrad : ∀ r : R, eH r ∈ BinaryLinear.radical P := by
    intro r
    refine ⟨hfixP r r.property, ?_⟩
    intro v
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := P)]
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro l hl
    have heq := LinearMap.congr_fun (hfixD r⁻¹ ((R.inv_mem r.property)) l hl) v
    change l (eH ((r : H)⁻¹)⁻¹ v) = l v at heq
    simp only [inv_inv] at heq
    rw [map_sub, heq, sub_self]
  let i : R →* BinaryLinear.radical P :=
    (eH.toMonoidHom.comp R.subtype).codRestrict _ hrad
  apply (BinaryLinear.radical_two P).of_injective i
  intro r t h
  apply Subtype.ext
  apply eH.injective
  exact congrArg Subtype.val h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
