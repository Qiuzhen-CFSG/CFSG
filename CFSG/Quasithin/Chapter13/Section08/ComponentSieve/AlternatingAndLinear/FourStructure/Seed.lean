module

public import Theory.Representation.BinaryOffender.FixedGenerator
public import Mathlib.GroupTheory.PGroup

/-!
# The generating two-space in the L₄ argument

A two-dimensional irreducible parabolic submodule whose H-span is the whole
module supplies a nonzero T-fixed generator: the two-group T has a nonzero
fixed point, and parabolic irreducibility makes its H-orbit span contain the
whole seed. The same argument proves that the seed injects into every proper
quotient. The last theorem supplies this generator to the published uniqueness
criterion; aligning the quotient representations remains a separate obligation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed pp.957, 960–961 (13.8.25).
`GeneratingSeed` records the properties of Ṽ₃ used here. Its construction from
the actual conjugate span U_H = ⟨V₃^H⟩ belongs to the source application.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
open Representation.BinaryOffender

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

structure GeneratingSeed where
  parabolic : Subgroup H
  sylow : Subgroup H
  sylow_le : sylow ≤ parabolic
  sylow_two_group : IsPGroup 2 sylow
  space : Subrepresentation (ρ.comp parabolic.subtype)
  irreducible : IsAtom space
  dim_two : Module.finrank (ZMod 2) space.toSubmodule = 2
  generates : ∀ W : Subrepresentation ρ, space.toSubmodule ≤ W.toSubmodule → W = ⊤

private def orbitSpan (v : U) : Subrepresentation ρ where
  toSubmodule := Submodule.span (ZMod 2) (Set.range (fun g : H => ρ g v))
  apply_mem_toSubmodule g := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by change ρ (g * h) v = ρ g (ρ h v); rw [map_mul]; rfl⟩
    | zero => simpa only [map_zero] using (Submodule.zero_mem _ : (0 : U) ∈ Submodule.span (ZMod 2) (Set.range (fun g : H => ρ g v)))
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

private def restrict (P : Subgroup H) (W : Subrepresentation ρ) :
    Subrepresentation (ρ.comp P.subtype) where
  toSubmodule := W.toSubmodule
  apply_mem_toSubmodule g := W.apply_mem_toSubmodule g

theorem GeneratingSeed.orbit_span_eq_top (s : GeneratingSeed ρ)
    {v : U} (hv : v ∈ s.space) (hv0 : v ≠ 0) :
    Submodule.span (ZMod 2) (Set.range (fun g : H => ρ g v)) = ⊤ := by
  let X := s.space ⊓ restrict ρ s.parabolic (orbitSpan ρ v)
  have hvX : v ∈ X := by
    refine ⟨hv, Submodule.subset_span ⟨1, ?_⟩⟩
    simp
  have hX : X ≠ ⊥ := by
    intro h
    have hz : v ∈ (⊥ : Subrepresentation (ρ.comp s.parabolic.subtype)) := h ▸ hvX
    exact hv0 hz
  have he : X = s.space := (s.irreducible.le_iff_eq hX).mp inf_le_left
  have hle : s.space.toSubmodule ≤ (orbitSpan ρ v).toSubmodule := by
    intro u hu
    have : u ∈ X := he ▸ hu
    exact this.2
  exact congrArg Subrepresentation.toSubmodule (s.generates _ hle)

variable [FiniteDimensional (ZMod 2) U]

theorem GeneratingSeed.exists_fixed_generator (s : GeneratingSeed ρ) :
    ∃ v : U, v ∈ s.space ∧ v ≠ 0 ∧ v ∈ fixedSpace ρ s.sylow ∧
      Submodule.span (ZMod 2) (Set.range (fun g : H => ρ g v)) = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite s.space.toSubmodule := Module.finite_of_finite (ZMod 2)
  let τ := s.space.toRepresentation.comp (Subgroup.inclusion s.sylow_le)
  let : MulAction s.sylow s.space.toSubmodule := {
    smul t v := τ t v
    one_smul v := by change τ 1 v = v; simp
    mul_smul t r v := by change τ (t * r) v = τ t (τ r v); rw [map_mul]; rfl }
  have hcard : 2 ∣ Nat.card s.space.toSubmodule := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, s.dim_two]
    decide
  obtain ⟨v, hv, hv0⟩ := s.sylow_two_group.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    s.space.toSubmodule hcard (a := 0) (by intro t; exact map_zero (τ t))
  have hne : (v : U) ≠ 0 := fun h => hv0 (Subtype.ext h.symm)
  refine ⟨v, v.property, hne, ?_, s.orbit_span_eq_top ρ v.property hne⟩
  intro t
  exact congrArg Subtype.val (hv t)

omit [FiniteDimensional (ZMod 2) U] in
theorem GeneratingSeed.disjoint_proper (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) :
    Disjoint s.space.toSubmodule W.toSubmodule := by
  let X := s.space ⊓ restrict ρ s.parabolic W
  have hX : X ≤ s.space := inf_le_left
  rcases s.irreducible.le_iff.mp hX with hbot | heq
  · exact disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hbot)
  · exfalso
    apply hW
    apply s.generates
    intro u hu
    have : u ∈ X := heq ▸ hu
    exact this.2

omit [FiniteDimensional (ZMod 2) U] in
theorem GeneratingSeed.quotient_injective (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) :
    Function.Injective (W.toSubmodule.mkQ.comp s.space.toSubmodule.subtype) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hw : (x : U) - y ∈ W.toSubmodule :=
    (Submodule.Quotient.eq W.toSubmodule).mp hxy
  have hs := s.space.toSubmodule.sub_mem x.property y.property
  exact (Submodule.disjoint_def.mp (s.disjoint_proper ρ W hW)) _ hs hw

/-- The seed supplies the generator premise in the fixed-generator uniqueness
criterion. The source application must still align the maximal quotients. -/
theorem GeneratingSeed.unique_maximal
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (s : GeneratingSeed ρ) (σ : Representation (ZMod 2) H E)
    (hfix : Module.finrank (ZMod 2) (fixedSpace σ s.sylow) = 1)
    (hquot : ∀ W : Subrepresentation ρ, IsCoatom W →
      ∃ e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] E,
        ∀ g q, e (W.quotientRepresentation g q) = σ g (e q))
    (W : Subrepresentation ρ) (hW : IsCoatom W) :
    ∀ X : Subrepresentation ρ, IsCoatom X → X = W := by
  obtain ⟨v, _, _, hv, hgen⟩ := s.exists_fixed_generator ρ
  exact unique_maximal_of_equivariant_quotients ρ σ s.sylow v hgen hv hfix hquot W hW

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
