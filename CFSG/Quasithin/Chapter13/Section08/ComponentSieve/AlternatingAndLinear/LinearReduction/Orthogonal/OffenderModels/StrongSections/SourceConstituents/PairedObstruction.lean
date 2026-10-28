module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Constituents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.ComponentInputs
public import Theory.Representation.BinaryOffender.SmallRank
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.DualCommutator

/-!
# The stabilizing actor on a natural-plus-dual pair

For a faithful quadratic action on a space of dimension at most four, put
r = codim C_V(A) and s = dim [V,A]. Displacement embeds A into Hom(V/C_V(A),[V,A]),
so its binary rank is at most r*s. Quadraticity gives r+s ≤ 4; hence r*s ≤ r+s.
Duality identifies s with the fixed codimension on V*. Therefore the actor
cannot be a strong offender on V ⊕ V*.

The exported statement transports this calculation to an actual equivariantly
identified K-restriction, keeping the original contained actor. This supplies
the stabilizing case absent from the exchanged-summand argument in 13.8.25,
printed p.960 (Aschbacher–Smith, 1 March 2004 manuscript).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.SourceConstituents
open Representation Representation.BinaryOffender
open FourStructure.ChiefFactors OrthogonalQuotient
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

private theorem product_bound (a b : ℕ) (h : a + b ≤ 4) : a * b ≤ a + b := by
  have ha : a ≤ 4 := by omega
  have hb : b ≤ 4 := by omega
  interval_cases a <;> interval_cases b <;> omega

private theorem rank_le_pair_fixedCodim (ρ : Representation (ZMod 2) H U)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) U ≤ 4)
    (A : Subgroup H) (hq : IsQuadratic ρ A) :
    rank A ≤ fixedCodim (ρ.prod ρ.dual) A := by
  let C := Coinvariants.ker (ρ.comp A.subtype)
  have hC : C ≤ fixedSpace ρ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩ b
    exact hq b b.property a a.property v
  have hc : fixedCodim ρ.dual A = Module.finrank (ZMod 2) C :=
    finrank_quotient_dual_invariants_eq_commutator (ρ.comp A.subtype)
  have hdim := Submodule.finrank_mono hC
  have hadd := fixedCodim_add_finrank ρ A
  have hr := rank_le_fixed_codim_mul_displacement_dim ρ hf A (fixedSpace ρ A) C le_rfl
    (fun a ha v => Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨a, ha⟩ v)
  change rank A ≤ fixedCodim ρ A * Module.finrank (ZMod 2) C at hr
  rw [← hc] at hr hdim
  rw [fixedCodim_prod]
  exact hr.trans (product_bound _ _ (by omega))

omit [FiniteDimensional (ZMod 2) U] in
/-- A quadratic actor contained in K is not strong on the actual
natural-plus-dual restriction, with both models using the same marking. -/
theorem not_strong_of_naturalDualRestriction
    (ρ : Representation (ZMod 2) H U) (K A : Subgroup H)
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (hmodel : IsNaturalDualRestriction ρ K eK) (hAK : A ≤ K)
    (hq : IsQuadratic ρ A) : ¬ IsStrongOffender ρ A := by
  obtain ⟨e, he⟩ := hmodel
  let σ := naturalAction eK
  let B := A.subgroupOf K
  have hAB : B.map K.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAK
  have hfix : fixedCodim (ρ.comp K.subtype) B = fixedCodim ρ A := by
    have h := fixedCodim_map_equivariant (ρ.comp K.subtype) ρ K.subtype
      (LinearEquiv.refl (ZMod 2) U) (fun _ _ => rfl) B
    rwa [hAB] at h
  have hrank : rank B = rank A := by
    have h := rank_map_injective K.subtype Subtype.val_injective B
    rw [hAB] at h
    exact h.symm
  have hqB : IsQuadratic (ρ.comp K.subtype) B := by
    intro a ha b hb v
    exact hq a ha b hb v
  have he' : ∀ g v, e ((ρ.comp K.subtype) g v) = (σ.prod σ.dual) g (e v) := by
    intro g v
    rw [show (ρ.comp K.subtype) g = ρ g from rfl, he]
    apply Prod.ext
    · exact BinaryLinear.NaturalDualFlag.action_fst (eK g) (e v)
    · apply LinearMap.ext
      intro x
      change (BinaryLinear.NaturalDualFlag.action (eK g) (e v)).2 x =
        (e v).2 (eK g⁻¹ x)
      rw [BinaryLinear.NaturalDualFlag.action_snd, map_inv]
      rfl
  have hqprod := quadratic_of_equivariant_surjection (ρ.comp K.subtype) (σ.prod σ.dual)
    e.toLinearMap e.surjective he' B hqB
  have hfσ : Function.Injective σ := by
    intro a b hab
    apply eK.injective
    exact LinearEquiv.toLinearMap_injective hab
  have hle := rank_le_pair_fixedCodim σ hfσ (by simp [FourSpace]) B
    ((quadratic_prod_iff σ σ.dual B).mp hqprod).1
  have hcost := fixedCodim_map_equivariant (ρ.comp K.subtype) (σ.prod σ.dual)
    (MonoidHom.id K) e he' B
  simp only [Subgroup.map_id] at hcost
  rw [← hcost, hfix, hrank] at hle
  exact fun hs => Nat.not_lt_of_ge hle hs.2
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.SourceConstituents
