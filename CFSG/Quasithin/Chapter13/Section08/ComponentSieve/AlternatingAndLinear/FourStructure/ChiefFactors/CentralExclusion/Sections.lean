module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion.Cohomology
public import Mathlib.Order.Atoms.Finite

/-!
# Exact quotient sequences and central chief sections

For invariant subspaces A ≤ B, the literal section B/A injects into U/A,
with image the kernel of U/A → U/B. Centrality of the section is exactly
the fixed-kernel condition needed by the covering argument. Commutator
generation passes to quotients, so vanishing H¹ of the dual of U/B rules
out a nonzero central kernel.

Source: Aschbacher–Smith, Remark I.1.5, printed p.408, and the
central-chief-factor step in 13.8.25, printed p.961.
-/

@[expose] public section

open Representation Representation.OneCohomology Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U) (A B : Subrepresentation ρ)

def sectionInclusion : (sectionRepresentation ρ A B).IntertwiningMap A.quotientRepresentation :=
  ((sectionLower ρ A B).toSubmodule.liftQ
    (A.toSubmodule.mkQ.comp B.toSubmodule.subtype) (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx)).intertwiningMap_of_isIntertwiningMap _ _ (by
        intro g v
        induction v using Submodule.Quotient.induction_on with | _ v => rfl)

def quotientMap (hAB : A ≤ B) : A.quotientRepresentation.IntertwiningMap B.quotientRepresentation :=
  (A.toSubmodule.mapQ B.toSubmodule LinearMap.id hAB).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g v
    induction v using Submodule.Quotient.induction_on with | _ v => rfl)

lemma sectionInclusion_injective : Function.Injective (sectionInclusion ρ A B) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  induction v using Submodule.Quotient.induction_on with | _ v =>
  change A.toSubmodule.mkQ (v : U) = 0 at hv
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero A.toSubmodule).mp hv)

lemma quotientMap_surjective (hAB : A ≤ B) : Function.Surjective (quotientMap ρ A B hAB) := by
  intro v
  induction v using Submodule.Quotient.induction_on with | _ v =>
  exact ⟨A.toSubmodule.mkQ v, rfl⟩

lemma section_exact (hAB : A ≤ B) :
    (sectionInclusion ρ A B).toLinearMap.range = (quotientMap ρ A B hAB).toLinearMap.ker := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with | _ x =>
    exact (Submodule.Quotient.mk_eq_zero _).mpr x.property
  · intro hv
    induction v using Submodule.Quotient.induction_on with | _ v =>
    have hvB : v ∈ B := (Submodule.Quotient.mk_eq_zero _).mp hv
    exact ⟨(sectionLower ρ A B).toSubmodule.mkQ ⟨v, hvB⟩, rfl⟩

lemma quotientMap_kernel_fixed (hAB : A ≤ B) (hc : IsCentralSection ρ A B) :
    (quotientMap ρ A B hAB).toLinearMap.ker ≤ fixed A.quotientRepresentation := by
  intro v hv g
  rw [← section_exact] at hv
  obtain ⟨x, rfl⟩ := hv
  change A.quotientRepresentation g (sectionInclusion ρ A B x) = sectionInclusion ρ A B x
  rw [← (sectionInclusion ρ A B).isIntertwining, hc]

lemma eq_of_quotientMap_injective (hAB : A ≤ B)
    (hi : Function.Injective (quotientMap ρ A B hAB)) : A = B := by
  apply le_antisymm hAB
  intro v hv
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply hi
  change B.toSubmodule.mkQ v = (quotientMap ρ A B hAB) 0
  rw [map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hv

lemma quotient_dual_H1_step [Finite H] [FiniteDimensional (ZMod 2) U]
    (hAB : A ≤ B)
    (hA : Module.finrank (ZMod 2) (H1 (sectionRepresentation ρ A B).dual) = 0)
    (hB : Module.finrank (ZMod 2) (H1 B.quotientRepresentation.dual) = 0) :
    Module.finrank (ZMod 2) (H1 A.quotientRepresentation.dual) = 0 :=
  h1_vanish_dual_exact (sectionInclusion ρ A B) (quotientMap ρ A B hAB)
    (sectionInclusion_injective ρ A B) (quotientMap_surjective ρ A B hAB)
    (section_exact ρ A B hAB) hA hB


lemma commutator_stable (g : H) :
    Coinvariants.ker ρ ≤ (Coinvariants.ker ρ).comap (ρ g) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨h, v⟩, rfl⟩
  change ρ g (ρ h v - v) ∈ Coinvariants.ker ρ
  have he : ρ g (ρ h v - v) = (ρ (g * h) v - v) - (ρ g v - v) := by
    rw [map_sub, map_mul, Module.End.mul_apply]
    abel
  rw [he]
  exact (Coinvariants.ker ρ).sub_mem (Coinvariants.sub_mem_ker _ _)
    (Coinvariants.sub_mem_ker _ _)

def commutatorSubrepresentation : Subrepresentation ρ where
  toSubmodule := Coinvariants.ker ρ
  apply_mem_toSubmodule g := commutator_stable ρ g

lemma quotient_commutator_top (hgen : Coinvariants.ker ρ = ⊤) :
    Coinvariants.ker A.quotientRepresentation = ⊤ := by
  have hle : Coinvariants.ker ρ ≤
      (Coinvariants.ker A.quotientRepresentation).comap A.toSubmodule.mkQ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change A.toSubmodule.mkQ (ρ g v - v) ∈ Coinvariants.ker A.quotientRepresentation
    rw [map_sub, ← A.quotientRepresentation_mk]
    exact Coinvariants.sub_mem_ker g _
  rw [hgen] at hle
  apply top_unique
  intro v _
  obtain ⟨u, rfl⟩ := A.toSubmodule.mkQ_surjective v
  exact hle (by trivial)

lemma central_section_eq [Finite H] [FiniteDimensional (ZMod 2) U]
    (hgen : Coinvariants.ker ρ = ⊤) (hAB : A ≤ B) (hc : IsCentralSection ρ A B)
    (hB : Module.finrank (ZMod 2) (H1 B.quotientRepresentation.dual) = 0) : A = B := by
  apply eq_of_quotientMap_injective ρ A B hAB
  exact cover_injective (quotientMap ρ A B hAB)
    ⟨quotientMap_surjective ρ A B hAB, quotientMap_kernel_fixed ρ A B hAB hc,
      quotient_commutator_top ρ A hgen⟩ hB

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion
