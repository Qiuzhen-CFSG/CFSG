module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Source
public import Theory.Representation.BinaryPermutationNaturalStructure
/-!
# Generation of the source module by its first flag

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, §13.5, printed p.916, and 13.8.6(5), printed p.948.

The actual four-dimensional A₆ natural module is irreducible by B.3.1.
Transporting the L-conjugate span of V₁ through the specified equivariant
identification therefore proves V = ⟨V₁^L⟩. The flag is required to be
nontrivial and contained in V. Generation is a conclusion, not a premise.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed
open BinaryPermutation
variable {G : Type*} [Group G]

/-- Irreducibility of the actual A₆ natural module proves generation by any
nontrivial flag subgroup; no generation identity is assumed. -/
theorem V_generated_by_flag (L V V₁ : Subgroup G) [IsElementaryAbelian 2 V]
    (hLV : L ≤ normalizer (V : Set G)) (hV₁V : V₁ ≤ V) (hV₁ : V₁ ≠ ⊥)
    (α : L →* alternatingGroup (Fin 6)) (hα : Function.Surjective α)
    (e : Additive V ≃ₗ[ZMod 2] natural (Fin 6))
    (heq : ∀ (l : L) (v : V),
      e (Additive.ofMul ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (hLV l.property) v).mp v.property⟩) =
      alternatingNaturalRepresentation (Fin 6) (α l) (e (Additive.ofMul v))) :
    V = conjugateSpanBy V₁ L := by
  let B := conjugateSpanBy V₁ L
  have hBV : B ≤ V := conjugateSpanBy_le hV₁V hLV
  let W : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 ((B.subgroupOf V).toAddSubgroup)
  let S : Subrepresentation (alternatingNaturalRepresentation (Fin 6)) := {
    toSubmodule := W.map e.toLinearMap
    apply_mem_toSubmodule := by
      intro a v hv
      obtain ⟨u, hu, rfl⟩ := hv
      obtain ⟨l, rfl⟩ := hα a
      let u' : V := ⟨(l : G) * u.toMul * (l : G)⁻¹,
        (mem_normalizer_iff.mp (hLV l.property) u.toMul).mp u.toMul.property⟩
      refine ⟨Additive.ofMul u', ?_, (heq l u.toMul)⟩
      exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₁ L l.property) u.toMul).mp hu }
  let : Representation.IsIrreducible (alternatingNaturalRepresentation (Fin 6)) :=
    alternatingNatural_isIrreducible (by decide)
  have hS : S = ⊤ := by
    apply (eq_bot_or_eq_top S).resolve_left
    intro hbot
    apply hV₁
    apply eq_bot_iff.mpr
    intro v hv
    let vV : V := ⟨v, hV₁V hv⟩
    have hvS : e (Additive.ofMul vV) ∈ S.toSubmodule :=
      ⟨Additive.ofMul vV, le_conjugateSpanBy V₁ L hv, rfl⟩
    rw [hbot] at hvS
    have hvzero : e (Additive.ofMul vV) = 0 := hvS
    have he : Additive.ofMul vV = 0 := e.map_eq_zero_iff.mp hvzero
    exact congrArg (fun x : Additive V => (x.toMul : G)) he
  apply le_antisymm ?_ hBV
  intro v hv
  let vV : V := ⟨v, hv⟩
  have hvS : e (Additive.ofMul vV) ∈ S.toSubmodule := by rw [hS]; trivial
  obtain ⟨u, hu, he⟩ := hvS
  have hue : u = Additive.ofMul vV := e.injective he
  subst u
  exact hu

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed

end
