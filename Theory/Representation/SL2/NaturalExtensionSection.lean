module
public import Theory.Representation.SL2.NaturalExtension
public import Theory.Representation.BinaryConjugationSection.NaturalExtension

/-!
# Original triple commutators from two natural factors

The literal Q/Z conjugation action descends through the specified SL₂
quotient. Marked natural factors V/Z and Q/V give its two nontrivial
sections. A subgroup D centralizing the Sylow modulo Z, with |D:Z|=q²,
supplies the full fixed-space bound. The arbitrary-degree quadratic
extension theorem therefore puts [Q,S,S] in Z.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 3.4 and the
class-three exclusion on p.58. No complement to the central kernel or
restriction to the field of order four is used.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL2
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
local instance naturalExtensionSectionAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The original natural factors force a triple-commutator bound at every
binary degree, retaining the literal center quotient and actor marking. -/
theorem triple_commutator_le_of_natural_factors
    (Q V Z : Subgroup G) [Q.Normal] [Z.Normal]
    (hVQ : V ≤ Q) (hZV : Z ≤ V)
    [IsElementaryAbelian 2 (Q ⧸ Z.subgroupOf Q)]
    (f : G →* SL(2,F)) (hf : Function.Surjective f) (hk : f.ker = Q)
    (cV : BinaryConjugationSection ⊤ V Z
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp
        (f.comp (⊤ : Subgroup G).subtype)))
    (cQ : BinaryConjugationSection ⊤ Q V
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp
        (f.comp (⊤ : Subgroup G).subtype)))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (D : Subgroup G) (hDQ : D ≤ Q)
    (hSD : ⁅(S : Subgroup G),D⁆ ≤ Z) (hi : Z.relIndex D = Nat.card F ^ 2) :
    ⁅⁅Q,(S : Subgroup G)⁆,(S : Subgroup G)⁆ ≤ Z := by
  let q : (⊤ : Subgroup G) →* SL(2,F) := f.comp (⊤ : Subgroup G).subtype
  have hq : Function.Surjective q := by
    intro g
    obtain ⟨x,rfl⟩ := hf g
    exact ⟨⟨x,mem_top x⟩,rfl⟩
  have hqker : q.ker = Q.subgroupOf ⊤ := by
    ext x
    change f (x : G) = 1 ↔ (x : G) ∈ Q
    rw [←hk]
    rfl
  obtain ⟨ρ,c,_⟩ := BinaryConjugationSection.exists_canonical ⊤ Q Z le_top
    (hZV.trans hVQ) (by rw [normalizer_eq_top]) (by rw [normalizer_eq_top]) q hq hqker
  let τ := (specialLinearNatural 2 (k := F)).restrictScalars (k := ZMod 2)
  obtain ⟨X,eX,eQ,heX,heQ,_⟩ := BinaryConjugationSection.exists_natural_submodule
    (W := Additive (Q ⧸ Z.subgroupOf Q)) ⊤ Q V Z hVQ hZV q hq ρ τ c cV cQ
  let P := S.mapSurjective hf
  have hP : ((S : Subgroup G).subgroupOf ⊤).map q = (P : Subgroup SL(2,F)) := by
    change ((S : Subgroup G).subgroupOf ⊤).map
      (f.comp (⊤ : Subgroup G).subtype) = (S : Subgroup G).map f
    rw [←map_map,subgroupOf_map_subtype,inf_top_eq]
  have hfixed : 2*n ≤ Module.finrank (ZMod 2) (fixedSpace ρ P) := by
    rw [←hP]
    apply c.fixedDimension_ge_of_commutator_le ρ q S D hDQ hSD (2*n)
    rw [hi,hF,←pow_mul,Nat.mul_comm n 2]
  have hquad := sylow_quadratic_of_natural_sections ρ X eX eQ heX heQ hn hF P hfixed
  apply c.triple_commutator_le_of_quadratic ρ q S le_top
  rwa [hP]
end Representation.SL2
