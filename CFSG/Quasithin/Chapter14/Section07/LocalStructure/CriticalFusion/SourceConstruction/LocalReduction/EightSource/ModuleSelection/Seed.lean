module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.Models

/-!
# The middle-node flag excludes a transitive seed in the eight-space

Every invariant plane in the natural-plus-dual module has a nonzero vector
fixed by its marked middle-node minimal parabolic. A transitive action on the
three nonzero vectors of the actual source seed cannot have such a fixed
vector. This transports the genuine flag obstruction to the supplied module.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
universe u v
variable {H : Type u} [Group H] {X : Type v} [AddCommGroup X] [Module (ZMod 2) X]
  [FiniteDimensional (ZMod 2) X]

theorem not_naturalDual_of_transitive_seed
    (ρ : Representation (ZMod 2) H X) (K : Subgroup H)
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (P : Subgroup K) (A B : Submodule (ZMod 2) FourSpace) (hAB : A ≤ B)
    (hA : Module.finrank (ZMod 2) A = 1) (hB : Module.finrank (ZMod 2) B = 3)
    (hP : P.map eK.toMonoidHom = BinaryLinear.parabolic A ⊓ BinaryLinear.parabolic B)
    (S : Submodule (ZMod 2) X) (hS : Module.finrank (ZMod 2) S = 2)
    (hstable : ∀ g ∈ P, ∀ x ∈ S, ρ (g : H) x ∈ S)
    (htrans : ∀ x ∈ S, x ≠ 0 → ∀ y ∈ S, y ≠ 0 →
      ∃ g ∈ P.map K.subtype, ρ g x = y) : ¬ IsNaturalDualRestriction ρ K eK := by
  rintro ⟨e,he⟩
  let W := S.map e.toLinearMap
  let : Finite W := Module.finite_of_finite (ZMod 2)
  have hW : Module.finrank (ZMod 2) W = 2 :=
    (Submodule.equivMapOfInjective e.toLinearMap e.injective S).finrank_eq.symm.trans hS
  have hc : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hW]
    decide
  obtain ⟨v,hv,hv0,hfix⟩ := BinaryLinear.NaturalDualFlag.exists_fixed hAB hA
    (by rw [hB]; exact (Module.finrank_fin_fun (ZMod 2)).symm) W hc (by
      intro g hg w hw
      obtain ⟨k,hk,rfl⟩ := hP.symm ▸ hg
      obtain ⟨x,hx,rfl⟩ := hw
      exact ⟨ρ k x,hstable k hk x hx,he k x⟩)
  obtain ⟨x,hx,rfl⟩ := hv
  have hx0 : x ≠ 0 := fun hz => hv0 (by rw [hz,map_zero])
  have hfixX : ∀ g ∈ P.map K.subtype, ρ g x = x := by
    rintro g ⟨k,hk,rfl⟩
    apply e.injective
    exact (he k x).trans (hfix (eK k) (hP ▸ mem_map_of_mem eK.toMonoidHom hk))
  have hnot : ¬ S ≤ Submodule.span (ZMod 2) {x} := by
    intro hh
    have hd := Submodule.finrank_mono hh
    rw [hS,finrank_span_singleton hx0] at hd
    omega
  obtain ⟨y,hy,hyn⟩ := SetLike.not_le_iff_exists.mp hnot
  have hy0 : y ≠ 0 := by
    intro hz
    apply hyn
    rw [hz]
    exact Submodule.zero_mem _
  have hyx : y ≠ x := by
    intro hz
    apply hyn
    rw [hz]
    exact Submodule.mem_span_singleton_self x
  obtain ⟨g,hg,hgxy⟩ := htrans x hx hx0 y hy hy0
  exact hyx (hgxy.symm.trans (hfixX g hg))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
