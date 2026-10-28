module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.Ambient

/-!
# Removing the field factor from an inner subgroup of FH

Suppose B ≤ D and B lies in the set product FH. If F acts by actual coefficient
field automorphisms and H acts by actual inner automorphisms on the G₂ model,
the field-outerness trace test shows that each element of B has the same action
on D as an element of H. Thus normalization of S ∩ D by H passes to B.
No faithfulness of the ambient action is needed for this argument.

Both action-realization hypotheses are explicit. This module does not identify
a subgroup bearing an inner-diagonal label with a group of inner automorphisms,
nor assert that a raw source field subgroup already has the chosen coordinates.
Those statements must be proved from the source configuration before this
reduction establishes the source theorem.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.15(5), printed
pp.50–51, and its use for B ≤ D in Proposition 1.3.4, printed p.511.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieAutomorphismExtensions
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
variable {J E : Type*} [Group J] [Field E] [CharP E 2]
variable (D : Subgroup J) [D.Normal]

theorem modelAction_field_cartan (e : D ≃* Model E)
    (B F H : Subgroup J) (hBD : B ≤ D)
    (hprod : ∀ b ∈ B, ∃ f ∈ F, ∃ h ∈ H, b = f * h)
    (hF : ∀ f ∈ F, ∃ σ : E ≃+* E, modelAction D e f = fieldAction σ)
    (hH : ∀ h ∈ H, ∃ d : Model E, modelAction D e h = MulAut.conj d) :
    ∀ b ∈ B, ∃ h ∈ H, modelAction D e b = modelAction D e h := by
  intro b hb
  obtain ⟨f, hf, h, hh, he⟩ := hprod b hb
  obtain ⟨σ, hσ⟩ := hF f hf
  obtain ⟨d, hd⟩ := hH h hh
  have hmul : fieldAction σ * MulAut.conj d = MulAut.conj (e ⟨b, hBD hb⟩) := by
    rw [← hσ, ← hd, ← map_mul, ← he]
    exact modelAction_inner D e ⟨b, hBD hb⟩
  have hfield : fieldAction σ = MulAut.conj (e ⟨b, hBD hb⟩ * d⁻¹) := by
    rw [map_mul, map_inv]
    exact eq_mul_inv_of_mul_eq hmul
  have hσ1 := fieldAction_eq_conj_implies_one σ _ hfield
  refine ⟨h, hh, ?_⟩
  rw [he, map_mul, hσ, hσ1, map_one, one_mul]

theorem normalizes_sylow_of_field_cartan (e : D ≃* Model E)
    (S B F H : Subgroup J) (hBD : B ≤ D)
    (hprod : ∀ b ∈ B, ∃ f ∈ F, ∃ h ∈ H, b = f * h)
    (hHN : H ≤ normalizer (S ⊓ D : Subgroup J))
    (hF : ∀ f ∈ F, ∃ σ : E ≃+* E, modelAction D e f = fieldAction σ)
    (hH : ∀ h ∈ H, ∃ d : Model E, modelAction D e h = MulAut.conj d) :
    B.subgroupOf D ≤ normalizer (S.subgroupOf D) := by
  apply le_normalizer_iff.mpr
  intro b hb x hx
  obtain ⟨h, hh, he⟩ := modelAction_field_cartan D e B F H hBD hprod hF hH b hb
  have he' := MulEquiv.congr_fun he (e x)
  rw [modelAction_apply, modelAction_apply] at he'
  have he'' := congrArg Subtype.val (e.injective he')
  change (b : J) * (x : J) * (b : J)⁻¹ ∈ S
  change (b : J) * (x : J) * (b : J)⁻¹ = h * (x : J) * h⁻¹ at he''
  rw [he'']
  exact ((mem_normalizer_iff.mp (hHN hh) (x : J)).mp ⟨hx, x.property⟩).1

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
