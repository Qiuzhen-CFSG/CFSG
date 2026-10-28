module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.Inputs
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Defs
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.SpecificGroups.SU3.FourActorInvolutionConjugacy
public import Theory.SpecificGroups.SU3.OddInvolutionNormalization
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Four conjugates for involutory automorphisms of PSU₃(5)

For inner actors, identify the arbitrary Hermitian model with the concrete
identity-Gram GF(25) model. Simplicity makes its inner conjugation faithful
as soon as the given inner actor is nonidentity. Projective involution
fusion puts each of the three generators of a maximal embedded A₇ in the
actor's class; a fourth conjugate then generates the group.

For outer actors, use the normalization valid for every odd prime to obtain
entrywise conjugation on an antidiagonal model. Three literal inner
conjugates generating a maximal embedded S₇ need one more conjugate to
cover the inner group. Both branches transport the actual conjugators
back through the specified equivalence.

The concrete A₇ and S₇ model theorems supply the embeddings, maximality
and generating triples. The final `fourBoundAtFive` discharges both model
inputs, retaining only the field, conjugation and inherited simplicity
hypotheses of `FourBoundAtFive`. The conditional assembly remains available.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem inner_standard_of_model (hinner : InnerModel)
    [IsSimpleGroup StandardGroup] (a : MulAut StandardGroup)
    (ha : a ≠ 1) (ha2 : a ^ 2 = 1) (hi : ∃ x, a = MulAut.conj x) :
    MulAut.HasInnerConjugateCover a 4 := by
  obtain ⟨x, rfl⟩ := hi
  have hinj : Function.Injective (MulAut.conj : StandardGroup →* MulAut StandardGroup) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (inferInstance : (MulAut.conj : StandardGroup →* MulAut StandardGroup).ker.Normal).eq_bot_or_eq_top
      with h | h
    · exact h
    · exact False.elim (ha (show x ∈ (MulAut.conj : StandardGroup →* MulAut StandardGroup).ker
        from h ▸ mem_top x))
  have hx : orderOf x = 2 := by
    rw [← orderOf_injective _ hinj]
    exact orderOf_eq_prime ha2 ha
  obtain ⟨f, hf, hm, t, ht2, ht⟩ := hinner
  have hconj : ∀ i, ∃ s : StandardGroup, s * x * s⁻¹ = f (t i) := by
    intro i
    apply isConj_iff.mp
    exact Matrix.SU3.projective_involutions_isConj (p := 5) (by decide)
      (GaloisField.card 5 (2 * 1) (by decide)) standardForm rfl
      (by intro z; simp only [standardForm, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one])
      x (f (t i)) hx ((orderOf_injective f hf _).trans (ht2 i))
  choose s hs using hconj
  have hclosure : closure (Set.range fun i => s i * x * (s i)⁻¹) = f.range := by
    have he : (fun i => s i * x * (s i)⁻¹) = f ∘ t := funext hs
    rw [he, Set.range_comp, ← MonoidHom.map_closure, ht]
    exact (MonoidHom.range_eq_map f).symm
  apply MulAut.hasInnerConjugateCover_conj_of_coatom x (by
    intro he
    simp [he] at ha) s
  rwa [hclosure]

private theorem outer_normalized_of_model (houter : OuterModel)
    {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hcard : Nat.card E = 5 ^ 2) (hc : ∀ x, J.conj x = x ^ 5)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ≠ 1) (ha2 : a ^ 2 = 1) (hgraph : J.IsEntrywiseConjugation a) :
    MulAut.HasInnerConjugateCover a 4 := by
  obtain ⟨f, _hf, hm, t, ht, hs⟩ := houter J hcard hc hJ a ha ha2 hgraph
  choose s hs using hs
  have he : closure (Set.range fun i => MulAut.conj (s i) * a * (MulAut.conj (s i))⁻¹) =
      f.range := by
    have he : (fun i => MulAut.conj (s i) * a * (MulAut.conj (s i))⁻¹) =
        f ∘ t := funext hs
    rw [he, Set.range_comp, ← MonoidHom.map_closure, ht]
    exact (MonoidHom.range_eq_map f).symm
  exact MulAut.hasInnerConjugateCover_of_covBy a ha s (he.symm ▸ hm)

/-- Conditional source assembly: the concrete A₇ and S₇ calculations remain
explicit; arbitrary forms, inner fusion, outer normalization and the fourth
conjugate are supplied here. -/
theorem fourBoundAtFive_of_models (hinner : InnerModel) (houter : OuterModel) :
    FourBoundAtFive.{0} := by
  intro E _ _ J _ hcard hc a ha ha2
  by_cases hi : ∃ x, a = MulAut.conj x
  · obtain ⟨e⟩ := Matrix.SU3.InnerThreeRank.exists_projective_equiv_standard 5 E J hcard hc
    let : IsSimpleGroup StandardGroup := e.symm.isSimpleGroup
    have hb : MulAut.HasInnerConjugateCover (MulAut.congr e a) 4 :=
      inner_standard_of_model hinner (MulAut.congr e a)
        (by intro h; apply ha; apply (MulAut.congr e).injective; simpa only [map_one] using h)
        (by rw [← map_pow, ha2, map_one]) ((MulAut.congr_inner_iff e a).mpr hi)
    have hh := hb.congr e.symm
    have he : MulAut.congr e.symm (MulAut.congr e a) = a := by
      ext x
      simp [MulAut.congr]
    rwa [he] at hh
  · have hfixed : Nat.card {x : E // J.conj x = x} = 5 := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
        J.conj 5 1 (by decide) (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hc)
    obtain ⟨J₀, e, hconj, hform, hgraph⟩ := OddInvolutionNormalization.normalized_outer
      J (by decide : Nat.Prime 5) (by decide : Odd 5) hcard hfixed a ha2 hi
    let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := e.symm.isSimpleGroup
    have hc₀ : ∀ x, J₀.conj x = x ^ 5 := by rw [hconj]; exact hc
    have hb := outer_normalized_of_model houter J₀ hcard hc₀ hform (MulAut.congr e a)
      (by intro h; apply ha; apply (MulAut.congr e).injective; simpa only [map_one] using h)
      (by rw [← map_pow, ha2, map_one]) hgraph
    have hh := hb.congr e.symm
    have he : MulAut.congr e.symm (MulAut.congr e a) = a := by
      ext x
      simp [MulAut.congr]
    rwa [he] at hh
end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five

namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds

/-- Every nonidentity involutory automorphism of PSU₃(5) has four conjugates
by actual elements of PSU₃(5) whose closure contains all inner automorphisms.
This includes both inner and outer actors over every allowed Hermitian form. -/
theorem fourBoundAtFive : FourBoundAtFive.{0} :=
  Five.fourBoundAtFive_of_models Five.innerModel Five.outerModel

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds
