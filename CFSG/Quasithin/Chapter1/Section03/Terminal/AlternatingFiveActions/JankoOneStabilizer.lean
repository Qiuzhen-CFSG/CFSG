module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Janko1.Model.Certification.AbelianSylow
public import Theory.SpecificGroups.AlternatingFiveInnerNormalizer
public import Theory.GroupTheory.InnerStabilizerAction

/-!
# The J₁ automorphism stabilizer of an actual A₅ subgroup

The completed matrix certificates make every automorphism of J₁ inner.
An automorphism preserving A is therefore conjugation by an element of
N_J₁(A). The explicit J₁ Sylow certificate makes every two-subgroup abelian,
so the A₅ normalizer-action theorem supplies a conjugator lying in A itself.

This is the J₁ exclusion in the final paragraph of Aschbacher–Smith,
Lemma 1.3.9, printed p.514, for the actual A₅ inclusion listed in
Proposition A.3.12(15), printed p.47. There are no extra model premises.
-/

namespace CFSG.Quasithin.Chapter1.Terminal

/-- Every automorphism of the actual J₁ model stabilizing an A₅ subgroup
acts on that subgroup by conjugation by one of its own elements. -/
public theorem janko_one_alternatingFive_hasInnerStabilizerAction
    (A : Subgroup Janko1.Model) (hA : Nonempty (A ≃* alternatingGroup (Fin 5))) :
    A.HasInnerStabilizerAction := by
  intro α hα
  obtain ⟨g, rfl⟩ := Janko1.OuterCertificate.aut_inner α
  have hg : g ∈ Subgroup.normalizer (A : Set Janko1.Model) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hα
  obtain ⟨e⟩ := hA
  obtain ⟨a, ha⟩ := Subgroup.alternatingFive_normalizerAction_inner
    Janko1.two_subgroup_isMulCommutative A e ⟨g, hg⟩
  refine ⟨a, a.property, fun x hx => ?_⟩
  exact congrArg Subtype.val (congrArg (fun β : MulAut A => β ⟨x, hx⟩) ha)

end CFSG.Quasithin.Chapter1.Terminal
