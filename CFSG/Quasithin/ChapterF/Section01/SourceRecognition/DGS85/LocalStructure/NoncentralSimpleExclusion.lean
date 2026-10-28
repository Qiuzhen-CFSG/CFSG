module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SimpleReplacementOffender
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.UnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SuzukiEnlargement
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem

/-!
# Excluding noncentral replacement sections for simple nonlinear models

Under the contrary normality of Q_delta intersect Q_lambda, a noncentral
Z_lambda would give the genuine replacement offender on the enlarged
quotient. For nondegenerate Suzuki and projective-unitary models, the
quotient is simple, so the preceding construction proves faithfulness
and preserves the offender index. The proved quadratic square bound
then contradicts the original maximum-abelian upper bound.

Thus these rows force Z_lambda to centralize X=<Q_delta^G_lambda>.
No Sylow assertion about Q_delta, linear-model selection, or conclusion
for the central branch is assumed. Sz(2), degree-one unitary groups and
nontrivial special-unitary central covers remain separate cases.

Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121, using the
quadratic bounds in corrected 5.12, pp.113--115. The square inequalities
used here do not require a fixed-generation assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The simple Suzuki rows exclude the noncentral neighboring-center case of the contrary-normality argument. -/
theorem source_suzuki_neighbor_center_central (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    {m : ℕ} (hm : 0 < m)
    (e : (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* SuzukiMatrixGroup m) :
    sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G) := by
  by_contra hnc
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨W,hW,hWM,hWf,ρ,hf,_,f,_,_,_,_,U,C,_,_,A,_,_,hp,hquad,hnon,hbound⟩ :=
    source_simple_replacement_offender h hB hS i d hn hnc q hq hk
  let := hW
  let := hWM
  let := hWf
  obtain ⟨T,hAT⟩ := hp.exists_le_sylow
  have hsquare := suzuki_all_square_bound m ρ hf T _ hAT hquad
  have hh := hsquare.trans hbound
  nlinarith

/-- Every projective-unitary row with fixed-field order greater than two excludes the same noncentral case. -/
theorem source_projective_unitary_neighbor_center_central (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G) := by
  by_contra hnc
  have hgt : 2 < 2^n := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hnpos
    norm_num at hh
    omega
  have hfixed : Nat.card {x : F // J.conj x=x} = 2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  let := BenderSuzuki.External.huppert_II_10_13 J (2^n) hgt hcard hfixed
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨W,hW,hWM,hWf,ρ,hf,hfix,f,_,_,_,_,U,C,_,_,A,_,_,_,hquad,hnon,hbound⟩ :=
    source_simple_replacement_offender h hB hS i d hn hnc q hq hk
  let := hW
  let := hWM
  let := hWf
  have hsquare := (psu3_all_quadratic_bounds J (by omega : 0 < n) hcard hconj ρ hf hfix _ hquad).2
  have hh := hsquare.trans hbound
  nlinarith
end CFSG.Quasithin.ChapterF.Source.DGS85
