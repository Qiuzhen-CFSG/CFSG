module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NoncentralSimpleExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NoncentralSpecialUnitaryExclusion

/-!
# Both adjacent-core obstructions for the large nonlinear rows

The common-core centralizer argument supplies the actual elementary
replacement span in both neighboring-center branches. Its residual-moving
section carries the escaping Thompson actor with its sharp index bound.
Suzuki and unitary quadratic square bounds contradict that bound, proving
relative nonnormality. The Sylow-to-normality implication then gives the
second clause of 6.5. Full special-unitary scalar centers are retained.

These results cover Sz(2^(2m+1)) for m>0 and both unitary forms for n>=2,
without a condition on the opposite endpoint model or the completion's
finiteness. The degree-one and small Suzuki/dihedral rows remain separate.
Source: DGS, Groups and Graphs (1985), 6.4--6.5, pp.120--122, using the
square bounds underlying corrected 5.12, pp.113--115.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Both source 6.5 conclusions for the suzuki row, with either neighboring-center case. -/
theorem source_suzuki_adjacent_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    {m : ℕ} (hm : 0 < m)
    (e : (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* SuzukiMatrixGroup m) :
    (¬ localEnlargement d ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  have hnfull : ¬ P (other i) ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G) := by
    intro hn
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : q.ker = pCore 2 (localEnlargement d) := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    obtain ⟨W,hW,hWM,hWf,ρ,hf,_,f,_,_,_,_,U,C,_,_,A,_,_,hp,hquad,hnon,hbound⟩ :=
      source_simple_replacement_offender_of_inter_normal h hB hS i d hn q hq hk
    let := hW
    let := hWM
    let := hWf
    obtain ⟨T,hAT⟩ := hp.exists_le_sylow
    have hsquare := suzuki_all_square_bound m ρ hf T _ hAT hquad
    have hh := hsquare.trans hbound
    nlinarith
  exact ⟨fun hn => hnfull ((inter_core_local_normal_iff h i d).mp hn),
    core_not_sylow_of_inter_not_normal h i hnfull⟩

/-- Both source 6.5 conclusions for the projective unitary row, with either neighboring-center case. -/
theorem source_projective_unitary_adjacent_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (¬ localEnlargement d ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  have hnfull : ¬ P (other i) ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G) := by
    intro hn
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
      source_simple_replacement_offender_of_inter_normal h hB hS i d hn q hq hk
    let := hW
    let := hWM
    let := hWf
    have hsquare := (psu3_all_quadratic_bounds J (by omega : 0 < n) hcard hconj ρ hf hfix _ hquad).2
    have hh := hsquare.trans hbound
    nlinarith
  exact ⟨fun hn => hnfull ((inter_core_local_normal_iff h i d).mp hn),
    core_not_sylow_of_inter_not_normal h i hnfull⟩

/-- Both source 6.5 conclusions for the special unitary row, with either neighboring-center case. -/
theorem source_special_unitary_adjacent_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* J.specialSubgroup) :
    (¬ localEnlargement d ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  have hnfull : ¬ P (other i) ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G) := by
    intro hn
    let : Group.IsPerfect J.specialSubgroup := SU3.BinaryDegree.isPerfect_specialSubgroup J hnpos hcard hconj
    have hgt : 2 < 2^n := (by decide : 2 < 2^2).trans_le
      (Nat.pow_le_pow_right (by decide) hnpos)
    have hfixed : Nat.card {x : F // J.conj x=x} = 2^n :=
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
    let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
      BenderSuzuki.External.huppert_II_10_13 J (2^n) hgt hcard hfixed
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : q.ker = pCore 2 (localEnlargement d) := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    obtain ⟨W,hW,hWM,hWf,σ,_,hfix,hnt,f,_,_,_,_,U,C,_,_,A,_,_,hp,hquad,hnon,hbound⟩ :=
      source_perfect_replacement_section_of_inter_normal h hB hS i d hn q hq hk
    let := hW
    let := hWM
    let := hWf
    let I := (A.subgroupOf (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map f
    have hscalar : σ.ker ≤ J.specialToProjective.ker :=
      SU3.BinaryDegree.ker_le_of_perfect_central_cover J.specialToProjective
        J.specialToProjective_surjective J.specialToProjective_ker_le_center σ hnt
    have hdis : Disjoint σ.ker I := by
      apply Disjoint.mono_left hscalar
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hkI⟩ := IsPGroup.iff_card.mp hp
      rw [hkI]
      exact J.odd_card_specialToProjective_ker.coprime_two_right.pow_right k
    have hfaith : Function.Injective (σ.comp I.subtype) := by
      apply (σ.comp I.subtype).ker_eq_bot_iff.mp
      apply bot_unique
      intro a ha
      exact Subtype.ext (mem_bot.mp (hdis.le_bot ⟨ha,a.property⟩))
    let : IsElementaryAbelian 2 (⊤ : Subgroup I) :=
      elementary_of_faithful_quadratic (σ.comp I.subtype) hfaith ⊤
        (fun a _ b _ w => hquad a a.property b b.property w)
    let : IsElementaryAbelian 2 I := IsElementaryAbelian.of_surjective
      (topEquiv (G := I)).toMonoidHom (topEquiv (G := I)).surjective
    have hsquare := su3_elementary_square_bound J hnpos hcard hconj σ hnt hfix I
    have hh := hsquare.trans hbound
    nlinarith
  exact ⟨fun hn => hnfull ((inter_core_local_normal_iff h i d).mp hn),
    core_not_sylow_of_inter_not_normal h i hnfull⟩

end CFSG.Quasithin.ChapterF.Source.DGS85
