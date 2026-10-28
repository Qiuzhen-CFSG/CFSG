module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PerfectReplacementSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SpecialUnitaryEnlargement

/-!
# The noncentral replacement exclusion for special-unitary covers

Restriction to the actual closure covers the full special-unitary model.
The replacement section descends on its original vectors. Perfectness
and the simple projective quotient put its action kernel in the odd scalar
kernel, which is disjoint from the original two-actor. Thus quadraticity
makes that actor elementary abelian, and the unitary square bound contradicts
its sharp Thompson index. Nontrivial cubic centers are retained throughout.

This excludes the noncentral neighboring-center case for all SU₃(2ⁿ),
n≥2. The reduced F1.11 application uses the actual enlarged quotient.
The central neighboring-center case and n=1 remain separate obligations.
Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121, and 5.12,
pp.113--115.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A full special-unitary enlarged quotient excludes the noncentral neighboring-center branch, including nontrivial cubic scalar centers. -/
theorem source_special_unitary_neighbor_center_central (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* J.specialSubgroup) :
    sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G) := by
  by_contra hnc
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
    source_perfect_replacement_section h hB hS i d hn hnc q hq hk
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
end CFSG.Quasithin.ChapterF.Source.DGS85
