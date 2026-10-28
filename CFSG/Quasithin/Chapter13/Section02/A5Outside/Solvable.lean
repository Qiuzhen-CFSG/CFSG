module

public import CFSG.Quasithin.Chapter13.Section02.A5Outside.Setup
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvableBaumann

/-!
# The solvable original outside action in 13.2.8

The previous reduction constructs the characteristic-two reduced omega
orbit and its nontrivial Thompson action. Solvable E.2.3 then constructs
one or two actual natural binary factors, permuted transitively by the
original Sylow subgroup, together with the Baumann Sylow and alpha identities.
The original centralizer has O₂(H) as its Sylow intersection; equality of
that whole centralizer with O₂(H) remains the separate argument 13.2.9.

The A₅ consumer uses the actual Context and quotient H/C_H(U). Only the
earlier 5.1.7(1) normalizer bound and 13.2.8(1) solvability are retained.
Source: Aschbacher–Smith 13.2.8, printed p.880; E.2.3(2), pp.216–217.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
universe u
variable {G : Type u} [Group G] [Finite G]

/-- One or two actual binary planes, with the original Sylow, Baumann and core data. -/
theorem solvable_omega_action {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) {M H : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced hG T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      (d.count = 1 ∨ d.count = 2) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup H)).map q = offenderSubgroup ρ ∧
      (∀ i j, ∃ t : S,
        (d.factor i).map (MulAut.conj (q t)).toMonoidHom = d.factor j) ∧
      Chapter1.IsSylowIn 2 (ChapterB.baumann (S : Subgroup H))
        (pResidual 2 H ⊔ ChapterB.baumann (S : Subgroup H)) ∧
      ChapterB.thompsonAlpha (S : Subgroup H) =
        (ChapterB.thompsonAlpha (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H)) ∧
      (S : Subgroup H) ⊓ C = pCore 2 H := by
  obtain ⟨hsq,_,hp,hU,hj⟩ := e23_hypotheses hG T hTM hH hB hZ
  let := hU.normal
  let := hU.elementary
  let := hs
  have hr := hsq.stronglyQuasithin 3 (by decide) (by decide)
  obtain ⟨d,hc,hg,ht⟩ := ChapterE.ThompsonAction.source_solvable_factors _ hp _ hU hj hr inferInstance
  obtain ⟨hb,ha⟩ := ChapterE.ThompsonAction.source_solvable_baumann_sylow_and_alpha
    _ hp _ hU hj hr inferInstance
  exact ⟨d,hc,hg,ht,hb,ha,(ChapterE.ThompsonAction.reduced_centralizer_sylow _ hp _ hU hj).1⟩

/-- Literal A₅ source application: the two earlier Chapter 5 branches are explicit. -/
theorem source_solvable_omega_action
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      (c.count = 1 ∨ c.count = 2) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup H)).map q = offenderSubgroup ρ ∧
      (∀ i j, ∃ t : S,
        (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) ∧
      Chapter1.IsSylowIn 2 (ChapterB.baumann (S : Subgroup H))
        (pResidual 2 H ⊔ ChapterB.baumann (S : Subgroup H)) ∧
      ChapterB.thompsonAlpha (S : Subgroup H) =
        (ChapterB.thompsonAlpha (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H)) ∧
      (S : Subgroup H) ⊓ C = pCore 2 H :=
  solvable_omega_action d.hypothesis.qtke T d.normalizes_L hH hB hZ hs

end CFSG.Quasithin.Chapter13.Section02.A5Outside
