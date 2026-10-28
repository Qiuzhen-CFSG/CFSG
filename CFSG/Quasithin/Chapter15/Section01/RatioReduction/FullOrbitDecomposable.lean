module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitMarkings
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.TwoFactorDecomposition
/-!
# The decomposable full-orbit branch of original 15.1.2

The original SQTK cover bounds a transitive nonsingleton ratio decomposition
by two factors and forces their odd kernels to be cyclic. Their marked D.2.17
endpoints have a common prime and support dimension. The literal embedded
actors form a direct product, their supports are complementary, and an element
of the original Sylow subgroup exchanges the two factors.

All decomposition and permutation data stay on the selected M-action; no
normality of an orbit kernel or quotient rank bound is assumed.

Source: Aschbacher--Smith 15.1.2(3), printed p.1084, paragraph two, and
p.1086, final paragraph.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_full_orbit_decomposable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let f := (actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull → U = ⊤ →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (∀ i j, ∃ g : D, π g i = j) → 1 < Nat.card d.Index →
      Nat.card d.Index = 2 ∧ ∃ p m, CyclicSource.PrimeDimensionOptions p m ∧
        (∀ i, ∃ l : CyclicSource.LocalGeneration (d.factor i).action,
          CyclicSource.DihedralMarking l p m) ∧
        ∃ i j : d.Index, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
          (c.ambientFactor d i).actor ⊔ (c.ambientFactor d j).actor = Jhat ρ ∧
          Disjoint (c.ambientFactor d i).actor (c.ambientFactor d j).actor ∧
          (∀ x ∈ (c.ambientFactor d i).actor,
            ∀ y ∈ (c.ambientFactor d j).actor, Commute x y) ∧
          IsCompl (c.ambientFactor d i).space (c.ambientFactor d j).space ∧
          ∃ t : M, (t : G) ∈ (T : Subgroup G) ∧ π (f t) i = j ∧ π (f t) j = i := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let Q := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  dsimp only
  intro U c d hd hU π hp hs ht hmore
  obtain ⟨hc,p,m,hpm,hmark⟩ := source_localAction_transitive_uniform_dihedral
    hG T hempty hM hmany hJ U c d hd π hp hs ht hmore
  obtain ⟨i,j,hij,hall,ha,hdis,hcom,hsp⟩ := c.two_factor_literal_decomposition d hU hc
  obtain ⟨t,htmem,htij⟩ := c.transitive_pair_sylow d π hs ht hc Q i j
  have htji : π t j = i := by
    rcases hall (π t j) with h | h
    · exact h
    · exact False.elim (hij ((π t).injective (htij.trans h.symm)))
  obtain ⟨a,haT,hat⟩ := htmem
  refine ⟨hc,p,m,hpm,hmark,i,j,hij,hall,ha,hdis,hcom,hsp,a,haT,?_,?_⟩
  · change π (f a) i = j
    exact hat ▸ htij
  · change π (f a) j = i
    exact hat ▸ htji
end CFSG.Quasithin.Chapter15.Section01
