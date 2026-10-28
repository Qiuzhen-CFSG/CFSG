module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitCyclic
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.CyclicKernelEndpoints
/-!
# The original decomposable full orbit has two cyclic dihedral factors

The genuine cyclic source witness supplies a moving involution on its
prime core. Applying the original SQTK cover's rank-two orbit theorem to
the canonical embedded prime cores gives exactly two factors and cyclic
cores. The original marked kernels are therefore cyclic and their D.2.17
endpoints are precisely case (1) or (2).

Source: Aschbacher--Smith 15.1.2, printed pp.1084 and 1086.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_transitive_factor_endpoints
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ i j, ∃ g : D, π g i = j) → 1 < Nat.card d.Index →
      Nat.card d.Index = 2 ∧ ∀ i, ∃ l : CyclicSource.LocalGeneration (d.factor i).action,
        letI := BinaryGroupAction.action (d.factor i).action
        letI : Finite (d.factor i).Space := Module.finite_of_finite (ZMod 2)
        letI : IsElementaryAbelian 2 (Multiplicative (d.factor i).Space) := BinaryGroupAction.elementary
        letI := l.normal
        ChapterD.Section02.CyclicThreeEndpoint (V := Multiplicative (d.factor i).Space)
          l.kernel l.involution ∨
          ChapterD.Section02.CyclicFiveEndpoint (V := Multiplicative (d.factor i).Space)
            l.kernel l.involution := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd π hp ht hmore
  have hlocal (i : d.Index) : Nat.card d.Index = 2 ∧
      ∃ l : CyclicSource.LocalGeneration (d.factor i).action,
        letI := BinaryGroupAction.action (d.factor i).action
        letI : Finite (d.factor i).Space := Module.finite_of_finite (ZMod 2)
        letI : IsElementaryAbelian 2 (Multiplicative (d.factor i).Space) := BinaryGroupAction.elementary
        letI := l.normal
        ChapterD.Section02.CyclicThreeEndpoint (V := Multiplicative (d.factor i).Space)
          l.kernel l.involution ∨
          ChapterD.Section02.CyclicFiveEndpoint (V := Multiplicative (d.factor i).Space)
            l.kernel l.involution := by
    obtain ⟨l⟩ := source_localAction_transitive_factor_localGeneration hG T hempty hM hmany hJ
      U c d hd π hp ht hmore i
    let : Fact l.prime.Prime := ⟨l.prime_prime⟩
    obtain ⟨hc,hcyc⟩ := c.transitive_core_bound d π hp ht hmore l.prime_odd
      f.rangeRestrict f.rangeRestrict_surjective
      ((Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1)).stronglyQuasithin
        l.prime l.prime_prime l.prime_odd)
      i l.involution l.order_two l.involution_not_centralizer_core
    exact ⟨hc,l,l.cyclic_endpoints (d.factor i).faithful (l.kernel_isCyclic_of_core (hcyc i))⟩
  exact ⟨(hlocal (Classical.arbitrary d.Index)).1,fun i => (hlocal i).2⟩
end CFSG.Quasithin.Chapter15.Section01
