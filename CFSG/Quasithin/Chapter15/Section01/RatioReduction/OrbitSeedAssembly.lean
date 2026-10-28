module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.OrbitSupports
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.OrbitSeed
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SeedAssembly

/-!
# The basic support-orbit case division in original 15.1.2

Coalescing the literal factor supports along the already constructed ambient
permutation gives one normal actor and invariant support for each orbit.
If one such support fills the module, independence forces a transitive factor
orbit and V=V₀. Otherwise every orbit support is proper, and the ordering
obstruction shows that its intersection with the original central seed has
proper orbit span under its own actor.

The final theorem constructs the factor datum, fully Fitting-moved decomposition
and ambient permutation from the original selected-action hypotheses. It keeps
the actual source partner Mc and its uniqueness hypothesis, needed by A.5.6.

Source: Aschbacher--Smith 15.1.2, basic case division, printed p.1085.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_orbit_seed_cases
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation) (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j) ∨
        ∀ i, Homogeneous.orbitSpan ρ (c.orbitActor d π i) (Z ⊓ c.orbitSpace d π i) <
          c.orbitSpace d π i := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d π hp
  by_cases ht : U = ⊤ ∧ ∀ i j, ∃ g, π g i = j
  · exact Or.inl ht
  · apply Or.inr
    intro i
    let := c.orbitActor_normal d π hp i
    apply source_localAction_proper_seed_span hG T hempty hM hJ hu hne
      (c.orbitActor d π i) (c.orbitSpace d π i)
      (c.orbitSpace_invariant d π hp i) (c.orbitSpace_ne_bot d π i)
    · intro he
      exact ht ((c.orbitSpace_eq_top_iff_transitive d π i).mp he)
    · exact c.orbitSpace_fixed_complement d π i

/-- The basic source alternative on the actual original partition: one full
orbit, or a proper span of the central seed in every orbit support. -/
theorem source_centralizing_orbit_seed_cases
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
    ∃ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation) (π : D →* Equiv.Perm d.Index),
      d.FittingFull ∧
      (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ Jhat ρ ≤ π.ker ∧
      (∀ g i,
        Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
        (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor ∧
        (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space) ∧
      ((U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j) ∨
        ∀ i, Homogeneous.orbitSpan ρ (c.orbitActor d π i) (Z ⊓ c.orbitSpace d π i) <
          c.orbitSpace d π i) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  obtain ⟨U,c,d,hd,π,hstars,hker,hp⟩ :=
    source_centralizing_classified_partition hG T hempty hM hmany hJ
  exact ⟨U,c,d,π,hd,hstars,hker,hp,
    source_localAction_orbit_seed_cases hG T hempty hM hJ hu hne U c d π (fun g i => (hp g i).2.1)⟩

end CFSG.Quasithin.Chapter15.Section01
