module

public import CFSG.Quasithin.Chapter3.Section02.FundamentalModule
public import CFSG.Quasithin.Chapter3.Section02.ReducedAmbient
public import Theory.GroupTheory.ReducedNormal.SubspaceGroupConsequences
public import Theory.GroupTheory.ReducedNormal.SubspaceQuotientConsequences

/-!
# The actual FSU module: conclusions 3.2.2(3)–(5)

The genuine internal seed identifies its full ambient orbit with the
original V_M. The linear orbit results give full commutator generation,
both centralizer-orbit identities, and the seed's TI alternative as
identities of the original subgroups. The literal quotient V_M/C_VM(L₀)
with original M-conjugation is semisimple for L₀, and M acts transitively
on its homogeneous components.

The only preceding source input is the established 1.2.7 uniqueness
conclusion, supplied under genuine Theorems A and C by SourceUniqueness.
No part of the module conclusions is a premise.

Source: Aschbacher–Smith, Lemma 3.2.2(3)–(5), combined manuscript of
1 March 2004, printed p.579.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- Source 3.2.2(3), for the actual FSU group V_M. -/
theorem fullModule_eq_commutator
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    D.fullModule = ⁅D.fullModule, localOrbit T L⁆ := by
  obtain ⟨J, hJ, hW, hi⟩ := D.exists_internal_seed h127
  let := hi.normal
  have he := ReducedNormal.seedOrbit_eq_commutator D.maximalLocal (localOrbit T L)
    (localOrbit T L).le_normalizer hi.seed
  rw [hJ, ← D.fullModule_eq_seed_orbit] at he
  exact he

/-- Source 3.2.2(4), first equality, with original FSU subgroups. -/
theorem fullModule_centralizer_eq_seed_orbit
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) =
      componentOrbit (D.seed ⊓ centralizer (localOrbit T L : Set G)) D.maximalLocal := by
  obtain ⟨J, hJ, hW, hi⟩ := D.exists_internal_seed h127
  let := hi.normal
  have he := ReducedNormal.seedOrbit_inf_centralizer D.maximalLocal (localOrbit T L)
    (localOrbit T L).le_normalizer hi.seed
  rw [hJ, ← D.fullModule_eq_seed_orbit] at he
  exact he

/-- Source 3.2.2(4), second equality, for V = ⟨V◦ᵀ⟩. -/
theorem fullModule_centralizer_eq_module_orbit
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) =
      componentOrbit (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G)) D.maximalLocal := by
  apply le_antisymm
  · rw [D.fullModule_centralizer_eq_seed_orbit h127]
    exact iSup_le fun g => (map_mono (inf_le_inf_right _ (le_componentOrbit D.seed T))).trans
      (le_iSup (fun g : D.maximalLocal =>
        (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G)).map
          (MulAut.conj (g : G)).toMonoidHom) g)
  · apply iSup_conjugates_le_of_le_normalizer _ _ _
      (inf_le_inf_right _ (le_componentOrbit D.moduleSubgroup D.maximalLocal))
    exact (le_inf D.maximalLocal_normalizes_fullModule
      (normalizer_le_normalizer_centralizer (localOrbit T L))).trans
        inf_normalizer_le_normalizer_inf

/-- Source 3.2.2(5): a seed with trivial relative centralizer is TI under M. -/
theorem seed_ti_under_maximalLocal
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    (hc : D.seed ⊓ centralizer (localOrbit T L : Set G) = ⊥) (g : D.maximalLocal) :
    D.seed ⊓ D.seed.map (MulAut.conj (g : G)).toMonoidHom = ⊥ ∨
      D.seed.map (MulAut.conj (g : G)).toMonoidHom = D.seed := by
  obtain ⟨J, hJ, hW, hi⟩ := D.exists_internal_seed h127
  let := hi.normal
  have he := ReducedNormal.seed_ti_of_centralizer_eq_bot D.maximalLocal (localOrbit T L)
    (localOrbit T L).le_normalizer hi.seed (by rwa [hJ]) g
  rwa [hJ] at he

/-- Source 3.2.2(3): the actual quotient V_M/C_{V_M}(L₀), with its
original M-conjugation, is semisimple for L₀ and has transitive homogeneous components. -/
theorem fullModule_quotient_consequences
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    letI := D.fullModule_elementary h127
    ∃ σ : Representation (ZMod 2) D.maximalLocal
        (Additive (D.fullModule ⧸
          (centralizer (localOrbit T L : Set G)).subgroupOf D.fullModule)),
      Representation.IsSemisimpleRepresentation
        (σ.comp ((localOrbit T L).subgroupOf D.maximalLocal).subtype) ∧
      (∀ (A B : Subrepresentation
          (σ.comp ((localOrbit T L).subgroupOf D.maximalLocal).subtype)),
        Representation.IsIrreducible A.toRepresentation →
        Representation.IsIrreducible B.toRepresentation →
        ∃ g : D.maximalLocal, (homogeneousPart A ⊤).map (σ g) = homogeneousPart B ⊤) ∧
      (∀ (g : D.maximalLocal) (v : D.fullModule),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (localOrbit T L : Set G)).subgroupOf D.fullModule) v)) =
        Additive.ofMul (QuotientGroup.mk'
          ((centralizer (localOrbit T L : Set G)).subgroupOf D.fullModule)
          ⟨(g : G) * (v : G) * (g : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule g.property) v).mp
              v.property⟩)) := by
  let := D.fullModule_elementary h127
  obtain ⟨J, hJ, hW, hi⟩ := D.exists_internal_seed h127
  let := hi.normal
  exact ReducedNormal.exists_actual_quotient_consequences D.maximalLocal
    (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J)
    (orbitSpan_invariant _ ⊤ J) (localOrbit T L) (localOrbit T L).le_normalizer
    hi.seed rfl D.fullModule hW D.maximalLocal_normalizes_fullModule

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
