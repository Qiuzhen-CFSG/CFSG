module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Consequences
public import CFSG.Quasithin.Chapter3.Section02.LocalModule
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedSpace

/-!
# The original full module in the chosen natural preliminaries

Apply the proved Fundamental Setup consequences to the unchanged chosen seed.
The maximal local is exactly N_G(L) and its full module is exactly the
normalizer orbit of V. This proves reducedness and commutator generation,
and identifies the full fixed space as the orbit of C_V(L). A nonzero fixed
space gives the actual Thompson commutator using the multiple-overgroup guard.
The conditional TI application isolates only normalizer invariance in that
nonzero-fixed-space branch; it does not assert that missing source conclusion.

Source: Aschbacher--Smith, 11.0.3(1,3,4), printed p.760, using
3.2.2(2,4,6,8) and 3.2.3, printed pp.579--580.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1

/-- The maximal local in the source is the literal normalizer of L. -/
theorem normalizer_maximal : IsMaximalTwoLocal (normalizer (L : Set G)) := by
  have h := ((D.fundamentalSetup S.source.toHypothesis1221).lemma_3_2_3_uniqueness
    (uniqueness D S)).1
  change IsMaximalTwoLocal (normalizer (Chapter3.Section02.localOrbit T L : Set G)) at h
  rwa [D.localOrbit_eq] at h

/-- The source H-star comparison exists for the same literal normalizer. -/
theorem exists_HStar : ∃ H : Subgroup G,
    H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
  Chapter3.exists_HStar_of_hasMaximalOutside
    (S.outside_of_many _ (normalizer_maximal D S) D.sylow_normalizes_component)

/-- Source 11.0.3(1): the full normalizer orbit belongs to R₂(M). -/
theorem fullModule_reduced :
    IsPReduced 2 ((componentOrbit V (normalizer (L : Set G))).subgroupOf
      (normalizer (L : Set G))) :=
  D.normalizerOrbit_reduced S.source.toHypothesis1221
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))

/-- The full module is elementary abelian, with no model or splitting premise. -/
theorem fullModule_elementary :
    IsElementaryAbelian 2 (componentOrbit V (normalizer (L : Set G))) := by
  have h := (D.fundamentalSetup S.source.toHypothesis1221).fullModule_elementary
    (uniqueness D S)
  rwa [D.fundamentalSetup_fullModule] at h

/-- The original V, identified by the unchanged-seed theorem, is reduced in LT. -/
theorem seed_reduced : IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) := by
  have h := (D.fundamentalSetup S.source.toHypothesis1221).module_reduced (uniqueness D S)
  rw [S.unchanged_seed] at h
  change IsPReduced 2 (V.subgroupOf
    (Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G))) at h
  rwa [D.localOrbit_eq] at h

/-- Commutator generation holds on the full orbit, not just on the seed. -/
theorem fullModule_eq_commutator :
    componentOrbit V (normalizer (L : Set G)) =
      ⁅componentOrbit V (normalizer (L : Set G)), L⁆ :=
  D.normalizerOrbit_eq_commutator S.source.toHypothesis1221
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))

/-- The central part of the full module is the M-orbit of the original central part. -/
theorem fullModule_centralizer :
    componentOrbit V (normalizer (L : Set G)) ⊓ centralizer (L : Set G) =
      componentOrbit (V ⊓ centralizer (L : Set G)) (normalizer (L : Set G)) := by
  have h := (D.fundamentalSetup S.source.toHypothesis1221).fullModule_centralizer_eq_seed_orbit
    (uniqueness D S)
  rw [D.fundamentalSetup_fullModule, D.fundamentalSetup_seed, D.localOrbit_eq] at h
  change componentOrbit V (normalizer (L : Set G)) ⊓ centralizer (L : Set G) =
    componentOrbit (V ⊓ centralizer (L : Set G))
      (normalizer (Chapter3.Section02.localOrbit T L : Set G)) at h
  rwa [D.localOrbit_eq] at h

/-- Vanishing on V is equivalent to vanishing on its entire normalizer orbit. -/
theorem fullModule_centralizer_eq_bot_iff :
    componentOrbit V (normalizer (L : Set G)) ⊓ centralizer (L : Set G) = ⊥ ↔
      V ⊓ centralizer (L : Set G) = ⊥ := by
  constructor
  · intro h
    exact le_bot_iff.mp ((inf_le_inf_right _ (le_componentOrbit V _)).trans h.le)
  · intro h
    rw [fullModule_centralizer D S, h]
    exact iSup_eq_bot.mpr (fun _ => Subgroup.map_bot _)

/-- The nonzero central branch forces the original Thompson commutator. -/
theorem thompson_commutator_of_centralizer_ne_bot
    (hc : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hf : (D.fundamentalSetup S.source.toHypothesis1221).seed ⊓
      centralizer (Chapter3.Section02.localOrbit T L : Set G) ≠ ⊥ := by
    rwa [D.fundamentalSetup_seed, D.localOrbit_eq]
  have h := ((D.fundamentalSetup S.source.toHypothesis1221).fixedSpace_consequences_of_many
    S.many hf).1
  rwa [D.localOrbit_eq] at h

/-- The fixed-free branch of source 11.0.3(4), with all earlier premises proved. -/
theorem ti_of_centralizer_eq_bot (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (g : G) (hg : g ∈ normalizer (L : Set G)) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V :=
  D.ti_of_centralizer_eq_bot S.source.toHypothesis1221
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hc g hg

/-- The actual TI consumer of the separate nonzero-fixed-space invariance result.
The assembly owner must discharge that earlier implication. -/
theorem ti_of_fixedSpace_invariance
    (hi : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ →
      V ⊓ centralizer (L : Set G) ≠ ⊥ →
      componentOrbit V (normalizer (L : Set G)) = V)
    (g : G) (hg : g ∈ normalizer (L : Set G)) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V := by
  by_cases hc : V ⊓ centralizer (L : Set G) = ⊥
  · exact ti_of_centralizer_eq_bot D S hc g hg
  · have he := hi (thompson_commutator_of_centralizer_ne_bot D S hc) hc
    have hn := he ▸ le_normalizer_componentOrbit V (normalizer (L : Set G))
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hn hg))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
