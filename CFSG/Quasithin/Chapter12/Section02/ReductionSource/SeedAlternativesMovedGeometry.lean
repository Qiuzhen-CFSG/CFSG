module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesAssembly
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedGeometry

/-!
# Geometric clauses of the moved chosen-seed alternative

Every moved T-conjugate of the actual chosen seed is nonisomorphic for the
unchanged L-action, by homogeneous selection in R₂(LT). The original TI
result makes it disjoint when the seed has trivial L-centralizer. That
trivial centralizer propagates to the full N_G(L)-orbit, so the central
quotients in D.3.10 are the literal modules in this branch.

The conditional assembly derives these clauses and leaves two genuine
source obligations: the local D.3.5 model with its two-summand Sylow orbit,
and the full normalizer-orbit equality proved in D.3.12--19. Their precise
shared local conclusion is `SylowMovedModel`, which asserts no theorem.
The final application feeds the existing Chapter 12 source325 assembly;
it is not a proof of either remaining classification obligation.

Source: Aschbacher--Smith A.1.40--42, D.3.5, D.3.10--19 and3.2.5,
combined manuscript of 1 March 2004, printed pp.31--32,195--204 and580.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The local D.3.5 conclusion on the actual chosen seed. This proposition
specifies the classifier's output; it does not assert that the output holds. -/
def SylowMovedModel (D : ChosenModule T L V) : Prop :=
  ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) ∧
  ∃ t ∈ (T : Subgroup G), t ∉ normalizer (V : Set G) ∧
    componentOrbit V (T : Subgroup G) = V ⊔ V.map (MulAut.conj t).toMonoidHom

omit [Finite G] in
/-- Homogeneous selection rules out an isomorphism with every moved
T-conjugate for the original, unchanged L-conjugation action. -/
theorem moved_conjugate_not_sameModule (D : ChosenModule T L V)
    {t : G} (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G)) :
    ¬ SameConjugationModule L V (V.map (MulAut.conj t).toMonoidHom) := by
  intro he
  let H := L ⊔ (T : Subgroup G)
  let t' : (T : Subgroup G).subgroupOf H := ⟨⟨t, (le_sup_right : (T : Subgroup G) ≤ H) ht⟩, ht⟩
  have he' : SameConjugationModule L (ReducedNormal.subspaceImage H D.space)
      ((ReducedNormal.subspaceImage H D.space).map (MulAut.conj t).toMonoidHom) := by
    change SameConjugationModule L (subspaceImage H D.space)
      ((subspaceImage H D.space).map (MulAut.conj t).toMonoidHom)
    rwa [D.image_eq]
  have hs := homogeneous_conjugate_eq_of_sameConjugationModule H L le_sup_left
    ((T : Subgroup G).subgroupOf H) D.space D.irrPlus t' he'
  change (subspaceImage H D.space).map (MulAut.conj t).toMonoidHom =
    subspaceImage H D.space at hs
  rw [D.image_eq] at hs
  exact hnt (mem_normalizer_iff_map_conj_eq.mpr hs)

/-- Every actual moved conjugate is disjoint from the fixed-free seed. -/
theorem moved_conjugate_inf_eq_bot (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G)) :
    V ⊓ V.map (MulAut.conj t).toMonoidHom = ⊥ := by
  apply (D.ti_of_centralizer_eq_bot h
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hc t
    (D.sylow_normalizes_component ht)).resolve_right
  intro he
  exact hnt (mem_normalizer_iff_map_conj_eq.mpr he)

/-- Proper Sylow orbit supplies an actual moved, disjoint, nonisomorphic
conjugate before any model classification or orbit-size bound is proved. -/
theorem exists_moved_conjugate_geometry (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (V : Set G) ∧
      V ⊓ V.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      ¬ SameConjugationModule L V (V.map (MulAut.conj t).toMonoidHom) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (V : Set G) := by
    intro hn
    exact (not_le_of_gt hm)
      (iSup_conjugates_le_of_le_normalizer V T V le_rfl hn)
  obtain ⟨t,ht,hnt⟩ := Set.not_subset.mp hn
  exact ⟨t,ht,hnt,D.moved_conjugate_inf_eq_bot h hc ht hnt,
    D.moved_conjugate_not_sameModule ht hnt⟩

/-- Fixed-freeness propagates to the full normalizer orbit, so the tilde
quotients in D.3.10 are the literal subgroups in this branch. -/
theorem normalizerOrbit_inf_centralizer_eq_bot (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    componentOrbit V (normalizer (L : Set G)) ⊓ centralizer (L : Set G) = ⊥ := by
  have he := (D.fundamentalSetup h).fullModule_centralizer_eq_seed_orbit
    (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      h.simpleQTKE T h.maximal_faithful.1)
  rw [D.fundamentalSetup_fullModule h, D.fundamentalSetup_seed h, D.localOrbit_eq, hc] at he
  simpa only [componentOrbit, Subgroup.map_bot, iSup_const] using he

/-- Assembly from the still separate D.3.5 classification and D.3.12--19
orbit equality. Disjointness and unchanged-actor nonisomorphism are proved
from the original choice, rather than required as extra inputs. -/
theorem markedDoubled_of_sylow_model_of_orbit_eq (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hmodel : ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype))
    (hpair : ∃ t ∈ (T : Subgroup G), t ∉ normalizer (V : Set G) ∧
      componentOrbit V (T : Subgroup G) = V ⊔ V.map (MulAut.conj t).toMonoidHom)
    (hfull : componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G)) :
    D.MarkedDoubled := by
  obtain ⟨t,ht,hnt,hpair⟩ := hpair
  exact ⟨hc,hmodel,t,ht,hnt,hfull,hpair,D.moved_conjugate_inf_eq_bot h hc ht hnt,
    D.moved_conjugate_not_sameModule ht hnt⟩

/-- The original Chapter 12 assembly with only the local D.3.5 model and
D.3.12--19 exhaustion still explicit in the moved branch. These are separate
source obligations; this theorem does not discharge either of them. -/
theorem source325_of_moved_inputs_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : D.NormalizerOrbitCubicBound h.toHypothesis1221)
    (hfixed : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ →
      V ⊓ centralizer (L : Set G) ≠ ⊥ →
      componentOrbit V (normalizer (L : Set G)) = V)
    (hlocal : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.SylowMovedModel)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G)) :
    D.Source325Alternatives := by
  apply D.source325_of_earlier_inputs_of_many h hmany hfull hfixed
  intro hq hfull hc hm
  obtain ⟨hmodel,hpair⟩ := hlocal hq hc hm
  exact D.markedDoubled_of_sylow_model_of_orbit_eq h.toHypothesis1221 hc hmodel hpair
    (hexhaust hq hfull hc hm ⟨hmodel,hpair⟩)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
