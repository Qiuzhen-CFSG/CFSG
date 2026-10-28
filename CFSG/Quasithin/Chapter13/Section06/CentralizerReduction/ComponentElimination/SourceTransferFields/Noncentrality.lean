module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.FaithfulTransfer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.SourceInputs

/-!
# Noncentrality of the checked-central conjugates, source 13.6.17

The small-index normalizer calculation and the two A.4.9 applications
construct a faithful component in the centralizer of a. Conjugation carries
the Sylow subgroup and the uniform A₅ choice together. All four clauses of
Hypothesis 13.3.1, and the §13.6 counterexample assumption, therefore hold
for the replacement. The genuine earlier 13.6.3(2) contradicts its
nonidentity central involution a.

The second theorem puts this conclusion on the literal checked Sylow map
used by the minimal-block replacement in 13.6.18. The earlier universal
A.3.9 and 13.6.3 inputs are explicit; no transfer witness or noncentrality
conclusion is assumed.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.930–931.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open A5Module ComponentSelection
open SourceContainment.RankTwo.LocalApplication
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Source 13.6.17, with the full standing hypothesis transported to the
constructed faithful component over the conjugated Sylow subgroup. -/
theorem lemma_13_6_17
    (T : Sylow 2 G) (L K : Subgroup G) (z v g : G) (a : Gv v)
    (standing : SourceHypothesis T L)
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
        cComponentLayer X = solvableResidual X)
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) z v)
    (hTK : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hvT : v ∈ T) (hv : v ^ 2 = 1)
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hag : (a : G) = MulAut.conj g z)
    (ha : checkedQuotientMap v a ∈ centralizer
      (checkedImage v (Tv (T : Subgroup G) v) : Set (Gcheck v))) :
    ¬ K ≤ centralizer ({(a : G)} : Set G) := by
  intro hKa
  obtain ⟨ha1, haz, K₁, hfaith, hK₁a, hA5, hchoice⟩ :=
    exists_faithful_component_of_checked_centralizes standing.qtke hA39 T L K z v g a
      standing.a5 standing.five_minimal hK hTK hSylow hidx hvT hv hz hz1 hf hag ha hKa
  let Tg := T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hreplacement : SourceHypothesis Tg K₁ := {
    qtke := standing.qtke
    local_component := hfaith
    no_larger_field := standing.no_larger_field
    no_linear := standing.no_linear
    no_alternating_nine := standing.no_alternating_nine
    no_sporadic := standing.no_sporadic
    five_minimal := hchoice
    a5 := hA5
    counterexample := standing.counterexample }
  have hac : (a : G) ∈ centralizer (K₁ : Set G) :=
    mem_centralizer_iff.mpr fun k hk => mem_centralizer_singleton_iff.mp (hK₁a hk)
  exact ha1 (mem_bot.mp ((h63 Tg K₁ hreplacement) ▸
    (show (a : G) ∈ omegaOneCenterAmbient (Tg : Subgroup G) ⊓ centralizer (K₁ : Set G)
      from ⟨haz, hac⟩)))

/-- The universally applicable form of 13.6.17 used after replacing K by
its minimal block. Centrality is in the range of the actual checked map. -/
theorem noncentral_of_checkedSylow_conjugate
    (T : Sylow 2 G) (L K : Subgroup G) (z v : G)
    (standing : SourceHypothesis T L)
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
        cComponentLayer X = solvableResidual X)
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) z v)
    (hTK : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hvT : v ∈ T) (hv : v ^ 2 = 1)
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (a : Tv (T : Subgroup G) v)
    (hag : ∃ g : G, (a : G) = MulAut.conj g z)
    (ha : (checkedSylowMap (T : Subgroup G) v).rangeRestrict a ∈
      center (checkedSylowMap (T : Subgroup G) v).range) :
    ¬ K ≤ centralizer ({(a : G)} : Set G) := by
  obtain ⟨g, hg⟩ := hag
  apply lemma_13_6_17 T L K z v g (inclusion inf_le_right a)
    standing hA39 h63 hK hTK hSylow hidx hvT hv hz hz1 hf hg
  apply mem_centralizer_iff.mpr
  rintro x ⟨t, ht, rfl⟩
  let t' : Tv (T : Subgroup G) v := ⟨t, ht⟩
  exact congrArg Subtype.val (mem_center_iff.mp ha
    ((checkedSylowMap (T : Subgroup G) v).rangeRestrict t'))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
