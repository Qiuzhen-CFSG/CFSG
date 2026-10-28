module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.Basic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.TwoCore
public import Theory.GroupTheory.TwoLocalCharacteristicControl

/-!+# The source noncontainment conclusion from the earlier two-core theorem

The earlier 13.6.16(1) already implies the conclusion K ⊄ M of 13.6.21.
Indeed M is a two-local containing the ambient Sylow T. If K ≤ M, then
O₂(M) ≤ O₂(⟨K,T⟩), while the left side is nontrivial and 13.6.16(1) makes
the right side trivial. This argument works for the covered A₆ case as well
as for every other selected component.

The application below derives the earlier two-core equality for the actual
K ∈ Y_z. Its explicit inputs are precisely those of the checked 13.6.16(1)
proof, including the uniform A₅ choice in Hypothesis 13.3.1(4), A.3.9(1),
and the earlier normalization and centralizer results. No later excluded
model or 13.6.22 conclusion is used. The source assembly must supply those
earlier inputs and the usual two-local overgroup M of T.

This proves K ⊄ M, not the stronger assertion that K* does not normalize
L_v*. It therefore supplies an alternative for the source-theorem assembly,
without claiming to resolve the covered-six star-action assertion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.16(1), printed p.930, and 13.6.21, printed p.932.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction.CoveredSix
open ComponentSelection
universe u
variable {G : Type u} [Group G]

private theorem not_le_twoLocal_of_trivial_join_core
    (T : Sylow 2 G) (K M : Subgroup G)
    (hM : IsTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hcore : (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥) : ¬ K ≤ M := by
  intro hKM
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  have hQM : Q ≤ (normalizer (Q : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp Q.le_normalizer le_rfl
  have hh := pCoreIn_le_pCoreIn_of_sylow T
    (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)
    (sup_le hKM hTM)
  rw [hcore] at hh
  exact hQ (bot_unique (hQM.trans hh))

/-- The actual 13.6.21 conclusion from the genuine earlier source inputs.
The two-core equality is proved by 13.6.16(1), rather than assumed as a
branch-impossibility premise. Membership in Y_z and 13.6.14 invariance
supply the moving local component required by that theorem. -/
theorem not_le_M_of_earlier_source [Finite G] {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (T : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ MainForward.faithfulLocalComponents T)
    (hA5 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hchoice : UniformA5Choice T L)
    (hnormal : ∀ I ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (I : Set G))
    (hcentralizer : ∀ I ∈ MainForward.faithfulLocalComponents T,
      Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) →
      UniformA5Choice T I → (T : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (z v : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hvT : v ∈ T) (hv : v ≠ 1)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (K M : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) z v)
    (hn : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hM : IsTwoLocal M) (hTM : (T : Subgroup G) ≤ M) : ¬ K ≤ M := by
  have hX := (invariant_component_consequences K L (T : Subgroup G) z v hK hn).1
  have hmove : ¬ K ≤ centralizer ({z} : Set G) := fun hc =>
    hX.2 ((starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr hc)
  have hcore := twoCore_eq_bot_of_earlier_source hG hA39 T L hL hA5 hchoice
    hnormal hcentralizer z v hz hvT hv hSylow hidx K hK.1 hn hmove
  exact not_le_twoLocal_of_trivial_join_core T K M hM hTM hcore

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.StarAction.CoveredSix
