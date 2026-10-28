module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Splitting
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore

/-!
# The original core omega subgroup when the marked fixed subgroup vanishes

The component-fixed subgroup of the global core omega is normalized by the
original point two-group and lies in that two-group. If it is nontrivial,
the normal subgroup fixed-point theorem gives a nontrivial intersection with
the central omega of the same point two-group. Thus vanishing of the marked
fixed subgroup forces vanishing of the entire global fixed supplement.

The genuine source splitting then identifies the whole global core omega
with the original doubled orbit. It also identifies the point omega with
the fixed subgroup of that orbit. This restricts the remaining branch of
12.1.4 without an MS classification or a point-omega cardinality assumption.
It does not exclude that remaining branch.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Triviality of the fixed part of the actual point omega detects triviality
of the fixed part of the whole global core omega. -/
theorem doubleNatural_point_omega_fixed_eq_bot_iff
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n)
    (w : componentOrbit V (T : Subgroup G)) :
    omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) = ⊥ ↔
      omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
        centralizer (L : Set G) = ⊥ := by
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let R := B.pointSylow w
  let F := omegaCenterIn Q ⊓ centralizer (L : Set G)
  have hQR : Q ≤ R := by
    dsimp only [Q, H]
    rw [← D.doubledOrbit_sylow_centralizer h]
    intro x hx
    exact ⟨hx.1, mem_centralizer_singleton_iff.mpr (hx.2 w w.property).symm⟩
  have hHQ : H ≤ normalizer (Q : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hRH : R ≤ H := (show R ≤ (T : Subgroup G) from inf_le_left).trans le_sup_right
  have hFR : F ≤ R := inf_le_left.trans ((map_subtype_le _).trans hQR)
  have hRF : R ≤ normalizer (F : Set G) :=
    (le_inf ((hRH.trans hHQ).trans (normalizer_le_normalizer_omegaCenterIn Q))
      ((show R ≤ (T : Subgroup G) from inf_le_left).trans
        (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L)))).trans
      inf_normalizer_le_normalizer_inf
  constructor
  · intro hz
    by_contra hF
    have hne := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup F R hFR
      (T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)) hRF hF
    apply hne
    apply bot_unique
    exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans_eq hz
  · intro hz
    apply bot_unique
    exact (inf_le_inf_right _ (D.doubleNatural_point_omega_le_core_omega h B w)).trans_eq hz

/-- Under the original contrary ambient-Sylow hypotheses, either the required
marked fixed subgroup is nontrivial, or the entire global core omega and the
point omega are the indicated literal subgroups of the original doubled orbit. -/
theorem doubleNatural_four_pure_omega_fixed_or_core_omega_eq_orbit
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ ∨
        (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
            componentOrbit V (T : Subgroup G) ∧
          omegaCenterIn (B.pointSylow w) =
            componentOrbit V (T : Subgroup G) ⊓ centralizer (B.pointSylow w : Set G)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  by_cases hz : omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) = ⊥
  · right
    have hF := (D.doubleNatural_point_omega_fixed_eq_bot_iff h B w).mp hz
    have he := D.doubleNatural_four_pure_core_omega_split_of_many h hmany B S w hw hp hfix hf
    rw [hF, sup_bot_eq] at he
    refine ⟨he, le_antisymm ?_ ?_⟩
    · exact le_inf ((D.doubleNatural_point_omega_le_core_omega h B w).trans_eq he)
        (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    · intro x hx
      apply (mem_omegaCenterIn_iff _ _).mpr
      refine ⟨?_, hx.2, elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1⟩
      exact ⟨(D.doubledOrbit_E322 h).le_sylow hx.1,
        mem_centralizer_singleton_iff.mpr
          ((componentOrbit V (T : Subgroup G)).le_centralizer hx.1 w w.property).symm⟩
  · exact Or.inl hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
