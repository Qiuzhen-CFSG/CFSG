module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Hall.Source
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality

/-!
# The left fixed spaces before the module comparison

The actual Hall calculation identifies C_Z(D₀) with C_Z(K). Since D₀ lies
in L, the subgroup C_Z(L) centralizes K and T, hence H. It also centralizes
LT. Nonsolvable uniqueness and H outside N_G(L) force it to be trivial.
Every nontrivial T-invariant two-subgroup meets Z, so C_V(L) and C_T(L)
vanish as well. Only the inclusion C_Z(L) ≤ C_Z(K) is needed here.

This removes the central kernel of the L-module before its Cartan
comparison, without splitting an arbitrary central extension.
Source: Aschbacher--Smith, 11.3.7(3), printed p.773.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

include D S in
/-- Local uniqueness needs only containment of the left fixed subgroup. -/
theorem omega_fixed_eq_bot_of_fixed_le
    (hTH : (T : Subgroup G) ≤ H) (hout : ¬ H ≤ normalizer (L : Set G))
    (hfixed : omegaCenter T ⊓ centralizer (L : Set G) ≤
      centralizer (outsideResidual H : Set G)) :
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ := by
  let E := omegaCenter T ⊓ centralizer (L : Set G)
  by_contra hE
  let := omegaCenter_elementary (T := T)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le
    (show E ≤ omegaCenter T from inf_le_left)
  have hEC : E ≤ centralizer ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans (omegaCenter_le_sylow_centralizer T)))
  have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_centralizer_iff.mp hEC).trans (Subgroup.centralizer_le_normalizer _)
  have hEH : E ≤ centralizer (H : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← outsideResidual_sup_sylow T H hTH]
    exact sup_le (le_centralizer_iff.mp hfixed)
      (le_centralizer_iff.mp (inf_le_left.trans (omegaCenter_le_sylow_centralizer T)))
  have hlocal : IsTwoLocal (normalizer (E : Set G)) :=
    ⟨E,hE,IsElementaryAbelian.isPGroup 2 E,rfl⟩
  obtain ⟨M,hNM,hM⟩ := Finite.exists_le_maximal hlocal
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hML : M = normalizer (L : Set G) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique M hM (hLT.trans hNM)
  exact hout ((le_centralizer_iff.mp hEH).trans
    ((Subgroup.centralizer_le_normalizer _).trans (hML ▸ hNM)))

/-- The literal Z- and V-fixed spaces vanish for the actual Hall subgroup. -/
theorem source_left_fixed_spaces
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ ∧
      V ⊓ centralizer (L : Set G) = ⊥ := by
  have hz : omegaCenter T ⊓ centralizer (L : Set G) = ⊥ := by
    apply omega_fixed_eq_bot_of_fixed_le (D := D) (S := S)
      s.outside.1.1.2 s.outside.1.2
    have he := Hall.source_oddCartan_fixed s c A hA hHall
    exact ((inf_le_inf_left _ (centralizer_le hAL)).trans he.le).trans inf_le_right
  exact ⟨hz,seed_fixed_eq_bot_of_omega_fixed D S hz⟩

/-- The entire original Sylow subgroup has trivial L-centralizer. -/
theorem source_sylow_component_centralizer
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  have hz := (source_left_fixed_spaces s c A hA hHall hAL).1
  apply subgroup_eq_bot_of_central_omega_disjoint (T := T)
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) inf_le_left
  · exact (le_inf (T : Subgroup G).le_normalizer
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  · exact bot_unique ((le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans hz.le)

/-- A fixed-free chosen seed lies in every L-invariant overgroup of the Sylow omega-center. -/
theorem seed_le_of_contains_omega
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (Q : Subgroup G) (hn : L ≤ normalizer (Q : Set G))
    (hz : omegaCenter T ≤ Q) (hc : V ⊓ centralizer (L : Set G) = ⊥) : V ≤ Q := by
  have himage : ReducedNormal.subspaceImage (L ⊔ (T : Subgroup G)) D.space = V := D.image_eq
  have hnorm : L ≤ normalizer (V ⊓ Q : Set G) :=
    (le_inf D.normalizes hn).trans inf_normalizer_le_normalizer_inf
  have h := ReducedNormal.subspaceImage_eq_or_le_centralizer
    (L ⊔ (T : Subgroup G)) L le_sup_left D.irrPlus.isIrrPlus (V ⊓ Q)
    (himage.symm ▸ inf_le_left) hnorm
  rcases h with he | he
  · exact inf_eq_left.mp (he.trans himage)
  · have hd : V ⊓ omegaCenter T = ⊥ := by
      apply bot_unique
      exact (le_inf inf_le_left ((inf_le_inf_left _ hz).trans he)).trans hc.le
    exact False.elim (D.ne_bot (subgroup_eq_bot_of_central_omega_disjoint V D.le_sylow
      S.sylow_normalizes hd))


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
