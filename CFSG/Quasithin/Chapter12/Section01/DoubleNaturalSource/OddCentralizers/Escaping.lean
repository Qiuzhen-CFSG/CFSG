module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.CentralizerSylow

/-!
# Escaping odd actors in the original doubled branch

Let Q = C_T(W), with w > 1. The relative Sylow theorem places a Sylow
subgroup of every C_G(U), U ≤ W, inside M and above the original Q.
Finite descent selects a minimal overgroup outside M. Its actual overlap
with M is the unique maximal subgroup above that Sylow subgroup, and
weak closure controls the Sylow normalizer. Thus it is a genuine minimal
parabolic. E.3.35 and the initial rank bound force its generation parameter
to exceed one. The proved E.2.2 Cartan theorem then supplies a nontrivial
odd-prime subgroup with escaping full ambient normalizer.

For U = 1, use the original outside H* supplied by the multiple-overgroup
guard. For U ≠ 1, SQTK is inherited inside N_G(U). No conjugation of U or
assumption that C_T(U) is Sylow is required. The same literal subgroup
centralizes U and lies in M. The source adapter discharges the first-stage
weak-closure and rank premises before applying the fixed-space calculation.
Source: Aschbacher--Smith, 12.1.9, printed pp.793--794, using E.2.2 and E.3.35.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open CFSG.Quasithin.ChapterB CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G]

private theorem relative_parabolic {C M : Subgroup G} (R : Sylow 2 C)
    (hout : ¬ C ≤ M)
    (hN : normalizer ((R : Subgroup C).map C.subtype : Set G) ≤ M) :
    ∃ (H : Subgroup G) (S : Sylow 2 H), H ≤ C ∧ ¬ H ≤ M ∧
      (S : Subgroup H).map H.subtype = (R : Subgroup C).map C.subtype ∧
      ∃ hP : IsMinimalParabolicOver S ⊤,
        minimalParabolicMax S hP = M.subgroupOf H := by
  let Rg := (R : Subgroup C).map C.subtype
  obtain ⟨H, hHC, hH⟩ := exists_minimal_le_of_wellFoundedLT
    (fun H : Subgroup G => Rg ≤ H ∧ ¬ H ≤ M) C ⟨map_subtype_le _, hout⟩
  have hRM : Rg ≤ M := Rg.le_normalizer.trans hN
  have hRH : (R : Subgroup C) ≤ (inclusion hHC).range := by
    rw [inclusion_range]
    exact map_le_iff_le_comap.mp hH.1.1
  let S := R.comapOfInjective (inclusion hHC) (inclusion_injective hHC) hRH
  have hS : (S : Subgroup H).map H.subtype = Rg := by
    have he : H.subtype = C.subtype.comp (inclusion hHC) := rfl
    rw [he, ← map_map]
    change (((R : Subgroup C).comap (inclusion hHC)).map (inclusion hHC)).map C.subtype = Rg
    rw [map_comap_eq_self hRH]
  have hSM : (S : Subgroup H) ≤ M.subgroupOf H :=
    map_le_iff_le_comap.mp (hS ▸ hRM)
  have hproper (Y : Subgroup H) (hSY : (S : Subgroup H) ≤ Y) (hY : Y ≠ ⊤) :
      Y ≤ M.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    by_contra hn
    have hRY : Rg ≤ Y.map H.subtype := hS ▸ map_mono hSY
    have he := hH.2 ⟨hRY, hn⟩ (map_subtype_le Y)
    have htop : (⊤ : Subgroup H).map H.subtype ≤ Y.map H.subtype := by
      simpa only [← MonoidHom.range_eq_map, range_subtype] using he
    exact hY (top_unique ((map_le_map_iff_of_injective H.subtype_injective).mp htop))
  have hne : M.subgroupOf H ≠ ⊤ := fun he => hH.1.2 (subgroupOf_eq_top.mp he)
  have hcoat : IsCoatom (M.subgroupOf H) := isCoatom_iff_ge_of_le.mpr
    ⟨hne, fun Y hY hMY => hproper Y (hSM.trans hMY) hY⟩
  have huniq : ∃! Y : Subgroup H, IsCoatom Y ∧ (S : Subgroup H) ≤ Y := by
    refine ⟨M.subgroupOf H, ⟨hcoat, hSM⟩, ?_⟩
    intro Y hY
    exact ((hY.1.le_iff.mp (hproper Y hY.2 hY.1.ne_top)).resolve_left hne).symm
  have hP : IsMinimalParabolicOver S ⊤ := (isMinimalParabolicOver_top_iff S).mpr
    ⟨huniq, by
      intro hnormal
      let := hnormal
      have hn : H ≤ normalizer (Rg : Set G) := by
        simpa only [hS, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
          (S : Subgroup H).le_normalizer_map H.subtype
      exact hH.1.2 (hn.trans hN)⟩
  exact ⟨H, S, hHC, hH.1.2, hS, hP,
    huniq.unique (minimalParabolicMax_spec S hP) ⟨hcoat, hSM⟩⟩

private theorem cartan_actor {H M : Subgroup G} (S : Sylow 2 H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hP : IsMinimalParabolicOver S ⊤)
    (hmax : minimalParabolicMax S hP = M.subgroupOf H)
    (hn : 1 < generationParameter H) :
    ∃ X : Subgroup G, X ≠ ⊥ ∧ Odd (Nat.card X) ∧ X ≤ M ∧ X ≤ H ∧
      ¬ normalizer (X : Set G) ≤ M := by
  obtain ⟨f, _, hb, d, hescape⟩ :=
    MarkedModels.Inverted.source_intrinsic_escape_knownSimple hH S hP hn
  have hf : 2 ≤ f := by omega
  have hc : 1 < Nat.card d.witness.cyclicGroup := by
    rw [d.witness.card]
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
    norm_num at hp
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hc)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime p
    (show p ^ 1 ∣ Nat.card d.witness.cyclicGroup by simpa using hpd)
  let A := A₀.map d.witness.cyclicGroup.subtype
  have hAc : Nat.card A = p := by
    rw [card_map_of_injective d.witness.cyclicGroup.subtype_injective]
    simpa only [pow_one] using hA₀
  have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hAc)
  have hAD : A ≤ d.witness.cyclicGroup := map_subtype_le _
  have ho : Odd p := (d.witness.odd.of_dvd_nat
    (card_dvd_of_le d.witness.cyclic_le)).of_dvd_nat hpd
  have hAM : A ≤ M.subgroupOf H := hAD.trans (d.witness.cyclic_le.trans
    (d.hall_le.trans hmax.le))
  have hAcG : Nat.card (A.map H.subtype) = p :=
    (card_map_of_injective H.subtype_injective).trans hAc
  refine ⟨A.map H.subtype,
    (A.map H.subtype).one_lt_card_iff_ne_bot.mp (hAcG ▸ hp.one_lt),
    hAcG ▸ ho, map_le_iff_le_comap.mpr hAM, map_subtype_le _, ?_⟩
  intro hN
  apply hescape p inferInstance A ho hAD hAp
  rw [hmax]
  intro x hx
  exact hN (A.le_normalizer_map H.subtype (mem_map.mpr ⟨x, hx, rfl⟩))

variable {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

include D h in
private theorem relative_generation_gt_one
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T)
    {H : Subgroup G} (S : Sylow 2 H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hout : ¬ H ≤ normalizer (L : Set G))
    (hQS : (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ≤
      (S : Subgroup H).map H.subtype)
    (hr : (n : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G))) :
    1 < generationParameter H := by
  let := D.doubledOrbit_elementary h
  by_contra hn
  have hn1 : generationParameter H ≤ 1 := by omega
  have hnlarge : 1 < n := by rcases B.degree with rfl | rfl <;> decide
  apply hout
  apply SourceContainment.le_of_sqtk_knownSimple (D.doubledOrbit_E322 h) S hH
    (D.doubledOrbit_centralizer_unique h)
    (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (D.doubledOrbit_normalizer_eq h B.orbit_eq).le)) hQS
  exact lt_min (lt_of_le_of_lt (by exact_mod_cast hn1) hw)
    (lt_of_lt_of_le (by exact_mod_cast (lt_of_le_of_lt hn1 hnlarge)) hr)

include D h in
/-- The actual source actor for every escaping subspace centralizer, from
first-stage weak closure and the initial rank bound. -/
theorem doubledOrbit_escapingOddActors_of_many_of_rank
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T)
    (hr : (n : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G))) :
    EscapingOddActors (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) := by
  let := D.doubledOrbit_elementary h
  intro U hUW hescape
  suffices ∃ (C : Subgroup G) (R : Sylow 2 C),
      IsSQTK KnownSimple.IsKnownSimple C ∧ C ≤ centralizer (U : Set G) ∧
      ¬ C ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ≤
        (R : Subgroup C).map C.subtype by
    obtain ⟨C,R,hC,hCU,hout,hQR⟩ := this
    have hN := D.doubledOrbit_relative_normalizer_le_of_many h hmany hw _
      (R.isPGroup'.map C.subtype) hQR
    obtain ⟨H,S,hHC,hHM,hS,hP,hmax⟩ := relative_parabolic R hout hN
    have hH : IsSQTK KnownSimple.IsKnownSimple H :=
      ⟨hC.stronglyQuasithin.of_injective (inclusion hHC) (inclusion_injective hHC),
        hC.isKGroup.of_injective (inclusion hHC) (inclusion_injective hHC)⟩
    have hn := D.relative_generation_gt_one h B hw S hH hHM (hQR.trans_eq hS.symm) hr
    obtain ⟨X,hX,ho,hXM,hXH,hXN⟩ := cartan_actor S hH hP hmax hn
    exact ⟨X,hX,ho,hXM,hXH.trans (hHC.trans hCU),hXN⟩
  by_cases hU : U = ⊥
  · obtain ⟨H,hH⟩ := D.doubledOrbit_outside_of_many h hmany
    refine ⟨H, T.subtype hH.1.1.2, Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1,
      ?_, hH.1.2, ?_⟩
    · rw [hU]
      intro x hx
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      have hy : y = 1 := hy
      simp [hy]
    · change (T : Subgroup G) ⊓ centralizer
        (componentOrbit V (T : Subgroup G) : Set G) ≤
          ((T : Subgroup G).subgroupOf H).map H.subtype
      rw [map_subgroupOf_eq_of_le hH.1.1.2]
      exact inf_le_left
  · obtain ⟨R,hQR,_⟩ := D.doubledOrbit_exists_centralizer_sylow_of_many h hmany hw U hUW
    have hUp : IsPGroup 2 U := (D.doubledOrbit_elementary h).isPGroup.of_injective
      (inclusion hUW) (inclusion_injective hUW)
    have hs := h.simpleQTKE.twoLocal_sqtk
      (show IsTwoLocal (normalizer (U : Set G)) from ⟨U,hU,hUp,rfl⟩)
    have hi := Subgroup.centralizer_le_normalizer (U : Set G)
    refine ⟨centralizer (U : Set G),R,?_,le_rfl,hescape,hQR⟩
    exact ⟨hs.stronglyQuasithin.of_injective (inclusion hi) (inclusion_injective hi),
      hs.isKGroup.of_injective (inclusion hi) (inclusion_injective hi)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
