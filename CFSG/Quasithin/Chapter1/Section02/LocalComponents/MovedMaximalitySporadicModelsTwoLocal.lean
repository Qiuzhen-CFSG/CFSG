module
public import Theory.GroupTheory.CComponent.SylowOvergroupTwoLocal
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.LocalA5Placement

/-!
# The nontrivial-two-core branches for Held and Rudvalis

The actual Held max3 and max4 quotients map onto S₆ with a solvable kernel;
max5 has order 2^10 · 3 · 7. The actual Rudvalis max4 and max6 orders are
2^14 · 3 · 7 and 2^14 · 3 · 5. These local calculations give uniqueness.
The certified elementary-normalizer catalogues cover every Sylow-containing
two-local by these literal subgroups, retaining their actual conjugations.

For P containing a full Sylow and P ≤ M with O₂(M) nontrivial, normalize that
core and use the appropriate catalogue. Thus any failure of uniqueness in
Held or Rudvalis requires a maximal odd-index subgroup with trivial two-core.
Excluding those maximal subgroups is still a separate mathematical obligation;
no exhaustive catalogue of arbitrary Sylow overgroups is asserted here.

Source: Aschbacher--Smith A.3.12(19--20), pp.47--48, citing Aschbacher's
1986 Sylow-overgroup analysis; GLS3 Tables 5.3p and 5.3r for the local structures.
The next module applies this reduction to the original moved-component quotient.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
open Held.LocalPairs.PairCoverage Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner

private theorem held_symmetric_six_unique : SylowOvergroupComponentUnique (Equiv.Perm (Fin 6)) := by
  apply SylowOvergroupComponentUnique.of_card_dvd_two_three_prime 4 2 5
    (by decide) (by decide) (by decide)
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- Each actual Held max3/max4/max5 candidate has unique components in its Sylow overgroups. -/
theorem held_local_component_unique (i : Fin 3) :
    SylowOvergroupComponentUnique (Held.TwoLocalCandidates.subgroup i) := by
  have h34 (i : Bool) : SylowOvergroupComponentUnique (localOvergroup i) := by
    let := pCore_isNilpotent (p := 2) (G := localOvergroup i)
    apply SylowOvergroupComponentUnique.of_quotient (pCore 2 (localOvergroup i))
    let f := SixPoint.quotientAction i
    let : Group.IsSolvable f.ker := by
      have hp : IsPGroup 3 f.ker := isPGroup_iff_card_dvd_pow.mpr
        ⟨1, by simpa only [pow_one] using
          Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i⟩
      let := hp.isNilpotent
      infer_instance
    exact SylowOvergroupComponentUnique.of_surjective f
      (SixPoint.quotientAction_surjective i) held_symmetric_six_unique
  fin_cases i
  · exact h34 false
  · exact h34 true
  · apply SylowOvergroupComponentUnique.of_card_dvd_two_three_prime 10 1 7
      (by decide) (by decide) (by decide)
    change Nat.card Held.TwoLocalCandidates.max5 ∣ _
    rw [Held.InvolutionFixedData.TwoB.max5_card]
    norm_num

private theorem held_twoLocal_cover (S : Sylow 2 Held.He) (N : Subgroup Held.He)
    (hSN : (S : Subgroup Held.He) ≤ N) (hN : IsTwoLocal N) :
    ∃ (e : Held.He ≃* Held.He) (J : Subgroup Held.He), N.map e.toMonoidHom ≤ J ∧
      SylowOvergroupComponentUnique J := by
  obtain ⟨T,hcatalogue⟩ := Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Held.He S T
  let a := MulAut.conj g
  have hT : (T : Subgroup Held.He) ≤ N.map a.toMonoidHom := by
    have hh := map_mono (f := a.toMonoidHom) hSN
    change ((g • S : Sylow 2 Held.He) : Subgroup Held.He) ≤ _ at hh
    rwa [hg] at hh
  obtain ⟨M,hNM,hM⟩ := Finite.exists_le_maximal (Theory.Quasithin.isTwoLocal_map a hN)
  obtain ⟨R,hR,hRn,hRe,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hM (hT.trans hNM)
  obtain ⟨i,k,hk⟩ := hcatalogue R hR hRn hRe (hNR ▸ hM)
  refine ⟨a,M,hNM,?_⟩
  rw [hNR,hk]
  exact SylowOvergroupComponentUnique.of_equiv
    ((MulAut.conj k).subgroupMap (Held.TwoLocalCandidates.subgroup i)).symm
    (held_local_component_unique i)

/-- The native Held restriction when the literal overgroup has nontrivial two-core. -/
theorem held_components_eq_of_twoCore_ne_bot (S : Sylow 2 Held.He) (P : Subgroup Held.He)
    (hSP : (S : Subgroup Held.He) ≤ P) (hcore : pCore 2 P ≠ ⊥)
    {B C : Subgroup P} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C :=
  SylowOvergroupComponentUnique.eq_of_le_overgroup_twoCore_ne_bot held_twoLocal_cover S P P hSP le_rfl hcore hB hC

/-- The checked order of the actual Rudvalis max4 candidate forces component uniqueness. -/
theorem rudvalis_max4_component_unique :
    SylowOvergroupComponentUnique Rudvalis.SylowOvergroups.max4 := by
  apply SylowOvergroupComponentUnique.of_card_dvd_two_three_prime 14 1 7
    (by decide) (by decide) (by decide)
  rw [Rudvalis.SylowOvergroups.max4_card]
  norm_num

/-- The checked order of the actual Rudvalis max6 candidate forces component uniqueness. -/
theorem rudvalis_max6_component_unique :
    SylowOvergroupComponentUnique Rudvalis.SylowOvergroups.max6 := by
  apply SylowOvergroupComponentUnique.of_card_dvd_two_three_prime 14 1 5
    (by decide) (by decide) (by decide)
  rw [Rudvalis.SylowOvergroups.max6_card]
  norm_num

private theorem rudvalis_twoLocal_cover (S : Sylow 2 Rudvalis.Model) (N : Subgroup Rudvalis.Model)
    (hSN : (S : Subgroup Rudvalis.Model) ≤ N) (hN : IsTwoLocal N) :
    ∃ (e : Rudvalis.Model ≃* Rudvalis.Model) (J : Subgroup Rudvalis.Model),
      N.map e.toMonoidHom ≤ J ∧ SylowOvergroupComponentUnique J := by
  rcases Rudvalis.SylowOvergroups.twoLocal_cover S N hN hSN with ⟨e,he⟩ | ⟨e,he⟩
  · exact ⟨e,_,he,rudvalis_max4_component_unique⟩
  · exact ⟨e,_,he,rudvalis_max6_component_unique⟩

/-- The native Rudvalis restriction when the literal overgroup has nontrivial two-core. -/
theorem rudvalis_components_eq_of_twoCore_ne_bot (S : Sylow 2 Rudvalis.Model)
    (P : Subgroup Rudvalis.Model) (hSP : (S : Subgroup Rudvalis.Model) ≤ P)
    (hcore : pCore 2 P ≠ ⊥)
    {B C : Subgroup P} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C :=
  SylowOvergroupComponentUnique.eq_of_le_overgroup_twoCore_ne_bot rudvalis_twoLocal_cover S P P hSP le_rfl hcore hB hC


variable {G : Type*} [Group G] [Finite G]

/-- Transport the Held restriction to an arbitrary isomorphic carrier, preserving the containing subgroup. -/
theorem held_eq_of_le_overgroup_twoCore_ne_bot
    (hm : Nonempty (G ≃* Held.He))
    (S : Sylow 2 G) (P M : Subgroup G) (hSP : (S : Subgroup G) ≤ P)
    (hPM : P ≤ M) (hcore : pCore 2 M ≠ ⊥)
    {B C : Subgroup P} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  obtain ⟨e⟩ := hm
  apply SylowOvergroupComponentUnique.eq_of_le_overgroup_twoCore_ne_bot_of_equiv e
    (fun S P M hSP hPM hc B C hB hC =>
      SylowOvergroupComponentUnique.eq_of_le_overgroup_twoCore_ne_bot
        held_twoLocal_cover S P M hSP hPM hc hB hC) S P M hSP hPM hcore hB hC

/-- Transport the Rudvalis restriction to an arbitrary isomorphic carrier, preserving the containing subgroup. -/
theorem rudvalis_eq_of_le_overgroup_twoCore_ne_bot
    (hm : Nonempty (G ≃* Rudvalis.Model))
    (S : Sylow 2 G) (P M : Subgroup G) (hSP : (S : Subgroup G) ≤ P)
    (hPM : P ≤ M) (hcore : pCore 2 M ≠ ⊥)
    {B C : Subgroup P} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  obtain ⟨e⟩ := hm
  apply SylowOvergroupComponentUnique.eq_of_le_overgroup_twoCore_ne_bot_of_equiv e
    (fun S P M hSP hPM hc B C hB hC =>
      SylowOvergroupComponentUnique.eq_of_le_overgroup_twoCore_ne_bot
        rudvalis_twoLocal_cover S P M hSP hPM hc hB hC) S P M hSP hPM hcore hB hC

/-- A remaining Held counterexample requires an actual maximal odd-index subgroup with trivial two-core. -/
theorem held_coreFree_maximal_of_not_unique [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : Nonempty (G ≃* Held.He)) (hu : ¬ SylowOvergroupComponentUnique G) :
    ∃ (S : Sylow 2 G) (M : Subgroup G), IsCoatom M ∧ (S : Subgroup G) ≤ M ∧
      ¬ 2 ∣ M.index ∧ pCore 2 M = ⊥ := by
  apply SylowOvergroupComponentUnique.exists_coreFree_maximal_of_not_unique _ hu
  intro S P M hSP hPM hc B C hB hC
  exact held_eq_of_le_overgroup_twoCore_ne_bot hm S P M hSP hPM hc hB hC

/-- A remaining Rudvalis counterexample requires an actual maximal odd-index subgroup with trivial two-core. -/
theorem rudvalis_coreFree_maximal_of_not_unique [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : Nonempty (G ≃* Rudvalis.Model)) (hu : ¬ SylowOvergroupComponentUnique G) :
    ∃ (S : Sylow 2 G) (M : Subgroup G), IsCoatom M ∧ (S : Subgroup G) ≤ M ∧
      ¬ 2 ∣ M.index ∧ pCore 2 M = ⊥ := by
  apply SylowOvergroupComponentUnique.exists_coreFree_maximal_of_not_unique _ hu
  intro S P M hSP hPM hc B C hB hC
  exact rudvalis_eq_of_le_overgroup_twoCore_ne_bot hm S P M hSP hPM hc hB hC

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
