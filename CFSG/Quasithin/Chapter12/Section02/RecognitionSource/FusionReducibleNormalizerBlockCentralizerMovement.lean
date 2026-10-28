module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerReduction
public import CFSG.Quasithin.ChapterC.Section06.General
public import Mathlib.GroupTheory.SchurZassenhaus
public import Theory.GroupTheory.TwoLocalUniqueness
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Genuine block movement in the escaping Sylow normalizer

Uniqueness rules out common nontrivial relatively normal subgroups of T.
The C.6 commutator bound therefore moves the actual block layer
U=[O₂(L),L] outside Q=O₂(LT). Schur–Zassenhaus constructs an odd complement
to T in its normalizer; factoring the moving element removes its T factor.

The source's disjointness C_T(L) ∩ C_T(L)^d = 1 is also proved here.
A nontrivial intersection, normal in T, would meet Ω₁Z(T); uniqueness
already makes the corresponding central omega subgroups disjoint.
Neither U nor the source omega-generated module is identified with chosen V.
All normality is relative to the displayed local group.

Source: Aschbacher–Smith C.6.3(1), p.166; 3.3.26 and 3.3.27(1), p.600.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
theorem BlockAlternative.short (hb : BlockAlternative L) : ChapterC.IsShort L := by
  rcases hb with hb | hb | hb
  · exact hb.2.1
  · exact hb.1
  · exact hb.2.1

theorem exists_odd_normalizer_complement (T : Sylow 2 G) :
    ∃ A : Subgroup G, A ≤ normalizer (T : Set G) ∧ Odd (Nat.card A) ∧
      (T : Subgroup G) ⊔ A = normalizer (T : Set G) ∧
      ∀ x ∈ normalizer (T : Set G), ∃ a ∈ A, ∃ t ∈ (T : Subgroup G), x = a * t := by
  let N := normalizer (T : Set G)
  let S : Sylow 2 N := T.subtype (T : Subgroup G).le_normalizer
  let : (S : Subgroup N).Normal := normal_in_normalizer
  have ho : Odd (S : Subgroup N).index := by
    simpa only [← Nat.not_even_iff_odd, even_iff_two_dvd] using S.not_dvd_index
  have hcop : Nat.Coprime (Nat.card (S : Subgroup N)) (S : Subgroup N).index := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact ho.coprime_two_left.pow_left n
  obtain ⟨A₀, hA₀⟩ := exists_right_complement'_of_coprime hcop
  let A := A₀.map N.subtype
  have hS : (S : Subgroup N).map N.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (T : Subgroup G).le_normalizer
  refine ⟨A, map_subtype_le _, ?_, ?_, ?_⟩
  · rw [card_map_of_injective N.subtype_injective, ← hA₀.symm.index_eq_card]
    exact ho
  · have hh := congrArg (map N.subtype) hA₀.sup_eq_top
    rw [Subgroup.map_sup, hS, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  · intro x hx
    obtain ⟨pair, hpair, _⟩ := hA₀.symm.existsUnique (⟨x, hx⟩ : N)
    exact ⟨pair.1, mem_map_of_mem N.subtype pair.1.property,
      pair.2, hS ▸ mem_map_of_mem N.subtype pair.2.property,
      (congrArg N.subtype hpair).symm⟩

theorem no_common_normal_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {A W : Subgroup G} (hA : ¬ A ≤ normalizer (L : Set G))
    (hWT : W ≤ (T : Subgroup G)) (hne : W ≠ ⊥)
    (hn : (W.subgroupOf (L ⊔ (T : Subgroup G))).Normal) :
    ¬ A ≤ normalizer (W : Set G) := by
  intro hAW
  exact hA (hAW.trans (D.normal_subgroup_normalizer_le h.toHypothesis1221
    (hWT.trans le_sup_right) hne
    ((normal_subgroupOf_iff_le_normalizer (hWT.trans le_sup_right)).mp hn)))

private theorem short_residual (hb : ChapterC.IsShort L) :
    Stellmacher.twoResidualAmbient L = L := by
  have hi : Stellmacher.twoResidualSubgroup L = ⊤ := by
    apply top_unique
    apply le_sInf
    rintro N ⟨hn, n, hi⟩
    let := hn
    have hp : IsPGroup 2 (L ⧸ N) := IsPGroup.iff_card.mpr
      ⟨n, by simpa only [index_eq_card] using hi⟩
    rw [hb.twoPerfect N hn hp]
  rw [Stellmacher.twoResidualAmbient, hi, ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
theorem block_module_eq_commutator :
    (ChapterC.blockU L).map L.subtype = ⁅L.pCoreIn 2, L⁆ := by
  rw [ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rfl

theorem exists_moving_normalizer_element
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    ∃ x ∈ normalizer (T : Set G),
      ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj x).toMonoidHom ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let U := (ChapterC.blockU L).map L.subtype
  have hU : U ≠ ⊥ := fun he => hb.blockU_ne_bot
    (((ChapterC.blockU L).map_eq_bot_iff_of_injective L.subtype_injective).mp he)
  have hc := ChapterC.c6_3_commutator_core_bound L (T : Subgroup G)
    D.sylow_normalizes_component (short_residual hb)
  have hUQ : U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    (map_mono ChapterC.blockU_le_core).trans hc.2
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  apply exists_conjugate_not_le_of_no_common_normal U (T : Subgroup G)
    ((L ⊔ (T : Subgroup G)).pCoreIn 2) L (normalizer (T : Set G)) hU
    (hUQ.trans hQT) le_rfl
  · rw [show U = ⁅L.pCoreIn 2, L⁆ from block_module_eq_commutator]
    exact hc.1
  · intro W hW hWT hLW hNW
    apply no_common_normal_of_escape h D hescape hWT hW _ hNW
    exact (normal_subgroupOf_iff_le_normalizer (hWT.trans le_sup_right)).mpr
      (sup_le hLW ((T : Subgroup G).le_normalizer.trans hNW))

theorem exists_odd_block_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : BlockAlternative L) :
    ∃ A : Subgroup G, A ≤ normalizer (T : Set G) ∧ Odd (Nat.card A) ∧
      (T : Subgroup G) ⊔ A = normalizer (T : Set G) ∧
      ¬ A ≤ normalizer (L : Set G) ∧
      ∃ d ∈ A, d ∉ normalizer (L : Set G) ∧
        ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom ≤
          (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨A, hAN, ho, hjoin, hfactor⟩ := exists_odd_normalizer_complement T
  have hA : ¬ A ≤ normalizer (L : Set G) := by
    intro ha
    exact hescape (hjoin ▸ sup_le D.sylow_normalizes_component ha)
  obtain ⟨x, hxN, hx⟩ := exists_moving_normalizer_element h D hescape hb.short
  obtain ⟨a, ha, t, ht, hxa⟩ := hfactor x hxN
  have hTU : (T : Subgroup G) ≤ normalizer ((ChapterC.blockU L).map L.subtype : Set G) :=
    D.sylow_normalizes_component.trans
      (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  have he : ((ChapterC.blockU L).map L.subtype).map (MulAut.conj (a*t)).toMonoidHom =
      (((ChapterC.blockU L).map L.subtype).map (MulAut.conj t).toMonoidHom).map
        (MulAut.conj a).toMonoidHom := by
    exact conjBy_mul _ a t
  have htU : ((ChapterC.blockU L).map L.subtype).map (MulAut.conj t).toMonoidHom =
      (ChapterC.blockU L).map L.subtype := mem_normalizer_iff_map_conj_eq.mp (hTU ht)
  rw [hxa, he, htU] at hx
  refine ⟨A, hAN, ho, hjoin, hA, a⁻¹, A.inv_mem ha, ?_, by simpa using hx⟩
  intro hm
  have haM := (normalizer (L : Set G)).inv_mem hm
  simp only [inv_inv] at haM
  have haU : ((ChapterC.blockU L).map L.subtype).map (MulAut.conj a).toMonoidHom =
      (ChapterC.blockU L).map L.subtype := mem_normalizer_iff_map_conj_eq.mp
        (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L) haM)
  rw [haU] at hx
  exact hx ((map_mono ChapterC.blockU_le_core).trans
    (ChapterC.c6_3_commutator_core_bound L (T : Subgroup G)
      D.sylow_normalizes_component (short_residual hb.short)).2)

theorem sylow_centralizer_disjoint_conjugate
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hout : d ∉ normalizer (L : Set G)) :
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
      ((T : Subgroup G) ⊓ centralizer (L : Set G)).map (MulAut.conj d).toMonoidHom = ⊥ := by
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let Z := C ⊓ omegaCenterIn (T : Subgroup G)
  let C' := C.map (MulAut.conj d).toMonoidHom
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hTC' : (T : Subgroup G) ≤ normalizer (C' : Set G) := by
    have hh := (map_mono (f := (MulAut.conj d).toMonoidHom) hTC).trans
      (C.le_normalizer_map (MulAut.conj d).toMonoidHom)
    have ht : (T : Subgroup G).map (MulAut.conj d).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp hd
    rwa [ht] at hh
  have hZZ : Z ⊓ Z.map (MulAut.conj d).toMonoidHom = ⊥ := by
    apply inf_conjugate_eq_bot_of_unique_maximalTwoLocal
      (maximal_unique h D).1 (maximal_unique h D).2 _ _ hout
    · apply sup_le
      · exact le_centralizer_iff.mp (inf_le_left.trans inf_le_right)
      · exact le_centralizer_iff.mp (fun z hz =>
          ((mem_omegaCenterIn_iff _ _).mp hz.2).2.1)
    · exact fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz.2).2.2
  by_contra hn
  have hnonzero := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup (C ⊓ C')
    (T : Subgroup G) (inf_le_left.trans inf_le_left) T.isPGroup'
    ((le_inf hTC hTC').trans inf_normalizer_le_normalizer_inf) hn
  apply hnonzero
  apply bot_unique
  apply le_trans _ hZZ.le
  have hzmap : (omegaCenterIn (T : Subgroup G)).map (MulAut.conj d).toMonoidHom =
      omegaCenterIn (T : Subgroup G) := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_omegaCenterIn (T : Subgroup G) hd)
  rw [map_inf _ _ _ (MulAut.conj d).injective, hzmap]
  exact fun z hz => ⟨⟨hz.1.1, hz.2⟩, hz.1.2, hz.2⟩

/-- Application to the literal reducible block source: choose an odd moving
actor, with the centralizer control and disjointness required at the endpoint. -/
theorem source_block_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : BlockAlternative L) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
    ∃ A : Subgroup G, A ≤ normalizer (T : Set G) ∧ Odd (Nat.card A) ∧
      (T : Subgroup G) ⊔ A = normalizer (T : Set G) ∧
      ¬ A ≤ normalizer (L : Set G) ∧
      ∃ d ∈ A, d ∉ normalizer (L : Set G) ∧
        ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom ≤
          (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
          ((T : Subgroup G) ⊓ centralizer (L : Set G)).map
            (MulAut.conj d⁻¹).toMonoidHom = ⊥ := by
  refine ⟨omega_centralizer_le h D hfixed, ?_⟩
  obtain ⟨A, hA, ho, hj, hn, d, hd, hout, hmove⟩ := exists_odd_block_movement h D hescape hb
  refine ⟨A, hA, ho, hj, hn, d, hd, hout, hmove, ?_⟩
  apply sylow_centralizer_disjoint_conjugate h D
    ((normalizer (T : Set G)).inv_mem (hA hd))
  exact fun hi => hout (by simpa only [inv_inv] using (normalizer (L : Set G)).inv_mem hi)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
