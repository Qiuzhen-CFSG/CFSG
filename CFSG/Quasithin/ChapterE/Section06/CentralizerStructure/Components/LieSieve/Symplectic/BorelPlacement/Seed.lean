module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Carrier
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# The marked symplectic Borel and its binary placement

The normalizer of the prescribed Sylow subgroup of L is the full preimage
of its image normalizer in L/Z(L). At n=1 the actual derived matrix group
Sp₄(2)' has self-normalizing Sylow two-subgroups, so this Borel lies in
L ∩ M directly. For n>1 the derived-to-full equivalence and Sylow conjugacy
identify the marked Borel with the standard matrix flag stabilizer.

Each marked Borel is solvable and has characteristic two. The latter follows
by restriction from a full point parabolic for n>1; at n=1 it is a two-group.
The centerless model comparison is also retained for the component-orbit
construction. Nonbinary containment in M is not asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), with the actual binary derived endpoint.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement
variable {G : Type*} [Group G] [Finite G] {L Q : Subgroup G}

@[expose] def markedBorel (S : Sylow 2 L) : Subgroup G :=
  (normalizer (S : Set L)).map L.subtype

omit [Finite G] in
theorem markedBorel_le (S : Sylow 2 L) : markedBorel S ≤ L := map_subtype_le _

theorem markedBorel_preimage (S : Sylow 2 L) : BorelPreimage L (markedBorel S) := by
  refine ⟨markedBorel_le S, S.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.normalizer_comap_quotient_center]
  exact comap_map_eq_self_of_injective L.subtype_injective _

private theorem normalizer_eq_of_model_one (hm : SymplecticDerivedModel L 1)
    (S : Sylow 2 L) : normalizer (S : Set L) = (S : Subgroup L) := by
  obtain ⟨_, F, _, _, hF, ⟨e⟩⟩ := hm
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Sylow.normalizer_map_surjective S e.toMonoidHom e.surjective]
  exact derived_sylow_normalizer_eq_of_card_two (by simpa using hF)
    (S.mapSurjective e.surjective)

theorem markedBorel_eq_of_model_one (hm : SymplecticDerivedModel L 1)
    (S : Sylow 2 L) : markedBorel S = (S : Subgroup L).map L.subtype := by
  rw [markedBorel, normalizer_eq_of_model_one hm S]

variable {K : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}

theorem exists_borel_of_model_one (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) :
    ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B := by
  obtain ⟨_, S, hS, _⟩ := component_sylow_action h hU hL rfl
  refine ⟨markedBorel S, ?_, markedBorel_preimage S⟩
  rw [markedBorel_eq_of_model_one hm, hS]
  exact inf_le_inf_left L (inf_le_left.trans h.sylow_le)

private theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hz : center Y = ⊥) : center X = ⊥ := by
  apply bot_unique
  intro x hx
  have he : e x ∈ center Y := (centerCongr e ⟨x, hx⟩).property
  rw [hz, mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))

omit [Finite G] in
theorem model_center_eq_bot {n : ℕ} (hm : SymplecticDerivedModel L n) : center L = ⊥ := by
  by_cases hn : n = 1
  · subst n
    obtain ⟨e⟩ := alternating_six_of_model_one hm
    exact center_eq_bot_of_equiv e (alternatingGroup.center_eq_bot (by simp))
  · obtain ⟨hnpos, F, _, _, hF, ⟨e⟩⟩ := hm
    let _ := EvenProjective.charTwo_of_card hF
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    exact center_eq_bot_of_equiv (e.trans (derivedEquivFull_of_card_gt_two hlarge))
      EvenProjective.center_eq_bot

private theorem matrix_borel_characteristicTwo {F : Type*} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    HasCharacteristicTwo (borel (F := F)) := by
  have hUB : unipotent (F := F) ≤ borel (F := F) := by
    rw [borel_eq_normalizer_unipotent]
    exact le_normalizer
  have hBP : borel (F := F) ≤ pointParabolic := inf_le_left
  have hc := centralizer_pCore_le_of_sylow_le
    ((unipotentSylow hF (by omega)).subtype (hUB.trans hBP))
    ((borel (F := F)).subgroupOf pointParabolic) (fun _ hx => hUB hx)
    (pointParabolic_selfCentralizing_core hF hn)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hBP)).mp hc

private theorem matrix_normalizer_characteristicTwo {F : Type*} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) : HasCharacteristicTwo (normalizer (S : Set (Sp F))) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF (by omega))
  let a := MulAut.conj g
  have hS : (S : Subgroup (Sp F)).map a.toMonoidHom = unipotent :=
    congrArg (fun R : Sylow 2 (Sp F) => (R : Subgroup (Sp F))) hg
  have hN : (normalizer (S : Set (Sp F))).map a.toMonoidHom = borel (F := F) := by
    change (normalizer ((S : Subgroup (Sp F)) : Set (Sp F))).map a.toMonoidHom = _
    rw [map_equiv_normalizer_eq, hS, borel_eq_normalizer_unipotent]
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 a _).mp
  rw [hN]
  exact matrix_borel_characteristicTwo hF hn

theorem normalizer_characteristicTwo {n : ℕ} (hm : SymplecticDerivedModel L n)
    (S : Sylow 2 L) : HasCharacteristicTwo (normalizer (S : Set L)) := by
  by_cases hn : n = 1
  · subst n
    rw [normalizer_eq_of_model_one hm S]
    have hc : pCore 2 S = ⊤ :=
      top_unique (le_sSup ⟨inferInstance, S.isPGroup'.to_subgroup ⊤⟩)
    change centralizer (pCore 2 S : Set S) ≤ pCore 2 S
    rw [hc]
    exact le_top
  · obtain ⟨hnpos, F, _, _, hF, ⟨e₀⟩⟩ := hm
    let _ := EvenProjective.charTwo_of_card hF
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    let e := e₀.trans (derivedEquivFull_of_card_gt_two hlarge)
    apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e _).mp
    rw [S.normalizer_map_surjective e.toMonoidHom e.surjective]
    exact matrix_normalizer_characteristicTwo hF (by omega) (S.mapSurjective e.surjective)

theorem markedBorel_solvable {n : ℕ} (hm : SymplecticDerivedModel L n)
    (S : Sylow 2 L) : Group.IsSolvable (markedBorel S) := by
  obtain ⟨hn, F, _, _, hF, ⟨e⟩⟩ := hm
  let _ := isSolvable_derived_sylow_normalizer_of_equiv hF hn e S
  exact Group.isSolvable_of_surjective (L.subtype.subgroupMap_surjective _)


/-- The nonbinary marked Borel is the actual standard matrix Borel. -/
theorem exists_standardBorel_equiv {n : ℕ} (hm : SymplecticDerivedModel L n)
    (hn : 1 < n) (S : Sylow 2 L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ Nonempty (markedBorel S ≃* borel (F := F)) := by
  obtain ⟨_, F, _, _, hF, ⟨e₀⟩⟩ := hm
  let _ := EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let e := e₀.trans (derivedEquivFull_of_card_gt_two hlarge)
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) R (unipotentSylow hF (by omega))
  let a := MulAut.conj g
  have hR : (R : Subgroup (Sp F)).map a.toMonoidHom = unipotent :=
    congrArg (fun P : Sylow 2 (Sp F) => (P : Subgroup (Sp F))) hg
  have hN : (normalizer (S : Set L)).map e.toMonoidHom = normalizer (R : Set (Sp F)) :=
    S.normalizer_map_surjective e.toMonoidHom e.surjective
  have hB : (normalizer (R : Set (Sp F))).map a.toMonoidHom = borel (F := F) := by
    change (normalizer ((R : Subgroup (Sp F)) : Set (Sp F))).map a.toMonoidHom = _
    rw [map_equiv_normalizer_eq, hR, borel_eq_normalizer_unipotent]
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, ⟨?_⟩⟩
  exact (equivMapOfInjective (normalizer (S : Set L)) L.subtype L.subtype_injective).symm.trans
    (((e.subgroupMap _).trans (MulEquiv.subgroupCongr hN)).trans
      ((a.subgroupMap _).trans (MulEquiv.subgroupCongr hB)))

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement
