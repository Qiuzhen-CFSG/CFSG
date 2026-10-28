module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.ExceptionalIsomorphisms
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme
public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import Theory.Quasithin.EvenCharacteristic

/-!
# The small rank-two models cannot have a unique maximal two-local

The actual point and line parabolics in PSL₃(2), and the duad and syntheme
parabolics in A₆, generate their groups and contain a common Sylow two-subgroup.
Their intrinsic two-cores have order four. Each therefore lies in a maximal
two-local overgroup. Uniqueness would put both parabolics in the same proper
subgroup, contradicting generation. Sylow conjugacy and genuine model
equivalences retain the original Sylow and maximal two-local.

This proves the A₆ and PSL₂(7) exclusions in the first paragraph of
Aschbacher–Smith, Lemma 2.4.26, printed p.543. It uses no classification or
recognition premise; PSL₂(7) is transported through the actual exceptional
isomorphism to PSL₃(2).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.SmallBlocks
variable {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]

omit [Finite X] in
private theorem core_ne_bot_of_card_four (P : Subgroup X)
    (hc : Nat.card (pCore 2 P) = 4) : pCore 2 P ≠ ⊥ := by
  intro hb
  rw [hb, card_bot] at hc
  norm_num at hc

omit [Finite G] [Finite X] in
private theorem unique_map (e : G ≃* X) (A M : Subgroup G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → A ≤ N → N = M) :
    ∀ N : Subgroup X, IsMaximalTwoLocal N → A.map e.toMonoidHom ≤ N →
      N = M.map e.toMonoidHom := by
  intro N hN hAN
  have hpre : A ≤ N.map e.symm.toMonoidHom := by
    simpa [map_map] using
      map_mono (f := e.symm.toMonoidHom) hAN
  have he := hu _ (Theory.Quasithin.isMaximalTwoLocal_map e.symm hN) hpre
  have hm := congrArg (map e.toMonoidHom) he
  simpa [map_map] using hm

private theorem false_of_generating_core_pair (B : Sylow 2 X) (P Q : Subgroup X)
    (hBP : (B : Subgroup X) ≤ P) (hBQ : (B : Subgroup X) ≤ Q)
    (hP : pCore 2 P ≠ ⊥) (hQ : pCore 2 Q ≠ ⊥) (hgen : P ⊔ Q = ⊤)
    (T : Sylow 2 G) (M : Subgroup G) (hM : M ≠ ⊤)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (e : G ≃* X) : False := by
  let R : Sylow 2 X := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R B
  let f : G ≃* X := e.trans (MulAut.conj g)
  have hTB : (T : Subgroup G).map f.toMonoidHom = (B : Subgroup X) := by
    rw [← hg]
    change (T : Subgroup G).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) =
      ((T : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom
    rw [map_map]
  have huni := unique_map f (T : Subgroup G) M hu
  rw [hTB] at huni
  obtain ⟨NP, hNP, hPN⟩ :=
    Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot P hP
  obtain ⟨NQ, hNQ, hQN⟩ :=
    Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot Q hQ
  have hPM : P ≤ M.map f.toMonoidHom := (huni NP hNP (hBP.trans hPN)) ▸ hPN
  have hQM : Q ≤ M.map f.toMonoidHom := (huni NQ hNQ (hBQ.trans hQN)) ▸ hQN
  have htop : M.map f.toMonoidHom = ⊤ := top_unique (hgen ▸ sup_le hPM hQM)
  apply hM
  apply (map_injective (f := f.toMonoidHom) f.injective)
  rw [htop, map_top_of_surjective f.toMonoidHom f.surjective]

/-- The actual binary projective linear group is excluded by the two
generating flag parabolics and their nontrivial two-cores. -/
theorem not_psl3_two (T : Sylow 2 G) (M : Subgroup G) (hM : M ≠ ⊤)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ¬ Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rintro ⟨e⟩
  open Matrix.PSL3Two in
  have hgen : pointParabolic ⊔ lineParabolic = ⊤ :=
    isCoatom_pointParabolic.sup_eq_top_of_ne isCoatom_lineParabolic pointParabolic_ne_line
  open Matrix.PSL3Two in
  exact false_of_generating_core_pair borelSylow pointParabolic lineParabolic
    (by rw [coe_borelSylow, ← pointParabolic_inf_line]; exact inf_le_left)
    (by rw [coe_borelSylow, ← pointParabolic_inf_line]; exact inf_le_right)
    (core_ne_bot_of_card_four _ pointParabolic_core_data.2)
    (core_ne_bot_of_card_four _ lineParabolic_core_data.2) hgen T M hM hu e

/-- The actual A₆ model is excluded by its duad and syntheme parabolics.
The uniqueness assumption is among maximal two-locals, not all maximals. -/
theorem not_alternating_six (T : Sylow 2 G) (M : Subgroup G) (hM : M ≠ ⊤)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ¬ Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  open Theory.SpecificGroups.SymmetricSix in
  exact false_of_generating_core_pair a6BorelSylow a6DuadStabilizer a6SynthemeStabilizer
    a6Borel_le_duadStabilizer a6Borel_le_synthemeStabilizer
    (core_ne_bot_of_card_four _ a6DuadCore_card)
    (core_ne_bot_of_card_four _ a6SynthemeCore_card) a6_parabolics_sup T M hM hu e

/-- PSL₂(7) is excluded through its concrete exceptional isomorphism.
The coefficient field in the supplied model may be any field of order seven. -/
theorem not_psl2_seven (T : Sylow 2 G) (M : Subgroup G) (hM : M ≠ ⊤)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ¬ ClassicalGroup.IsPSL G 2 7 := by
  rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  exact not_psl3_two T M hM hu
    ⟨e.trans (psl2_equiv_psl3Two_of_card_seven hcard).some⟩

/-- The two small rank-two alternatives in source 2.4.26 are eliminated
under the literal simple-QTKE and unique-two-local hypotheses. -/
theorem source_small_rank_two_exclusions {K : GroupClass} (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ¬ ClassicalGroup.IsPSL G 2 7 ∧ ¬ Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  let := hG.simple
  have hproper := twoLocal_ne_top_of_nonabelian_simple hG.nonabelian hM.1
  exact ⟨not_psl2_seven T M hproper hu, not_alternating_six T M hproper hu⟩

end CFSG.Quasithin.Chapter2.SmallBlocks
