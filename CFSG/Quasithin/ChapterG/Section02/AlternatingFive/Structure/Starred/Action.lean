module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.Starred.Coordinates
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.TerminalReduction
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor

/-!
# A faithful five-point action of the actual star quotient

The normal A₅-image of L has a two-group quotient in LT/O₂(LT), whose
two-core is trivial. Hence it is self-centralizing. The proved
Aut(A₅) = S₅ theorem gives a faithful five-point action extending the
original marking. The image of L₁ is the previously derived A₄ Borel.
The image of U is a nontrivial two-subgroup of the corresponding S₄,
normalized by that A₄. These facts discharge the source assumptions for
the finite Borel calculation; no singular point is added as a premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(1), printed p.334, using the G.2.3 argument on pp.333–334.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Theory.SpecificGroups.Alternating
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

theorem star_L_normal : (D.star D.L).Normal := by
  let : (D.L.subgroupOf D.LT).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le D.L.le_normalizer d.setup.T_normalizes_L)
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

noncomputable def starAction : D.Star →* Equiv.Perm (Fin 5) :=
  let := d.star_L_normal
  FiveExtensionAction.action (D.star D.L) d.model

theorem starAction_on_L (l : D.star D.L) : d.starAction l = (d.model l).val := by
  let := d.star_L_normal
  exact FiveExtensionAction.action_on_subgroup _ _ l

theorem starAction_injective : Function.Injective d.starAction := by
  let := d.star_L_normal
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (D.star D.L) := d.model.isSimpleGroup
  have hn : ¬ IsMulCommutative (D.star D.L) := by
    intro h
    have hA : IsMulCommutative (alternatingGroup (Fin 5)) :=
      isMulCommutative_iff.mpr (fun a b => d.model.symm.injective (by
        simpa only [map_mul] using (isMulCommutative_iff.mp h) (d.model.symm a) (d.model.symm b)))
    have := alternatingGroup.isMulCommutative_iff_card_le_three.mp hA
    norm_num at this
  have hsup : D.star D.L ⊔ D.star D.T = ⊤ := by
    rw [← binary_star_sup D.L D.T le_sup_left le_sup_right]
    change D.star D.LT = ⊤
    rw [Setup.star, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hquot : IsPGroup 2 (D.Star ⧸ D.star D.L) :=
    isPGroup_quotient_of_sup_eq_top _ _
      (d.setup.toBaseHypothesis.binary_T_isPGroup.comap_subtype.map _) hsup
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : pCore 2 D.Star = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 D.LT)
    have hk : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    have he := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk
    have hm := congrArg (Subgroup.map q) he
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
    exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  exact FiveExtensionAction.action_injective _ _
    (Theory.GroupTheory.centralizer_eq_bot_of_simple_two_quotient _ hn hquot
      hcore)

theorem star_L_action : (D.star D.L).map d.starAction = alternatingGroup (Fin 5) := by
  ext s
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (d.starAction_on_L ⟨l, hl⟩).symm ▸ (d.model ⟨l, hl⟩).property
  · intro hs
    obtain ⟨l, hl⟩ := d.model.surjective ⟨s, hs⟩
    exact ⟨l, l.property, (d.starAction_on_L l).trans (congrArg Subtype.val hl)⟩

theorem star_local_action : (D.star D.L₁).map d.starAction =
    alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 5)) d.pointIndex := by
  have hL : D.star D.L₁ ≤ D.star D.L :=
    binary_star_mono (show D.L₁ ≤ D.L from (map_subtype_le _).trans inf_le_left)
  have hhom : d.starAction.comp (D.star D.L).subtype =
      (alternatingGroup (Fin 5)).subtype.comp d.model.toMonoidHom := by
    apply MonoidHom.ext
    exact d.starAction_on_L
  rw [← map_subgroupOf_eq_of_le hL, map_map, hhom, ← map_map, d.star_local_model]
  ext s
  exact ⟨fun ⟨a, ha, he⟩ => he ▸ ⟨a.property, ha⟩,
    fun ⟨ha, hs⟩ => ⟨⟨s, ha⟩, hs, rfl⟩⟩

omit d [Finite G] in
private theorem star_normalizes {A B : Subgroup G} (h : A ≤ normalizer (B : Set G)) :
    D.star A ≤ normalizer (D.star B : Set D.Star) := by
  have hn : A.subgroupOf D.LT ≤ normalizer (B.subgroupOf D.LT : Set D.LT) :=
    (comap_mono h).trans (B.le_normalizer_comap D.LT.subtype)
  exact (map_mono hn).trans ((B.subgroupOf D.LT).le_normalizer_map _)

theorem star_U_normalizes_local : D.star D.U ≤ normalizer (D.star D.L₁ : Set D.Star) :=
  star_normalizes (d.setup.U_normal_in_T.1.trans (T_normalizes_L₁ d.setup.toBaseHypothesis))

theorem star_local_normalizes_U : D.star D.L₁ ≤ normalizer (D.star D.U : Set D.Star) :=
  star_normalizes ((le_sup_left.trans d.setup.local_le).trans
    (le_normalizer_conjugateSpanBy D.V D.H))

theorem starAction_U_control :
    IsPGroup 2 ((D.star D.U).map d.starAction) ∧
    (D.star D.U).map d.starAction ≠ ⊥ ∧
    (D.star D.U).map d.starAction ≤
      MulAction.stabilizer (Equiv.Perm (Fin 5)) d.pointIndex ∧
    alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 5)) d.pointIndex ≤
      normalizer ((D.star D.U).map d.starAction : Set (Equiv.Perm (Fin 5))) := by
  refine ⟨(d.setup.U_isPGroup.comap_subtype.map _).map _, ?_, ?_, ?_⟩
  · intro h
    apply d.star_U_ne_bot
    exact (map_injective d.starAction_injective) (h.trans (Subgroup.map_bot _).symm)
  · have h := (map_mono (f := d.starAction) d.star_U_normalizes_local).trans
      ((D.star D.L₁).le_normalizer_map _)
    rwa [d.star_local_action, FiveBorelCentralFactor.even_stabilizer_normalizer] at h
  · rw [← d.star_local_action]
    exact (map_mono d.star_local_normalizes_U).trans ((D.star D.U).le_normalizer_map _)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
