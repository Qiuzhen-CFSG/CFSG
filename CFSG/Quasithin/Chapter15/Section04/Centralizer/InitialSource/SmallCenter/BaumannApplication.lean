module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.Join
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.BaumannSelection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Selection

/-!
# The selected local-class member on the original Chapter15 local

An original family member in the small-center case generates its actual
maximal local with T. This is already a solvable minimal parabolic, and
its original omega-center identity supplies the native Baumann setup.
The selection theorem constructs a genuine C.1.17 local-class member
inside this same M, generating M with the same restricted Sylow subgroup.

No local-class, quotient-model, or module-action premise is assumed.
Source: Aschbacher--Smith 15.4.7 and C.1.26, printed pp.1158 and132.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure FamilySource.ThompsonSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original family input produces the actual local-class member inside M. -/
theorem member_baumann_localClass {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    let S := T.subtype h.sylow_le
    ∃ (K : Subgroup M) (hBK : ChapterB.baumann (S : Subgroup M) ≤ K),
      ChapterC.GlaubermanNiles.InLocalClass (inclusion hBK) ∧ K ⊔ (S : Subgroup M) = ⊤ := by
  let S := T.subtype h.sylow_le
  have hmin := member_minimal_parabolic h hZ
  have hh := ChapterC.RankOne.Solvable.sectionTwoHypotheses_of_proper_subgroup
    h.solvable (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
    (S : Subgroup M) hmin.1.1
  have hv : SectionTwo.vSubgroup S = internalModule T M := closure_eq_internalModule T M h.sylow_le
  have hcore : pCore 2 M = (S : Subgroup M) ⊓ centralizer (SectionTwo.vSubgroup S : Set M) := by
    rw [hv,internal_centralizer T M h.sylow_le h.center_centralizer]
    exact (inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal S)).symm
  have hnot : ¬ SectionTwo.vSubgroup S ≤ centralizer
      (elementaryAbelianMaxJ (S : Subgroup M) : Set M) := by
    rw [hv]
    intro hc
    apply h.thompson_moved
    have hm := map_mono (f := M.subtype) (le_centralizer_iff.mp hc)
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_le,map_centralizer_subtype] at hm
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hm.trans inf_le_right))
  have hu : IsUniqueMaximalContaining (S : Subgroup M) ⊤ := by
    obtain ⟨⟨N,hN,huniq⟩,_⟩ := ChapterB.isMinimalParabolicOver_top_iff S |>.mp hmin
    exact (uniqueMaximalContaining_top_iff _).mpr
      ⟨N,hN.1,hN.2,fun N' ha hb => huniq N' ⟨ha,hb⟩⟩
  have hc : centralizer (omegaOneCenterAmbient (S : Subgroup M) : Set M) = S := by
    have hΩM : omegaOneCenterAmbient (T : Subgroup G) ≤ M :=
      fun _ hz => h.sylow_le ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
    apply map_injective M.subtype_injective
    change (centralizer (omegaOneCenterAmbient (T.subtype h.sylow_le : Subgroup M) : Set M)).map
      M.subtype = ((T.subtype h.sylow_le : Subgroup M)).map M.subtype
    rw [restricted_omega, map_centralizer_subtype,map_subgroupOf_eq_of_le hΩM,
      h.center_centralizer,Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_le,
      inf_eq_right.mpr h.sylow_le]
  exact exists_baumann_localClass hh S hcore hnot hu hc
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
