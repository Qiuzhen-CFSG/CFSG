module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Action
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.NormalStructure
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Fusion

/-!
# Normal structure on the literal Chapter 14 subgroup L

From the selected-counterexample setup and `SourceLocalData`, the seed is the
actual O₂(L), elementary of order eight, and the natural marking identifies
the literal quotient with PSL₃(2). Self-centralization identifies the core
with F*(L), so the normal-subgroup theorem proves that L is perfect and
centerless. For any ambient normal N, N ∩ L is 1, the original seed V, or L.
The full source configuration also supplies an ambient involution with
centralizer order 576 and a distinct conjugate in a common Sylow subgroup.

This applies the I.4 normal-structure reduction without assuming an abstract
model for L. `SourceLocalData` is still an explicit, undischarged premise owned
by `qt-d-14414-g2-source`. The I.4.5 ambient recognition callback remains with
`qt-i45-g2-recognition`; this module does not claim the final isomorphism.
Source: Aschbacher–Smith 14.4.3–5, printed pp.1007–1008, and §I.4(G2), p.417.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_normal_structure (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (localData : SourceLocalData L F) :
    Group.IsPerfect L ∧ center L = ⊥ ∧
      ∀ N : Subgroup G, N.Normal → N ⊓ L = ⊥ ∨ N ⊓ L = V ∨ N ⊓ L = L := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  have hVL : V ≤ L := localData.seed_core.le.trans (L.pCoreIn_le 2)
  have hVcore : V.subgroupOf L = pCore 2 L := by
    apply (map_injective L.subtype_injective)
    rw [map_subgroupOf_eq_of_le hVL]
    exact localData.seed_core
  let eV : pCore 2 L ≃* V :=
    (MulEquiv.subgroupCongr hVcore.symm).trans (subgroupOfEquivOfLe hVL)
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    IsElementaryAbelian.of_injective eV.toMonoidHom eV.injective
  have hcard : Nat.card (pCore 2 L) = 8 := by
    rw [Nat.card_congr eV.toEquiv]
    simpa [F.last] using F.card 3 (by decide)
  have hcentral : centralizer (pCore 2 L : Set L) ≤ pCore 2 L := by
    intro x hx
    rw [← hVcore]
    change (x : G) ∈ V
    rw [localData.seed_core, ← h.centralizer_L]
    refine ⟨x.property, ?_⟩
    intro v hv
    have hv' : (⟨v, hVL hv⟩ : L) ∈ pCore 2 L := by rw [← hVcore]; exact hv
    exact congrArg L.subtype (hx ⟨v, hVL hv⟩ hv')
  have hfit : pCore 2 L = generalizedFitting L :=
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hcentral).symm
  let e : (L ⧸ pCore 2 L) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    h.naturalMarking.quotientEquiv.trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm
  have hquot : Nat.card (L ⧸ pCore 2 L) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := e.isSimpleGroup
  refine ⟨GeneralizedFittingEight.perfect (pCore 2 L) hfit hcard hquot,
    GeneralizedFittingEight.center_eq_bot (pCore 2 L) hfit hcard hquot, ?_⟩
  intro N hN
  let := hN
  rcases GeneralizedFittingEight.normal_subgroup_trichotomy
    (pCore 2 L) hfit hcard hquot (N.subgroupOf L) with hn | hn | hn
  · left
    have hh := congrArg (Subgroup.map L.subtype) hn
    simpa only [subgroupOf_map_subtype, Subgroup.map_bot] using hh
  · right; left
    have hh := congrArg (Subgroup.map L.subtype) hn
    rw [subgroupOf_map_subtype] at hh
    exact hh.trans localData.seed_core.symm
  · right; right
    have hh := congrArg (Subgroup.map L.subtype) hn
    simpa only [subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- The remaining source local data already force nontrivial ambient fusion.
This supplies the first fusion witness, not the recognition isomorphism. -/
theorem source_distinguished_fusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (z : G) (S : Sylow 2 G) (g : G), orderOf z = 2 ∧
      Nat.card (centralizer ({z} : Set G)) = 576 ∧ z ∈ (S : Subgroup G) ∧
      g * z * g⁻¹ ∈ (S : Subgroup G) ∧ g * z * g⁻¹ ≠ z := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨z, S, g, hz, hH, hzS, hg⟩ := exists_distinguished_fusion c
  exact ⟨z, S, g, hz, hH ▸ H_card c, hzS, hg⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
