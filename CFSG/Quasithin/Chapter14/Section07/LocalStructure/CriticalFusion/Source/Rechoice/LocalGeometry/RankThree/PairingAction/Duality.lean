module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction.Centralizers
public import CFSG.Quasithin.ChapterF.Section09

/-!
# F.9.7 on the literal subgroups of H

The original point is central in H and belongs to O₂(H); the actual U is
normal and elementary abelian. These facts discharge the applicability
conditions of the proved F.9.7. The resulting perfect pairing retains the
actual two centralizer quotients and its commutator evaluation formula.
In particular its characters can be restricted to the original Fcomm.

The source input [U,O₂(H)]=V₁ is earlier 14.5.21(2), produced by qt-14-05.
The rank-three axis application and its character extension are separate
steps; no automorphism-realization conclusion is assumed here.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
F.9.7, 14.5.21(1), and proof of 14.7.70, printed pp.321, 1019, 1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d

/-- Both the elementary and relative-normality hypotheses needed by F.9.7
are consequences of the original section. -/
theorem original_U_pairing_conditions :
    (F.U.subgroupOf F.H).Normal ∧ IsElementaryAbelian 2 (F.U.subgroupOf F.H) := by
  refine ⟨(normal_subgroupOf_iff_le_normalizer d.conjugationSection.section_le).mpr
    d.conjugationSection.normalized, ?_⟩
  let := d.U_elementary
  exact IsElementaryAbelian.subgroupOf d.conjugationSection.section_le

/-- The perfect commutator pairing on the actual relative U and O₂(H).
Its values use the literal inclusion in H, with no replacement quotients. -/
theorem original_commutator_duality
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    letI := (original_U_pairing_conditions d).1
    letI := (original_U_pairing_conditions d).2
    ∃ (eZ : (F.Vi 1).subgroupOf F.H ≃* Multiplicative (ZMod 2))
      (e : ((pCore 2 F.H) ⧸
          (centralizer (F.U.subgroupOf F.H : Set F.H)).subgroupOf (pCore 2 F.H)) ≃*
        Multiplicative (Module.Dual (ZMod 2)
          (Additive ((F.U.subgroupOf F.H) ⧸
            (centralizer (pCore 2 F.H : Set F.H)).subgroupOf (F.U.subgroupOf F.H))))),
      ∀ (q : pCore 2 F.H) (x : F.U.subgroupOf F.H),
        (e (QuotientGroup.mk' _ q)).toAdd (Additive.ofMul (QuotientGroup.mk' _ x)) =
          (eZ ⟨⁅(q : F.H), (x : F.H)⁆, by
            change ⁅((q : F.H) : G), ((x : F.H) : G)⁆ ∈ F.Vi 1
            rw [← h21, commutator_comm]
            exact commutator_mem_commutator (mem_map_of_mem F.H.subtype q.property) x.property⟩).toAdd := by
  let := (original_U_pairing_conditions d).1
  let := (original_U_pairing_conditions d).2
  have hPH : F.Vi 1 ≤ F.H := d.conjugationSection.kernel_le.trans d.conjugationSection.section_le
  have hcentral : (F.Vi 1).subgroupOf F.H ≤ center F.H := by
    intro z hz
    apply mem_center_iff.mpr
    intro h
    apply Subtype.ext
    exact ((show (h : G) ∈ centralizer (F.Vi 1 : Set G) from
      (point_centralizer d).symm ▸ h.property) z hz).symm
  have hUcore : F.U ≤ F.H.pCoreIn 2 := by
    let := d.U_elementary
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U)
      d.conjugationSection.section_le d.conjugationSection.normalized
  have hPQ : (F.Vi 1).subgroupOf F.H ≤ pCore 2 F.H := by
    intro z hz
    exact (mem_map_iff_mem F.H.subtype_injective).mp
      (hUcore (d.conjugationSection.kernel_le hz))
  have hcomm : ⁅pCore 2 F.H, F.U.subgroupOf F.H⁆ ≤ (F.Vi 1).subgroupOf F.H := by
    apply commutator_le.mpr
    intro q hq x hx
    change ⁅(q : G), (x : G)⁆ ∈ F.Vi 1
    rw [← h21, commutator_comm]
    exact commutator_mem_commutator (mem_map_of_mem F.H.subtype hq) hx
  have hcard : Nat.card ((F.Vi 1).subgroupOf F.H) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv]
    simpa using F.card 1 (by decide)
  obtain ⟨eZ, e, he, _⟩ := ChapterF.lemma_F_9_7
    (pCore 2 F.H) (F.U.subgroupOf F.H) ((F.Vi 1).subgroupOf F.H)
    hPQ hcentral hcomm hcard
  exact ⟨eZ, e, he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
