module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.FixedSpace
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Characteristic two for the block–Sylow join in E.6.23

The normal closure of a short subnormal subgroup in an odd-core-free
centralizer has no ordinary components: every component centralizes every
conjugate block, since it cannot lie in a characteristic-two short group.
Its odd core also vanishes, so this normal closure has characteristic two.
Adjoining the common Sylow subgroup preserves characteristic two, and
restriction to the actual join of the block with that Sylow finishes.

The construction permits Q to move X. It imposes no normality of X in
C_G(A), in G, or under Q, and uses no block-persistence conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265), with the component calculus and E.6.21.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
variable {G : Type*} [Group G] [Finite G]

private theorem component_not_le_short {B D : Subgroup G}
    (hB : ChapterC.IsShort B) (hD : IsComponent G D) : ¬ D ≤ B := by
  intro hDB
  have hc := hD.subgroupOf hDB
  let _ := hc.2
  let _ : IsSimpleGroup ((D.subgroupOf B) ⧸ center (D.subgroupOf B)) := IsQuasisimple.simple
  let _ : Nontrivial (D.subgroupOf B) :=
    (QuotientGroup.mk'_surjective (center (D.subgroupOf B))).nontrivial
  have hd : D.subgroupOf B ≤ pCore 2 B :=
    (component_le_generalizedFitting B _ hc).trans hB.fitting.le
  let _ := (pCore_isPGroup.to_le hd).isNilpotent
  exact Group.IsPerfect.not_isSolvable (D.subgroupOf B) inferInstance

private theorem block_normalClosure_characteristicTwo {B : Subgroup G}
    (hB : ChapterC.IsBlock B) (ho : pPrimeCore 2 G = ⊥) :
    HasCharacteristicTwo (normalClosure (B : Set G)) := by
  let N := normalClosure (B : Set G)
  have hn : componentLayer N = ⊥ := by
    apply sSup_eq_bot.mpr
    intro L hL
    let D := L.map N.subtype
    let _ := hL.2
    have hD : IsComponent G D :=
      ⟨hL.1.trans' (inferInstance : N.Normal).isSubnormal,
        IsQuasisimple.of_mulEquiv (L.equivMapOfInjective N.subtype N.subtype_injective)⟩
    have hND : N ≤ centralizer (D : Set G) := by
      apply (closure_le _).mpr
      intro x hx
      obtain ⟨b, hb, hx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨g, rfl⟩ := isConj_iff.mp hx
      have hBg := hB.map_equiv (MulAut.conj g)
      have hc : ⁅D, B.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
        (hD.subnormal_dichotomy _ hBg.subnormal).resolve_left
          (component_not_le_short hBg.short hD)
      rw [commutator_comm] at hc
      exact (commutator_eq_bot_iff_le_centralizer.mp hc) (mem_map.mpr ⟨b, hb, rfl⟩)
    have hcomm : ⁅D, D⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      ((map_subtype_le L).trans hND)
    let _ := hD.2
    rw [commutator_eq_self] at hcomm
    exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp hcomm
  have hNo : pPrimeCore 2 N = ⊥ :=
    Subgroup.IsSubnormal.pPrimeCore_eq_bot ho N (inferInstance : N.Normal).isSubnormal
  have hNF : generalizedFitting N = pCore 2 N := by
    rw [generalizedFitting, hn, sup_bot_eq, Fitting_eq_pcore N 2 hNo]
  change centralizer (pCore 2 N : Set N) ≤ pCore 2 N
  rw [← hNF]
  exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le

private theorem block_sylow_join_characteristicTwo {B : Subgroup G}
    (hB : ChapterC.IsBlock B) (ho : pPrimeCore 2 G = ⊥) (P : Sylow 2 G) :
    HasCharacteristicTwo (B ⊔ (P : Subgroup G) : Subgroup G) := by
  let N := normalClosure (B : Set G)
  let J := N ⊔ (P : Subgroup G)
  have hNJ : N ≤ J := le_sup_left
  have hPJ : (P : Subgroup G) ≤ J := le_sup_right
  have hN : HasCharacteristicTwo (N.subgroupOf J) :=
    (block_normalClosure_characteristicTwo hB ho).of_equiv (subgroupOfEquivOfLe hNJ).symm
  have hgen : N.subgroupOf J ⊔ (P : Subgroup G).subgroupOf J = ⊤ := by
    apply (Subgroup.map_injective J.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNJ, map_subgroupOf_eq_of_le hPJ,
      ← MonoidHom.range_eq_map, range_subtype]
  have hJ : HasCharacteristicTwo J :=
    centralizer_pCore_le_of_normal_pGroup_quotient (N.subgroupOf J) hN
      (isPGroup_quotient_of_sup_eq_top (N.subgroupOf J) ((P : Subgroup G).subgroupOf J)
        P.isPGroup'.comap_subtype hgen)
  have hKJ : B ⊔ (P : Subgroup G) ≤ J := sup_le (le_normalClosure.trans hNJ) hPJ
  have hp : (P.subtype hPJ : Sylow 2 J) ≤ (B ⊔ (P : Subgroup G)).subgroupOf J := by
    intro x hx
    exact mem_sup_right hx
  exact (show HasCharacteristicTwo ((B ⊔ (P : Subgroup G)).subgroupOf J) from
    centralizer_pCore_le_of_sylow_le (P.subtype hPJ) _ hp hJ).of_equiv
      (subgroupOfEquivOfLe hKJ)

/-- The actual block overgroup generated with the common Sylow has characteristic two.
No normality of X under Q is assumed. -/
theorem block_join_characteristicTwo
    {𝒦 : GroupClass} {T : Sylow 2 G} {M V A X : Subgroup G}
    (h : HypothesisE61 𝒦 T M V) (h21 : OddCoreFree V)
    (hA : A ∈ obstructionFamily M V) (hX : CentralizerBlock A X) :
    HasCharacteristicTwo (X ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) := by
  let H := centralizer (A : Set G)
  obtain ⟨P, hP⟩ := h.sylow_obstruction hA
  have he : ((X.subgroupOf H) ⊔ (P : Subgroup H)).map H.subtype =
      X ⊔ sylowCentralizer (T : Subgroup G) V := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hX.1, hP]
  exact ((block_sylow_join_characteristicTwo hX.2 (h21 A hA.1 hA.2.1) P).of_equiv
    (((X.subgroupOf H) ⊔ (P : Subgroup H)).equivMapOfInjective H.subtype
      H.subtype_injective)).of_equiv (MulEquiv.subgroupCongr he)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
