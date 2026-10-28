module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupAction.PPerfectFixedCentralizer

/-!
# Two-subgroups fixing the elementary block layer

A two-subgroup and a short subgroup which normalize each other commute
on the latter's U-layer. The proof uses the irreducibility of U/C_U(X)
and the Thompson A × B fixed-point lemma. Applying subnormal residual
normalization shows that the ambient two-core fixes every block's layer.

The fixed-point argument is reused from the checked private
`short_core_centralizes` proof in the E.6 local Baumann centralizer module,
with its unneeded chi-zero and characteristic-two context removed.
Source: Aschbacher--Smith A.1.41 and C.1.11, printed pp.31 and 124.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A two-subgroup normalized by a short group and normalizing it centralizes its layer. -/
theorem IsShort.normalizing_twoGroup_centralizes_blockU {L Q : Subgroup G}
    (hL : IsShort L) (hQ : IsPGroup 2 Q)
    (hLQ : L ≤ normalizer (Q : Set G))
    (hQL : Q ≤ normalizer (L : Set G)) : Q ≤ centralizer ((blockU L).map L.subtype : Set G) := by
  let V := (blockU L).map L.subtype
  let W := V ⊓ centralizer (Q : Set G)
  let Z := (blockU L ⊓ center L).map L.subtype
  have hVL : V ≤ L := map_subtype_le _
  have hLV : L ≤ normalizer (V : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (blockU L))
  have hQV : Q ≤ normalizer (V : Set G) :=
    hQL.trans (normalizer_le_normalizer_characteristic_image L (blockU L))
  have hLW : L ≤ normalizer (W : Set G) :=
    (le_inf hLV (hLQ.trans (normalizer_le_normalizer_centralizer Q))).trans
      inf_normalizer_le_normalizer_inf
  have hWL : W ≤ L := inf_le_left.trans hVL
  have hcore : ⁅Q, L⁆ ≤ pCoreIn 2 L :=
    le_pCoreIn_of_normalizes
      (hQ.to_le (le_normalizer_iff_commutator_le_left.mp hLQ))
      (le_normalizer_iff_commutator_le_right.mp hQL)
      (normalizer_commutator_ge_right Q L)
  have hcomm : ⁅Q, L⁆ ≤ centralizer (V : Set G) := by
    apply hcore.trans
    exact (map_mono hL.core_centralizes_blockU).trans
      (map_centralizer_le_centralizer_image _ L.subtype)
  have hVLcomm : ⁅V, L⁆ = V := by
    have hi := commutator_isPPerfect_idempotent L (pCoreIn 2 L)
      hL.twoPerfect (isPGroup_pCoreIn 2 L)
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    simpa only [pCoreIn, V, blockU, map_commutator, ← MonoidHom.range_eq_map,
      range_subtype] using hi
  let _ : IsElementaryAbelian 2 V := hL.elementary.map L.subtype
  have hZC : Z ≤ centralizer (L : Set G) := by
    intro z hz l hl
    obtain ⟨x, hx, rfl⟩ := hz
    exact congrArg Subtype.val (mem_center_iff.mp hx.2 ⟨l, hl⟩)
  let D : Subgroup L := W.subgroupOf L ⊔ (blockU L ⊓ center L)
  have hnW : (W.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hLW
  let _ := hnW
  have hDU : D ≤ blockU L := by
    apply sup_le ?_ inf_le_left
    intro x hx
    have hxV : (x : G) ∈ (blockU L).map L.subtype := (show W ≤ V from inf_le_left) hx
    obtain ⟨y, hy, he⟩ := hxV
    exact (Subtype.ext he : y = x) ▸ hy
  rcases hL.irreducible.2 D inferInstance le_sup_right hDU with he | he
  · have hWC : W ≤ centralizer (L : Set G) := by
      intro w hw
      have hd : (⟨w, hWL hw⟩ : L) ∈ D := (show W.subgroupOf L ≤ D from le_sup_left) hw
      rw [he] at hd
      exact hZC (mem_map_of_mem L.subtype hd)
    have hz : ⁅V, L⁆ = ⊥ := hL.twoPerfect.centralizes_of_commuting_fixed
      L Q V hQ hLV hQV hcomm (commutator_eq_bot_iff_le_centralizer.mpr hWC)
    have hVbot : V = ⊥ := hVLcomm.symm.trans hz
    exact False.elim (hL.blockU_ne_bot ((map_injective L.subtype_injective)
      (hVbot.trans (map_bot L.subtype).symm)))
  · have hjoin : W ⊔ Z = V := by
      have hh := congrArg (Subgroup.map L.subtype) he
      simpa only [D, Z, V, Subgroup.map_sup, map_subgroupOf_eq_of_le hWL] using hh
    have hWLcomm : ⁅W, L⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hLW
    have hZLcomm : ⁅Z, L⁆ ≤ W := (commutator_eq_bot_iff_le_centralizer.mpr hZC).le.trans bot_le
    have hjoincomm : ⁅W ⊔ Z, L⁆ ≤ W := by
      apply (le_commutatorPreimage_iff (normalizer (W : Set G)) L W (W ⊔ Z) le_rfl).mp
        (sup_le (le_commutatorPreimage W.le_normalizer hWLcomm)
          (le_commutatorPreimage
            ((hZC.trans (centralizer_le hWL)).trans (Subgroup.centralizer_le_normalizer _))
            hZLcomm)) |>.2
    have hVW : V ≤ W := hVLcomm.symm.le.trans (hjoin ▸ hjoincomm)
    exact le_centralizer_iff.mp (hVW.trans inf_le_right)

/-- The ambient two-core fixes the U-layer of every subnormal short block. -/
theorem IsBlock.core_centralizes_blockU {X : Subgroup G} (hX : IsBlock X) :
    pCore 2 G ≤ centralizer ((blockU X).map X.subtype : Set G) := by
  apply hX.short.normalizing_twoGroup_centralizes_blockU pCore_isPGroup
    le_normalizer_of_normal
  exact le_normalizer_of_isSubnormal_isPPerfect X (pCore 2 G)
    hX.subnormal hX.short.twoPerfect pCore_isPGroup le_normalizer_of_normal

end CFSG.Quasithin.ChapterC
