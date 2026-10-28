module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FivePairControl
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.UniformPair
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The actual selected A5 block from external C.1.23

Use the canonical pair on the original external Baumann subgroup. If its
first member were central, or its second member normal, the selected
component would lie in the characteristic-normalizer control subgroup.
Both contradict its proved outside placement. The remaining typed block
maps to that same component, and two-perfect commutator idempotence gives
its literal support [U,L].

Source: Aschbacher–Smith C.1.23 and C.1.28, pp.129–130,133–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles FiveBlockSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The external C123 theorem produces the same ambient selected block. -/
theorem selected_five_block_of_external_action
    (T : Sylow 2 G) (hTne : (T : Subgroup G) ≠ ⊥)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (L : Subgroup G) (hL : L.IsCComponent)
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hout : ¬ L ≤ M)
    (N : Subgroup G) (hLN : L ≤ N)
    (R : Sylow 2 N) (hBR : baumann (T : Subgroup G) ≤ (R : Subgroup N).map N.subtype)
    (hRT : (R : Subgroup N).map N.subtype ≤ T)
    (hfit : generalizedFitting N = pCore 2 N)
    [Normal (L.subgroupOf N)]
    (hprod : L.subgroupOf N ⊔ (R : Subgroup N) = ⊤)
    (eL : ((L.subgroupOf N) ⧸ pCore 2 (L.subgroupOf N)) ≃* alternatingGroup (Fin 5))
    (V : Subgroup N) [V.Normal] [IsElementaryAbelian 2 V]
    (hV : V.map N.subtype = ⁅U,L⁆)
    (p : N →* Equiv.Perm (Fin 5)) (hp : Function.Surjective p)
    (hk : p.ker = centralizer (V : Set N))
    (hLp : (L.subgroupOf N).map p = alternatingGroup (Fin 5))
    (f : Additive V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (he : ∀ g v, f (NormalElementaryQuotient.representation V p hp hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (f v))
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup N) ≤ centralizer (V : Set N)) :
    IsChiBlockIn L ∧ L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U := by
  let A := L.subgroupOf N
  have hAN : A.map N.subtype = L := map_subgroupOf_eq_of_le hLN
  obtain ⟨D,hD⟩ := exists_baumann_universal_pair.{u,u} (T : Subgroup G) T.isPGroup' hTne
  have hx := external_source_conclusion (T : Subgroup G) N R hBR hRT hfit A
    (hL.subgroupOf hLN) hprod eL V p hp hk hLp f.toLinearMap f.surjective he
    (fun v hv _ _ => by
      have hz : v = 0 := f.injective (hv.trans (map_zero f).symm)
      subst v
      exact map_zero _) hJ D hD
  have hBN : baumann (T : Subgroup G) ≤ N := hBR.trans (map_subtype_le _)
  have hfirstN : firstAmbient (T : Subgroup G) D ≤ N :=
    (firstAmbient_le_omegaCenter (T : Subgroup G) D).trans ((omegaCenter_le_baumann _).trans hBN)
  have hsecondN : secondAmbient (T : Subgroup G) D ≤ N := (map_subtype_le _).trans hBN
  rcases hx with hc | hn | ⟨hb,ha,hm,hs,hu⟩
  · have hn : N ≤ normalizer (firstAmbient (T : Subgroup G) D : Set G) := by
      apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro n hn x hx
      obtain ⟨z,hz,hzx⟩ := hc hx
      rw [←hzx]
      exact (congrArg N.subtype (mem_center_iff.mp hz ⟨n,hn⟩)).symm
    exact (hout (hLN.trans (hn.trans ((firstAmbient_normalizer_le_control
      (T : Subgroup G) T.isPGroup' D).trans hcpu)))).elim
  · let : ((secondAmbient (T : Subgroup G) D).subgroupOf N).Normal := hn
    have hN : N ≤ normalizer (secondAmbient (T : Subgroup G) D : Set G) := by
      have hh := ((secondAmbient (T : Subgroup G) D).subgroupOf N).le_normalizer_map N.subtype
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
        map_subgroupOf_eq_of_le hsecondN] using hh
    let := D.second_characteristic
    exact (hout (hLN.trans (hN.trans ((characteristic_baumann_normalizer_le_control
      (T : Subgroup G) D.second D.second_ne_bot).trans hcpu)))).elim
  · let e : A ≃* L := subgroupOfEquivOfLe hLN
    have hblock : IsChiBlockIn L := by
      let := hL.perfect
      exact ⟨⟨inferInstance,RankOne.Solvable.isShort_of_equiv e hb.short,hL.subnormal⟩,
        Or.inr ⟨5,by decide,RankOne.Solvable.isAlternatingBlock_of_equiv e ha⟩⟩
    have hpL : IsPPerfect 2 L := by
      let := hL.perfect
      intro Q hQ hpQ
      let := hQ
      let : Group.IsNilpotent (L ⧸ Q) := hpQ.isNilpotent
      apply top_unique
      rw [←solvableResidual_eq_top (G := L)]
      exact solvableResidual_le_of_solvable_quotient Q
    have hsame : (blockU A).map (N.subtype.comp A.subtype) = (blockU L).map L.subtype := by
      rw [←RankOne.Solvable.blockU_map_equiv e,map_map]
      rfl
    rw [hsame,hAN,hV] at hs
    rw [hAN] at hm
    have hid : ⁅(⁅U,L⁆ : Subgroup G),L⁆ = ⁅U,L⁆ :=
      commutator_isPPerfect_idempotent L U hpL (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
    exact ⟨hblock,hm,hs.trans hid,(hs.trans hid).le.trans (commutator_le_left U L)⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
