module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Selection
public import Theory.GroupTheory.QuasithinBasic

/-!
# The full-Sylow selection retains its single-factor action

The canonical module in a Sylow overgroup maps into the original canonical
module. The original action kernel therefore centralizes the local module.
Abelianness of the Sylow image descends through this kernel inclusion, just
as solvability does. Consequently the escaping minimal parabolic selected
for the same fixed characteristic pair satisfies every local action premise
of the single-factor source theorem.

Source: Aschbacher--Smith C.1.26--28 and 14.1.11, printed pp.132--134,978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
open ChapterB GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem abelian_sylow_local_action (T : Sylow 2 G)
    (V H : Subgroup G) [V.Normal] (hTH : (T : Subgroup G) ≤ H)
    (U : Subgroup H) [U.Normal] (hUV : U.map H.subtype ≤ V)
    (ha : IsMulCommutative ((T : Subgroup G).map (QuotientGroup.mk' (centralizer (V : Set G))))) :
    IsMulCommutative ((T.subtype hTH : Subgroup H).map
      (QuotientGroup.mk' (centralizer (U : Set H)))) := by
  let f := (QuotientGroup.mk' (centralizer (V : Set G))).comp H.subtype
  have hk : f.ker ≤ centralizer (U : Set H) := by
    intro h hh u hu
    apply Subtype.ext
    have hc : (h : G) ∈ centralizer (V : Set G) := (QuotientGroup.eq_one_iff _).mp hh
    exact hc u (hUV (mem_map_of_mem H.subtype hu))
  have hf : IsMulCommutative ((T.subtype hTH : Subgroup H).map f) := by
    rw [show f = (QuotientGroup.mk' (centralizer (V : Set G))).comp H.subtype from rfl,
      ←Subgroup.map_map,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
    exact ha
  apply commutator_self_eq_bot_iff.mp
  rw [←map_commutator]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  apply le_trans _ hk
  apply (Subgroup.map_eq_bot_iff _).mp
  rw [map_commutator]
  exact commutator_self_eq_bot_iff.mpr hf

/-- The selected escaping subgroup contains the full original Sylow and
retains the abelian Sylow image needed by the cubic fixed-pair theorem. -/
theorem exists_moving_single_minimalParabolic (T : Sylow 2 G)
    (hf : generalizedFitting G = pCore 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hproper : control T D ≠ ⊤)
    (hrank : primeRank 3 G ≤ 2)
    (hs : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G)))
    (ha : IsMulCommutative ((T : Subgroup G).map (QuotientGroup.mk' (centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))))) :
    ∃ (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H),
      IsMinimalParabolicOver (T.subtype hTH) ⊤ ∧ ¬ H ≤ control T D ∧
      generalizedFitting H = pCore 2 H ∧ primeRank 3 H ≤ 2 ∧ Group.IsSolvable H ∧
      ¬ elementaryAbelianMaxJ (T.subtype hTH : Subgroup H) ≤ centralizer
        (normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H) : Set H) ∧
      IsMulCommutative ((T.subtype hTH : Subgroup H).map (QuotientGroup.mk' (centralizer
        (normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H) : Set H)))) := by
  obtain ⟨H,hTH,hP,hout,hfit,hsH,hJ⟩ := exists_moving_solvable_minimalParabolic T hf D hproper hs
  refine ⟨H,hTH,hP,hout,hfit,(primeRank_le_of_injective 3 H.subtype H.subtype_injective).trans hrank,
    hsH,hJ,?_⟩
  exact abelian_sylow_local_action T _ H hTH _ (omegaClosure_map_le T H hTH) ha
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
