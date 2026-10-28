module
public import Theory.GroupAction.BinaryNaturalPlaneSeed
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Pair
public import Theory.GroupTheory.NormalClosureCentralizerCore
/-!
# The original characteristic-pair seed in a natural plane

Transport the binary-plane centralizer theorem through the actual subgroup
inclusion M ↪ G. The nontrivial first member's central restriction lies in
the original localModule and is centralized by the prescribed Sylow group.
Its full centralizer inside M is therefore C_M(V(M)) T. No choice of a
new pair or replacement module is made.
Source: Aschbacher–Smith 14.1.7 and 14.1.11, printed pp.977–978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterB ChapterC.GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]

theorem plane_fixed_pair_centralizer_factorization
    (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    [((localModule T M).subgroupOf M).Normal]
    [IsElementaryAbelian 2 ((localModule T M).subgroupOf M)]
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (c : Additive ((localModule T M).subgroupOf M) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (e : (M ⧸ centralizer (((localModule T M).subgroupOf M) : Set M)) ≃* SL(2,ZMod 2))
    (hc : ∀ g v, c (NormalElementaryQuotient.representation ((localModule T M).subgroupOf M)
      (QuotientGroup.mk' (centralizer (((localModule T M).subgroupOf M) : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g v) =
      Representation.specialLinearNatural 2 (e g) (c v)) :
    M ⊓ centralizer (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D : Set G) =
      (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G) := by
  let A := ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D
  let V := localModule T M
  have hAV : A ≤ V := inf_le_left.trans (le_conjugateSpanBy _ _)
  have hVM : V ≤ M := conjugateSpanBy_le_self
    (fun z hz => hTM ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  have hAM := hAV.trans hVM
  have hne : A.subgroupOf M ≠ ⊥ := by
    intro he
    have hh := congrArg (map M.subtype) he
    rw [map_subgroupOf_eq_of_le hAM,Subgroup.map_bot] at hh
    exact ChapterC.RankOne.ChiProduct.FixedPair.firstSeed_ne_bot T D hh
  have hSA : ((T.subtype hTM : Sylow 2 M) : Subgroup M) ≤
      centralizer (A.subgroupOf M : Set M) := by
    intro t ht z hz
    apply Subtype.ext
    exact (((mem_omegaOneCenterAmbient_iff _ (z : G)).mp hz.1).2.2 t ht).symm
  have h := Theory.GroupAction.BinaryNaturalPlaneSeed.centralizer_eq_sylow_sup
    (V.subgroupOf M) (T.subtype hTM) (A.subgroupOf M) (comap_mono hAV) hne hSA c e hc
  have hh := congrArg (map M.subtype) h
  rw [Subgroup.map_centralizer_subtype, map_subgroupOf_eq_of_le hAM,
    Subgroup.map_sup, Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,
    Subgroup.map_centralizer_subtype,map_subgroupOf_eq_of_le hVM,sup_comm] at hh
  exact hh
end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
