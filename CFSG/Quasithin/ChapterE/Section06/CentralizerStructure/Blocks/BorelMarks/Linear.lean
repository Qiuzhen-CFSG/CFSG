module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.BorelMarks.LinearControl
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ControlIntersection
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
/-!
# The original linear-block Borel mark

The full block Sylow normalizer belongs to the prescribed characteristic
control overgroup. Its image in the actual SL₂ quotient is the Sylow
normalizer. Sylow conjugacy chooses upper-triangular coordinates, and the
unique proper overgroup property gives equality with the whole Borel.
Pulling this equality back retains the original two-core and intersection;
the field size and parameter are those of the supplied block type.

Source: Aschbacher–Smith C.1.29, printed p.134, applied in E.6.7, p.246.
-/
public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06
open ChapterC Matrix.SpecialLinearGroup
variable {G : Type*} [Group G] [Finite G]

theorem linear_block_borel_of_control
    (S : Sylow 2 G) (N L : Subgroup G)
    (hcontrol : (S : Subgroup G).characteristicNormalizerClosure ≤ N)
    (hL : IsBlock L) (hout : ¬L ≤ N)
    (hmove : L = ⁅L,Stellmacher.elementaryAbelianMaxJ (S : Subgroup G)⁆)
    {n : ℕ} (htype : IsL2EvenBlock L n) : L2BlockBorel L (N.subgroupOf L) n := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  have hPmap : (P : Subgroup L).map L.subtype = L ⊓ S := by
    rw [hP,subgroupOf_map_subtype,inf_comm]
  have hBN := linear_block_sylow_normalizer_le_control S N L hcontrol hout hmove htype P hPmap
  obtain ⟨_,_,F,_,_,hF,_,hmodel⟩ := htype
  obtain ⟨e⟩ := hmodel.quotient_iso
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) F)
    (P.mapSurjective hq) (upperUnipotentSylow F 2)
  let e' := e.trans (MulAut.conj g)
  let q' := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq' : Function.Surjective q' := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hU : (P : Subgroup L).map q' = upperUnipotent F := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((P : Subgroup L).map q).map (MulAut.conj g).toMonoidHom = upperUnipotent F at hh
    have heq : q' = (MulAut.conj g).toMonoidHom.comp q := by ext; rfl
    rw [heq]
    simpa only [Subgroup.map_map] using hh
  have hB : (normalizer (P : Set L)).map q' = rankOneBorel F := by
    rw [P.normalizer_map_surjective q' hq',hU]
  have hk : q'.ker ≤ N.subgroupOf L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
    exact ChapterC.LocalC129.core_le_control_intersection S N L hcontrol hL.subnormal
  have hproper : (N.subgroupOf L).map q' ≠ ⊤ := by
    intro ht
    have hh := congrArg (Subgroup.comap q') ht
    rw [comap_map_eq_self hk,comap_top] at hh
    exact hout (subgroupOf_eq_top.mp hh)
  have hBM : rankOneBorel F ≤ (N.subgroupOf L).map q' := hB ▸ map_mono hBN
  have heq : (N.subgroupOf L).map q' = rankOneBorel F := by
    apply le_antisymm (overgroup_le_rankOneBorel ?_ hproper) hBM
    exact (upperUnipotent F).le_normalizer.trans hBM
  refine ⟨F,inferInstance,inferInstance,hF,e',?_⟩
  have hh := congrArg (Subgroup.comap q') heq
  rwa [comap_map_eq_self hk] at hh

end CFSG.Quasithin.ChapterE.Section06
