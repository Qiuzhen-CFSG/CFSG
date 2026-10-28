module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.AlphaOrder
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SeedFaithfulness
public import Stellmacher.BaumannIntermediate

/-!
# The orbit Borel in the common local overgroup

The paired natural action places Baum(T) in (T ∩ L₀)O₂(L₀T).
Both factors are normalized by the original orbit Borel, and Baumann
heredity therefore gives B₀ ≤ N_G(Baum(T)). The seed-faithfulness proof
constructs a common maximal two-local overgroup of this normalizer and H.
Thus B₀ and H lie in the same actual local overgroup before Hall placement.

The intermediate two-core is retained; Baum(T) ≤ L₀ is not assumed.
These are the inputs to the remaining component-normalization argument
on printed p.746, owned by the moving-Hall source assembly.
Source: Aschbacher–Smith 10.2.2(3)–(4), 10.2.3, printed pp.744–746.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]

/-- The original Baumann subgroup lies in the orbit Sylow times the
local-join two-core, before block recovery or Hall placement. -/
theorem original_baumann_le_common_two
    {H : Subgroup G} {B : Subgroup H} (ctx : MovingHall.Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    baumann (T : Subgroup G) ≤ ((T : Subgroup G) ⊓ localOrbit T L) ⊔
      (localJoin T L).pCoreIn 2 := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hP := source_natural_minimal_parabolic D e n hn hF ctx.nonnormal
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving
  obtain ⟨d,E,⟨c⟩,hexchange⟩ := ctx.original_paired_linear D n hn hF e
  obtain ⟨_,_,_,_,⟨_,hBq⟩,_⟩ :=
    RankOneBaumann.PairedFactorOrbit.source_images_and_fixedSpace S hP
      U hU hJ q hq hk d E c hexchange
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [source_natural_paired_field_card D n hn hF e ctx.nonnormal hJ d E c hexchange,hF]
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hp
    omega
  let A := SL(2,E.Carrier)
  let : Group.IsPerfect A := GorensteinWalter.sl2_isPerfect_of_card_gt_three E.Carrier hlarge
  let : Group.IsPerfect (A × A) := ⟨by
    rw [_root_.commutator_def,←top_prod_top,commutator_prod_prod]
    simp only [←_root_.commutator_def,Group.IsPerfect.commutator_eq_top]⟩
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := c.action.groupEquiv.symm.toMonoidHom) c.action.groupEquiv.symm.surjective
  let : Group.IsNilpotent ((X ⧸ C) ⧸ pResidual 2 (X ⧸ C)) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  have hY : Y ≤ (pResidual 2 X).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact le_of_isPerfect_of_solvable_quotient Y _
  have hkr : q.ker = pCore 2 X := by
    rw [hk]
    exact source_natural_local_module_kernel_eq_twoCore D n hn hF e ctx.nonnormal hJ
  have hB : baumann (S : Subgroup X) ≤ ((S : Subgroup X) ⊓ pResidual 2 X) ⊔ pCore 2 X := by
    have hm := map_le_iff_le_comap.mp (hBq.le.trans (inf_le_right.trans hY))
    rw [comap_map_eq,hkr] at hm
    intro x hx
    obtain ⟨r,hr,k,hk,he⟩ := mem_sup_of_normal_right.mp (hm hx)
    have hrS : r ∈ (S : Subgroup X) := by
      have hh := (S : Subgroup X).mul_mem hx.1
        ((S : Subgroup X).inv_mem (pCore_isPGroup.le_sylow_of_normal S hk))
      rwa [←he,mul_inv_cancel_right] at hh
    rw [←he]
    exact mul_mem_sup ⟨hrS,hr⟩ hk
  have hBm := map_mono (f := X.subtype) hB
  have hSm : (S : Subgroup X).map X.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le le_sup_right
  have hBmEq := baumann_map_injective X.subtype X.subtype_injective (S : Subgroup X)
  change (baumann (S : Subgroup X)).map X.subtype = baumann ((S : Subgroup X).map X.subtype) at hBmEq
  rw [hSm] at hBmEq
  rwa [Subgroup.map_sup,Subgroup.map_inf _ _ _ X.subtype_injective,
    source_join_residual D,hBmEq,hSm] at hBm
/-- Source 10.2.2(3): the actual orbit Borel normalizes Baum(T), with the
local-join two-core retained in the intermediate two-subgroup. -/
theorem borel_normalizes_baumann
    {H : Subgroup G} {B : Subgroup H} (ctx : MovingHall.Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    sourceOrbitBorel T L ≤ normalizer (baumann (T : Subgroup G) : Set G) := by
  let Q := (localJoin T L).pCoreIn 2
  let P := ((T : Subgroup G) ⊓ localOrbit T L) ⊔ Q
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (localJoin T L) (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right))
    exact hh.trans_eq (map_subgroupOf_eq_of_le le_sup_right)
  have hBP : baumann (T : Subgroup G) ≤ P :=
    original_baumann_le_common_two D ctx n hn hF e
  have he : baumann P = baumann (T : Subgroup G) :=
    baumann_eq_of_intermediate (T : Subgroup G) P hBP (sup_le inf_le_left hQT)
  have hB : sourceOrbitBorel T L ≤ localOrbit T L := (map_subtype_le _).trans inf_le_left
  have hR : sourceOrbitBorel T L ≤ normalizer
      (((T : Subgroup G) ⊓ localOrbit T L : Subgroup G) : Set G) :=
    (map_subtype_le _).trans inf_le_right
  have hQ : sourceOrbitBorel T L ≤ normalizer (Q : Set G) :=
    (hB.trans (show localOrbit T L ≤ localJoin T L from le_sup_left)).trans
      ((localJoin T L).le_normalizer.trans (normalizer_le_normalizer_characteristic_image
        (localJoin T L) (pCore 2 (localJoin T L))))
  have hN : sourceOrbitBorel T L ≤ normalizer (P : Set G) :=
    (le_inf hR hQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rw [←he]
  exact hN.trans (normalizer_le_normalizer_baumann P)

/-- The original orbit Borel and H lie in one actual maximal two-local
subgroup, with no Hall-placement or seed-centralizer assumption. -/
theorem borel_common_local_overgroup
    {H : Subgroup G} {B : Subgroup H} (ctx : MovingHall.Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e) :
    ∃ M₁ : Subgroup G, IsMaximalTwoLocal M₁ ∧
      normalizer (baumann (T : Subgroup G) : Set G) ⊔ H ≤ M₁ ∧
      sourceOrbitBorel T L ⊔ H ≤ M₁ := by
  obtain ⟨M₁,hM,hNH⟩ := common_local_overgroup D ctx n hn hF e mark
  exact ⟨M₁,hM,hNH,(sup_le_sup_right (borel_normalizes_baumann D ctx n hn hF e) H).trans hNH⟩

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
