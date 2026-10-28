module
public import Theory.GroupTheory.PResidual.SymmetricThreeProducts
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.ThompsonAction
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.OddResidual

/-!
# The odd-by-two Thompson–Sylow action

The actual Thompson image is a subgroup of the solvable offender product.
Its internal S₃ coordinates give an odd two-residual. Adjoining the original
Sylow image preserves an odd normal subgroup with two-group quotient, so the
entire Thompson–Sylow action has odd two-residual. The representation and
quotient map are precisely the local action of the selected conjugate span.

Source: Aschbacher–Smith, original 14.1.4, printed p.976.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

theorem source_thompsonSylow_action_oddResidual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {N : Subgroup G} (hN : N ∈ Chapter1.HOver G (T : Set G))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T N : Set G)) :
    Odd (Nat.card (pResidual 2
      (((elementaryAbelianMaxJ (⊤ : Subgroup N)) ⊔ (T.subtype hN.2 : Subgroup N)).map
        (localActionMap (centralInvolutions T) N)))) := by
  let U := (localModule T N).subgroupOf N
  let := (localModule_reduced_from_source hG T hN).normal
  let := (localModule_reduced_from_source hG T hN).elementary
  let q := localActionMap (centralInvolutions T) N
  let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (localActionKernel_eq_centralizer T hN.2))
  obtain ⟨d,_,_,_,hd⟩ := local_thompson_factors_from_source
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hN hJ
  let I := (elementaryAbelianMaxJ (⊤ : Subgroup N)).map q
  let S := (T.subtype hN.2 : Subgroup N).map q
  let D := I ⊔ S
  have hIO : I ≤ offenderSubgroup ρ := by
    rw [show I = _ from hd]
    exact iSup_le fun i => iSup_le fun _ => d.toSolvableFFFactors.factor_le_offenderSubgroup i
  let : (elementaryAbelianMaxJ (⊤ : Subgroup N)).Characteristic :=
    elementaryAbelianMaxJ_top_characteristic
  let : I.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let f : I.subgroupOf D →* offenderSubgroup ρ := {
    toFun x := ⟨x.val.val,hIO x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg
      (fun z : offenderSubgroup ρ => (z : LocalActionQuotient (centralInvolutions T) N)) he))
  have hodd := d.toSolvableFFFactors.odd_pResidual_of_embedding f hf
  have hS : IsPGroup 2 (S.subgroupOf D) :=
    ((T.subtype hN.2).isPGroup'.map q).of_equiv (subgroupOfEquivOfLe
      (show S ≤ D from le_sup_right)).symm
  have hgen : I.subgroupOf D ⊔ S.subgroupOf D = ⊤ := by
    rw [← subgroupOf_sup (show I ≤ D from le_sup_left) (show S ≤ D from le_sup_right)]
    exact subgroupOf_self _
  obtain ⟨L,hL,hLodd,hquot⟩ := exists_odd_normal_two_quotient_of_normal_sup
    (I.subgroupOf D) (S.subgroupOf D) hodd hS hgen
  let := hL
  have hres : pResidual 2 D ≤ L := sInf_le ⟨hL,hquot⟩
  have hDodd : Odd (Nat.card (pResidual 2 D)) := hLodd.of_dvd_nat (card_dvd_of_le hres)
  rw [Subgroup.map_sup]
  exact hDodd
end CFSG.Quasithin.Chapter15.Section01
