module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableCentralSplitting
public import Theory.GroupAction.FullFourPlaneCentralizer

/-!
# Equality of the full action kernels in the solvable seed branch

The full kernel C_H(U-hat) commutes with K modulo C_K(Z(U)). Its action
on the order-four commutator plane therefore centralizes the full S3
plane action, so it is trivial. The whole-center splitting makes this
kernel fix the image of Z(U) in H/C_Z(U)(K). Reducedness of the U-image
then kills its action on that image as well.

This proves C_H(U-hat) = C_H(U-check), with the latter centralizer pulled
back along the literal quotient by C_Z(U)(K). The induced isomorphism
between H-dot and the second centralizer quotient is constructed with
its exact evaluation on every element of the original H.

SolvableSeedRow remains the original explicit marked-action premise.
Its construction and the seed and centerlessness contradictions remain
with qt-d-hs-centerless-source; final LocalStructure discharge remains
with qt-d-hs-local-structure. These results use no later theorem whose
hypotheses already include centerlessness.

Source: Aschbacher--Smith, 14.3.25, printed p.1001, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full H-kernel on U-hat centralizes the original order-four plane. -/
theorem source_solvable_hatted_kernel_plane (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    F.uhatAction.ker ≤ centralizer
      ((⁅F.ZU.subgroupOf F.H,solvableSeedActor F g⁆ : Subgroup F.H) : Set F.H) := by
  let := chosen.elementary
  let Z := F.ZU.subgroupOf F.H
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  let D := ⁅Z,K⁆
  let C := solvableCenterFixed F g
  let N := F.uhatAction.ker
  let : Z.Normal := normal_subgroupOf_of_le_normalizer F.H_normalizes_ZU
  obtain ⟨hn,he,hker,_,_⟩ := source_solvable_seed_kernel_and_plane d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  obtain ⟨hsame,hcard,hd⟩ := source_solvable_center_plane d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hDW : D ≤ W := hsame.le.trans (commutator_le_left W K)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le hDW
  have hs := (source_solvable_center_splitting d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row).1
  have hkZ := source_solvable_center_kernel d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hCeq : (centralizer (D : Set F.H)).comap K.subtype =
      (centralizer (W : Set F.H)).comap K.subtype := by
    ext k
    constructor
    · intro hk
      have hCZ : (k:F.H) ∈ centralizer (Z : Set F.H) := by
        intro z hz
        obtain ⟨x,hx,y,hy,rfl⟩ := mem_sup_of_normal_left.mp (hs.le hz)
        have hc : y * (k:F.H) = (k:F.H) * y := (hy.2 k k.property).symm
        have hcx : x * (k:F.H) = (k:F.H) * x := hk x hx
        rw [mul_assoc,hc,←mul_assoc,hcx,mul_assoc]
      exact hker.ge ((hkZ.le ⟨k.property,hCZ⟩).2)
    · intro hk
      exact centralizer_le hDW hk
  obtain ⟨⟨em⟩,_⟩ := source_solvable_seed_model d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn
  have hmodel : Nonempty ((K ⧸ (centralizer (D : Set F.H)).comap K.subtype) ≃*
      Equiv.Perm (Fin 3)) := ⟨(QuotientGroup.quotientMulEquivOfEq hCeq).trans em⟩
  apply centralizes_four_plane_of_commuting_symmetricThree D K N hcard hmodel
  intro x hx
  have hxN : x ∈ K ⊓ N := by
    have hh := commutator_le_inf N K hx
    exact ⟨hh.2,hh.1⟩
  exact centralizer_le (commutator_le_left Z K) (hkZ.ge hxN).2

/-- The full original H-kernels agree, after killing precisely C_Z(U)(K). -/
theorem source_solvable_full_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    solvableCenterQuotientKernel F g = F.uhatAction.ker := by
  let := chosen.elementary
  let U := F.U.subgroupOf F.H
  let Z := F.ZU.subgroupOf F.H
  let K := solvableSeedActor F g
  let D := ⁅Z,K⁆
  let C := solvableCenterFixed F g
  let N := F.uhatAction.ker
  let q := QuotientGroup.mk' C
  let : Z.Normal := normal_subgroupOf_of_le_normalizer F.H_normalizes_ZU
  have hUZ : ⁅U,N⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro n hn x hx
    exact (F.mem_uhatAction_ker_iff n).mp hn x hx
  have hND := source_solvable_hatted_kernel_plane d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hZN : ⁅Z,N⁆ ≤ C := by
    have hs : Z = D ⊔ C := (source_solvable_center_splitting d earlier hq chosen
      structural alternatives F hne hz g hgP hgH row).1
    rw [hs]
    apply commutator_sup_le_of_relative_normal ⊤ D C N C le_normalizer_of_normal le_top le_top
    · rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr hND]
      exact bot_le
    · exact commutator_le_left C N
  have hred := source_solvable_center_quotient_reduced d earlier hq chosen structural alternatives
    F hne g
  let : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  have hNC : N.map q ≤ centralizer (U.map q : Set (F.H ⧸ C)) :=
    hred.centralizes_of_three_layers (N.map q) (Z.map q) ⊥
      (by rw [←map_commutator]; exact map_mono hUZ)
      (by
        rw [←map_commutator]
        apply (map_mono hZN).trans
        exact ((Subgroup.map_eq_bot_iff (H := C)).mpr (by rw [QuotientGroup.ker_mk'])).le)
      (by rw [Subgroup.commutator_bot_left])
  apply le_antisymm
  · intro k hk
    apply (F.mem_uhatAction_ker_iff k).mpr
    intro x hx
    have hxH : x ∈ F.H := F.U_le_H hx
    have hc : q ⁅k,(⟨x,hxH⟩ : F.H)⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (hk _ (mem_map_of_mem q hx)).symm
    exact (QuotientGroup.eq_one_iff _).mp hc |>.1
  · intro k hk
    exact hNC (mem_map_of_mem q hk)

/-- The full dotted group is the literal centralizer quotient of the U-image
in H/C_Z(U)(K); the isomorphism agrees with both original quotient maps. -/
theorem source_solvable_full_quotient_equiv (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    let q := QuotientGroup.mk' (solvableCenterFixed F g)
    let Uq := (F.U.subgroupOf F.H).map q
    ∃ hn : Uq.Normal, letI := hn
      ∃ e : Hdot F F.uhatAction ≃* ((F.H ⧸ solvableCenterFixed F g) ⧸
          centralizer (Uq : Set (F.H ⧸ solvableCenterFixed F g))),
        ∀ h : F.H, e (QuotientGroup.mk' F.uhatAction.ker h) =
          QuotientGroup.mk' (centralizer (Uq : Set (F.H ⧸ solvableCenterFixed F g))) (q h) := by
  let q := QuotientGroup.mk' (solvableCenterFixed F g)
  let Uq := (F.U.subgroupOf F.H).map q
  have hr := source_solvable_center_quotient_reduced d earlier hq chosen structural alternatives
    F hne g
  let := hr.normal
  refine ⟨hr.normal,?_⟩
  let π := QuotientGroup.mk' (centralizer (Uq : Set (F.H ⧸ solvableCenterFixed F g)))
  let f := π.comp q
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = F.uhatAction.ker := by
    have hh : f.ker = solvableCenterQuotientKernel F g := by
      ext h
      exact QuotientGroup.eq_one_iff (q h)
    exact hh.trans (source_solvable_full_kernel d earlier hq chosen structural alternatives
      F hne hz g hgP hgH row)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf),fun h => rfl⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
