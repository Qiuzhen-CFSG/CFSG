module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableCentralQuotient
public import Theory.GroupTheory.ReducedNormal.ThreeLayers
public import Theory.GroupTheory.Commutator.SymmetricThreePlaneSplitting

/-!
# The actual solvable action kernels and the whole-center splitting

For the original marked row of 14.3.25, let K be the H-normal closure
of Z(U)^g and C = C_Z(U)(K). The K-kernel on U/Z(U) acts trivially on
three successive layers of the elementary U-image in H/C. Reducedness
therefore makes it centralize that whole image. The surviving commutator
plane then shows that this kernel centralizes Z(U) itself.

Consequently the actual action on Z(U) is S3. Its cubic residual splits
off the order-four commutator plane, giving Z(U) = [VH,K] × C. The literal
K-image after quotienting first by C and then by the centralizer of the
U-image is also S3. No whole-center splitting is assumed in the kernel
comparison, and no quotient surjection is treated as an isomorphism.

These results retain SolvableSeedRow as an explicit earlier marked-action
premise. Constructing that row, the remaining seed contradiction and the
centerlessness assembly stay with qt-d-hs-centerless-source. Final
LocalStructure discharge stays with qt-d-hs-local-structure; no theorem
assuming centerlessness is used to obtain these results.

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

/-- The pullback to H of the centralizer of the literal U-image in H/C_Z(U)(K). -/
@[expose] def solvableCenterQuotientKernel (F : InvariantFlag T V 3) (g : G) : Subgroup F.H :=
  let q := QuotientGroup.mk' (solvableCenterFixed F g)
  (centralizer ((F.U.subgroupOf F.H).map q : Set (F.H ⧸ solvableCenterFixed F g))).comap q

/-- The same K-kernel acts on U-hat and on the literal U-image in H/C_Z(U)(K). -/
theorem source_solvable_center_quotient_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    solvableSeedActor F g ⊓ solvableCenterQuotientKernel F g =
      solvableSeedActor F g ⊓ F.uhatAction.ker := by
  let := chosen.elementary
  let U := F.U.subgroupOf F.H
  let Z := F.ZU.subgroupOf F.H
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  let N := K ⊓ F.uhatAction.ker
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  have hUZ : ⁅U,N⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro n hn x hx
    exact (F.mem_uhatAction_ker_iff n).mp hn.2 x hx
  obtain ⟨hn,he,hker,_,_⟩ := source_solvable_seed_kernel_and_plane d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hZN : ⁅Z,N⁆ ≤ W := by
    have hsame := (source_solvable_center_plane d earlier hq chosen structural alternatives
      F hne hz g hgP hgH row).1
    exact ((commutator_mono le_rfl inf_le_left).trans hsame.le).trans (commutator_le_left W K)
  have hWN : ⁅W,N⁆ = ⊥ := by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro n hn
    exact hker.ge (show (⟨n,hn.1⟩ : K) ∈ (F.uhatAction.comp K.subtype).ker from hn.2)
  have hred := source_solvable_center_quotient_reduced d earlier hq chosen structural alternatives
    F hne g
  let : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  have hNC : N.map q ≤ centralizer (U.map q : Set (F.H ⧸ C)) :=
    hred.centralizes_of_three_layers (N.map q) (Z.map q) (W.map q)
      (by rw [←map_commutator]; exact map_mono hUZ)
      (by rw [←map_commutator]; exact map_mono hZN)
      (by rw [←map_commutator,hWN,Subgroup.map_bot])
  apply le_antisymm
  · intro k hk
    refine ⟨hk.1,(F.mem_uhatAction_ker_iff k).mpr ?_⟩
    intro x hx
    have hxH : x ∈ F.H := F.U_le_H hx
    have hc : q ⁅k,(⟨x,hxH⟩ : F.H)⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (hk.2 _ (mem_map_of_mem q hx)).symm
    exact (QuotientGroup.eq_one_iff _).mp hc |>.1
  · intro k hk
    exact ⟨hk.1,hNC (mem_map_of_mem q hk)⟩

/-- The original hatted kernel also centralizes the whole center Z(U),
not merely VH. This uses its just-proved action on the actual central quotient. -/
theorem source_solvable_center_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    solvableSeedActor F g ⊓ centralizer (F.ZU.subgroupOf F.H : Set F.H) =
      solvableSeedActor F g ⊓ F.uhatAction.ker := by
  let := chosen.elementary
  let K := solvableSeedActor F g
  let Z := F.ZU.subgroupOf F.H
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  obtain ⟨_,_,hd⟩ := source_solvable_center_plane d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hqkernel := source_solvable_center_quotient_kernel d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  obtain ⟨hn,he,hker,_,_⟩ := source_solvable_seed_kernel_and_plane d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hWZ := (source_faithful_test_reduced d earlier hq chosen structural alternatives F).1
  apply le_antisymm
  · intro k hk
    refine ⟨hk.1,?_⟩
    have hc : (⟨k,hk.1⟩ : K) ∈ (centralizer
        ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap K.subtype :=
      (centralizer_le (comap_mono hWZ)) hk.2
    exact hker.le hc
  · intro k hk
    refine ⟨hk.1,?_⟩
    intro z hz
    have hcomm : ⁅z,k⁆ ∈ C := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ⁅z,k⁆ = 1
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (hqkernel.ge hk).2 _ (mem_map_of_mem q ((map_subtype_le (center F.U)) hz))
    have hbot : ⁅z,k⁆ = 1 := hd.le_bot ⟨commutator_mem_commutator hz hk.1,hcomm⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp hbot

/-- The whole center splits over the actual order-four commutator plane.
Every quotient and kernel is inherited from the original marked row. -/
theorem source_solvable_center_splitting (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    F.ZU.subgroupOf F.H = ⁅F.ZU.subgroupOf F.H,solvableSeedActor F g⁆ ⊔
        solvableCenterFixed F g ∧
      Disjoint (⁅F.ZU.subgroupOf F.H,solvableSeedActor F g⁆ : Subgroup F.H)
        (solvableCenterFixed F g) := by
  let := chosen.elementary
  let Z := F.ZU.subgroupOf F.H
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  let : Z.Normal := normal_subgroupOf_of_le_normalizer F.H_normalizes_ZU
  let : IsMulCommutative F.ZU := by
    change IsMulCommutative ((center F.U).map F.U.subtype)
    infer_instance
  let : IsMulCommutative Z := inferInstanceAs (IsMulCommutative (F.ZU.subgroupOf F.H))
  obtain ⟨hn,he,hker,_,_⟩ := source_solvable_seed_kernel_and_plane d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hkZ := source_solvable_center_kernel d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hCeq : (centralizer (Z : Set F.H)).comap K.subtype =
      (centralizer (W : Set F.H)).comap K.subtype := by
    ext k
    constructor
    · intro hk
      exact hker.ge ((hkZ.le ⟨k.property,hk⟩).2)
    · intro hk
      exact (hkZ.ge ⟨k.property,hker.le hk⟩).2
  obtain ⟨⟨em⟩,_⟩ := source_solvable_seed_model d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn
  have hmodel : Nonempty ((K ⧸ (centralizer (Z : Set F.H)).comap K.subtype) ≃*
      Equiv.Perm (Fin 3)) := ⟨(QuotientGroup.quotientMulEquivOfEq hCeq).trans em⟩
  obtain ⟨_,hcard,hdis⟩ := source_solvable_center_plane d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hZtwo : IsPGroup 2 Z :=
    (T.isPGroup'.to_le ((map_subtype_le (center F.U)).trans
      (source_closure_le_sylow d earlier hq chosen structural alternatives F))).comap_subtype
  exact ⟨commutator_plane_splitting_of_symmetricThree Z K hZtwo hcard hdis hmodel,hdis⟩

/-- The literal K-image in H/C_Z(U)(K), followed by the centralizer quotient
of the original U-image, is S3. Both successive quotient maps are retained. -/
theorem source_solvable_center_quotient_symmetricThree (d : Counterexample T L)
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
      Nonempty ((((solvableSeedActor F g).map q).map
        (QuotientGroup.mk' (centralizer (Uq : Set (F.H ⧸ solvableCenterFixed F g))))) ≃*
        Equiv.Perm (Fin 3)) := by
  let q := QuotientGroup.mk' (solvableCenterFixed F g)
  let Uq := (F.U.subgroupOf F.H).map q
  have hred := source_solvable_center_quotient_reduced d earlier hq chosen structural alternatives
    F hne g
  let := hred.normal
  refine ⟨hred.normal,?_⟩
  let K := solvableSeedActor F g
  let π := QuotientGroup.mk' (centralizer (Uq : Set (F.H ⧸ solvableCenterFixed F g)))
  let D := (K.map q).map π
  let f : K →* D := ((π.comp q).comp K.subtype).codRestrict D
    (fun k => mem_map_of_mem π (mem_map_of_mem q k.property))
  have hf : Function.Surjective f := by
    rintro ⟨x,y,⟨k,hk,rfl⟩,rfl⟩
    exact ⟨⟨k,hk⟩,rfl⟩
  have hkq : f.ker = (solvableCenterQuotientKernel F g).comap K.subtype := by
    ext k
    change f k = 1 ↔ q k ∈ centralizer (Uq : Set (F.H ⧸ solvableCenterFixed F g))
    rw [←QuotientGroup.eq_one_iff]
    exact Subtype.ext_iff
  have hkhat := source_solvable_center_quotient_kernel d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  obtain ⟨hn,he,hker,_,_⟩ := source_solvable_seed_kernel_and_plane d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have heq : f.ker = (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap
      K.subtype := by
    rw [hkq,hker]
    ext k
    exact ⟨fun hk => (hkhat.le ⟨k.property,hk⟩).2,
      fun hk => (hkhat.ge ⟨k.property,hk⟩).2⟩
  obtain ⟨⟨em⟩,_⟩ := source_solvable_seed_model d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq heq).trans em)⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
