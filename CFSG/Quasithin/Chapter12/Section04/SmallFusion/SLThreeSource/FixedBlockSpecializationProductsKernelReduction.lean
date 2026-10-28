module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationProductsReduction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.LinearThreeCore
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Reducing the fixed-line kernel action to a small fixed core

Let P = O₂(L), Q = C_T(V), and C = P ∩ C_G(L). The marked short
block and the actual binary linear-three central cover prove that P is
abelian and |P| ≤ 32. Vanishing H¹ on the original four-space then gives
P = VC, with |C| ≤ 4. Applied to C_Q(P), the same correction gives the
literal equality C_Q(P) = V C_T(L).

Thus the outstanding kernel action is precisely the action of Q on C.
If |C| ≤ 2, normality forces that action to be trivial, and the existing
source consumer proves Q = V C_T(L). The final theorem retains the
order-four branch explicitly. Its elimination requires the escape/MS3
argument and is not asserted here. The marked fifth MS alternative and
its commutator identification are inputs from qt-d-1246-l3-ms-specialization;
qt-d-1246-l3-ms-centralizer-products retains the assembly of both products.

Source: Aschbacher--Smith C.1.13(b), pp.124--125, B.4.8(4), pp.91--92,
and the shared block calculation in the proof of 12.4.6, p.814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02 ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
namespace LocalGeometry
variable (d : LocalGeometry D)

private theorem fixed_supplement_in_core_centralizer
    (ext : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (Q : Subgroup G) (hVQ : V ≤ Q) (hc : ⁅L,Q⁆ ≤ V)
    (hkernel : L.pCoreIn 2 ≤ centralizer (Q : Set G)) :
    Q = V ⊔ (Q ⊓ centralizer (L : Set G)) := by
  let _ := D.elementary
  let := extension_H1_subsingleton D ext hne
  let π : L →* BinaryLinearThree.Group :=
    ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := ext.quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)
  let coords : V →* Multiplicative (Additive V) := {
    toFun := fun v => Multiplicative.ofAdd (Additive.ofMul v)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let c : BinaryConjugationSection L V ⊥ (ext.action.comp π) := {
    section_le := D.le_component
    kernel_le := bot_le
    normalized := D.normalizes
    coordinates := coords
    onto := fun v => ⟨v.toAdd.toMul,rfl⟩
    kernel_eq := by
      ext v
      change v = 1 ↔ (v : G) = 1
      exact Subtype.ext_iff
    equivariant := by
      intro l v
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (ext.conjugation l (Additive.ofMul v)).symm }
  have hk : ∀ l ∈ π.ker, ∀ x ∈ Q, ⁅(l : G),x⁆ ∈ (⊥ : Subgroup G) := by
    intro l hl x hx
    have hlcore : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
      (ext.quotientEquiv.injective ((show ext.quotientEquiv
        (QuotientGroup.mk' (pCore 2 L) l) = 1 from hl).trans ext.quotientEquiv.map_one.symm))
    exact mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
      ((hkernel (mem_map_of_mem L.subtype hlcore)) x hx).symm)
  have he := c.sup_fixedPreimage_eq π hπ Q
    hVQ le_normalizer_of_normal hc hk
  have hf : commutatorPreimage Q L ⊥ = Q ⊓ centralizer (L : Set G) := by
    ext x
    rw [mem_commutatorPreimage_iff Q L ⊥ le_normalizer_of_normal]
    simp only [mem_inf, mem_bot, commutatorElement_eq_one_iff_mul_comm,
      mem_centralizer_iff]
    exact and_congr_right (fun _ => forall_congr' fun l => forall_congr' fun _ => eq_comm)
  rw [hf,sup_comm] at he
  exact he

/-- The canonical kernel is abelian before considering the action of the larger core. -/
theorem ms_core_commutative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    IsMulCommutative (L.pCoreIn 2) := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let := (d.ms_isShort h ext e hcase hQ).linearThree_core_commutative e
  exact map_isMulCommutative (pCore 2 L) L.subtype

/-- The part of the original ambient core that fixes O₂(L) is exactly the desired product. -/
theorem ms_kernelCentralizer_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥) (hQ : msQ L d.R = V) :
    ((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊓
      centralizer (L.pCoreIn 2 : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let X := Q ⊓ centralizer (L.pCoreIn 2 : Set G)
  let _ := D.elementary
  have hPQ : L.pCoreIn 2 ≤ Q := by
    change L.pCoreIn 2 ≤ (T : Subgroup G) ⊓ centralizer (V : Set G)
    rw [←d.ms_core_eq ext h hTV]
    exact pCoreAmbient_mono_of_isSubnormalIn L (L ⊔ d.R) 2 le_sup_left
      d.ms_relative_normal.isSubnormal
  have hVX : V ≤ X := le_inf (le_inf D.le_sylow V.le_centralizer)
    (le_centralizer_iff.mpr (hPQ.trans inf_le_right))
  have hc : ⁅L,X⁆ ≤ V := by
    have hh : ⁅(L ⊔ d.R).pCoreIn 2,L⁆ = V := hQ
    rw [d.ms_core_eq ext h hTV,commutator_comm] at hh
    exact (commutator_mono le_rfl inf_le_left).trans hh.le
  have hs := fixed_supplement_in_core_centralizer ext hne X hVX hc
    (le_centralizer_iff.mp (show X ≤ centralizer (L.pCoreIn 2 : Set G) from inf_le_right))
  have hf : X ⊓ centralizer (L : Set G) =
      (T : Subgroup G) ⊓ centralizer (L : Set G) := by
    apply le_antisymm (inf_le_inf_right _ (inf_le_left.trans inf_le_left))
    exact le_inf (le_inf
      (le_inf inf_le_left (inf_le_right.trans (centralizer_le D.le_component)))
      (inf_le_right.trans (centralizer_le (pCoreIn_le 2 L)))) inf_le_right
  rw [hf] at hs
  exact hs

/-- The original O₂(L) splits over V without a kernel-fixation premise. -/
theorem ms_componentCore_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    L.pCoreIn 2 = V ⊔ (L.pCoreIn 2 ⊓ centralizer (L : Set G)) := by
  let := d.ms_core_commutative h ext e hcase hQ
  apply fixed_supplement_in_core_centralizer ext hne (L.pCoreIn 2)
    D.le_componentCore ?_ (L.pCoreIn 2).le_centralizer
  have hh := d.ms_blockU_eq hQ
  rw [blockU,map_commutator, ←MonoidHom.range_eq_map,range_subtype] at hh
  exact (commutator_comm L (L.pCoreIn 2)).le.trans hh.le

/-- The original two-core has at most one binary layer above the four-space. -/
theorem ms_core_card_le_thirtyTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hQ : msQ L d.R = V) : Nat.card (L.pCoreIn 2) ≤ 32 := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hu : Nat.card (blockU L) = 16 := by
    rw [←card_map_of_injective (f := L.subtype) L.subtype_injective,
      d.ms_blockU_eq hQ]
    exact module_card_sixteen ext hne
  have hc := linearThree_core_card_le_twice_blockU e
  rw [hu] at hc
  simpa only [pCoreIn, card_map_of_injective L.subtype_injective] using hc

/-- Only a fixed subgroup of order at most four remains above the module. -/
theorem ms_fixedCore_card_le_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    Nat.card (L.pCoreIn 2 ⊓ centralizer (L : Set G) : Subgroup G) ≤ 4 := by
  let C := L.pCoreIn 2 ⊓ centralizer (L : Set G)
  have hn : C ≤ normalizer (V : Set G) :=
    (inf_le_right.trans (centralizer_le D.le_component)).trans (Subgroup.centralizer_le_normalizer _)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes V C hn
  have hi : V ⊓ C = fixedSubgroup L V := by
    change V ⊓ (L.pCoreIn 2 ⊓ centralizer (L : Set G)) = _
    rw [←inf_assoc, inf_eq_left.mpr D.le_componentCore]
  have hf : Nat.card (fixedSubgroup L V) = 2 := by
    obtain ⟨c⟩ := hcase.2.1
    change Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) = 2
    rw [←hQ]
    exact (Nat.card_congr c.toEquiv).trans (Nat.card_zmod 2)
  rw [hi, hf, ← d.ms_componentCore_product h ext hne e hcase hQ,
    module_card_sixteen ext hne] at hprod
  have hc := d.ms_core_card_le_thirtyTwo h ext hne e hQ
  change Nat.card C ≤ 4
  omega

/-- The outstanding kernel action is exactly the action on the small fixed core. -/
theorem ms_core_centralization_iff_fixedCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    L.pCoreIn 2 ≤ centralizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ↔
    L.pCoreIn 2 ⊓ centralizer (L : Set G) ≤ centralizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  constructor
  · exact fun hc => inf_le_left.trans hc
  · intro hc
    rw [d.ms_componentCore_product h ext hne e hcase hQ]
    exact sup_le (le_centralizer_iff.mpr inf_le_right) hc

/-- A fixed core of order at most two has no remaining kernel action. -/
theorem ms_core_centralization_of_fixedCore_le_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V)
    (hsmall : Nat.card (L.pCoreIn 2 ⊓ centralizer (L : Set G) : Subgroup G) ≤ 2) :
    L.pCoreIn 2 ≤ centralizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  let C := L.pCoreIn 2 ⊓ centralizer (L : Set G)
  have hFC : fixedSubgroup L V ≤ C := inf_le_inf_right _ D.le_componentCore
  have hlo := card_le_of_le hFC
  rw [ext.fixed_card_eq_two hne] at hlo
  change Nat.card C ≤ 2 at hsmall
  change 2 ≤ Nat.card C at hlo
  have hC : Nat.card C = 2 := by omega
  have hn : normalizer (L : Set G) ≤ normalizer (C : Set G) :=
    (le_inf (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
      (normalizer_le_normalizer_centralizer L)).trans inf_normalizer_le_normalizer_inf
  apply (d.ms_core_centralization_iff_fixedCore h ext hne e hcase hQ).mpr
  apply le_centralizer_iff.mp
  exact (inf_le_left.trans D.sylow_normalizes_component).trans
    (hn.trans (normalizer_le_centralizer_of_card_two C hC))

/-- The literal first source product is proved in the small fixed-core branch. -/
theorem ms_core_product_of_fixedCore_le_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V)
    (hsmall : Nat.card (L.pCoreIn 2 ⊓ centralizer (L : Set G) : Subgroup G) ≤ 2) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) :=
  d.ms_core_product_of_core_centralization h ext hTV hne hQ
    (d.ms_core_centralization_of_fixedCore_le_two h ext hne e hcase hQ hsmall)

/-- Every branch except the order-four fixed core gives the literal source product. -/
theorem ms_core_product_or_fixedCore_card_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    ((T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))) ∨
    Nat.card (L.pCoreIn 2 ⊓ centralizer (L : Set G) : Subgroup G) = 4 := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  let C := L.pCoreIn 2 ⊓ centralizer (L : Set G)
  have hc : Nat.card C ≤ 4 := d.ms_fixedCore_card_le_four h ext hne e hcase hQ
  by_cases hs : Nat.card C ≤ 2
  · exact Or.inl (d.ms_core_product_of_fixedCore_le_two h ext
      ((structural G T L h).2.2 V D).1 hne e hcase hQ hs)
  · right
    have hp : IsPGroup 2 C := (isPGroup_pCoreIn 2 L).to_le inf_le_left
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    change Nat.card C = 2^n at hn
    have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (show 2^n ≤ 2^2 from hn ▸ hc)
    have hn1 : 1 < n := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      (show 2^1 < 2^n from hn ▸ Nat.lt_of_not_ge hs)
    have he : n = 2 := by omega
    change Nat.card C = 4
    calc
      Nat.card C = 2^n := hn
      _ = 4 := by rw [he]; norm_num

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
