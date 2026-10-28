module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Quotient.Cocycles
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cohomology

/-!
# Descent of the corrected core cocycles and the linear-three branch

The three-subgroups lemma puts [Q,O₂(L)] in C_V(L). Thus the displacement
cocycle vanishes on the kernel of the original quotient marking. In the
nonbinary SL₃ row, vanishing natural H¹ makes every such cocycle principal,
so the original Q equals VC_T(L). This excludes the strict-quotient branch
without inferring quotient nontriviality from V<Q.

Source: Aschbacher–Smith C.1.13(b), I.1.6, and 11.1.5, printed pp.124–125,
408,765–766; the denominator is corrected as in CoreSplit.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

include D in
/-- The three-subgroups calculation required to descend the actual displacement cocycle. -/
theorem core_intrinsicCore_commutator_central (hb : ChapterC.IsShort L) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, L.pCoreIn 2⁆ ≤ centralizer (L : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let P := L.pCoreIn 2
  have hPQ : P ≤ Q := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hPL : ⁅P,L⁆ = V := by
    rw [PointBlocks.seed_eq_blockU D hb, ChapterC.blockU, map_commutator,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hLQ : ⁅L,Q⁆ = V := (commutator_comm L Q).trans (core_commutator_eq_seed D hb)
  have h1 : ⁅⁅P,L⁆,Q⁆ = ⊥ := by
    rw [hPL]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp D.core_centralizes)
  have h2 : ⁅⁅L,Q⁆,P⁆ = ⊥ := by
    rw [hLQ]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hPQ.trans D.core_centralizes))
  exact commutator_eq_bot_iff_le_centralizer.mp (commutator_commutator_eq_bot_of_rotate h1 h2)

/-- The commutator cocycle vanishes on O₂(L), under the literal quotient marking. -/
theorem coreCocycle_kernel_zero {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) (q : (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (l : L) (hl : l ∈ c.quotientMap.ker) : (coreCocycle D c hb q).val l = 0 := by
  have hlP : l ∈ pCore 2 L := by
    change c.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 at hl
    exact (QuotientGroup.eq_one_iff l).mp
      (c.groupEquiv.injective (hl.trans c.groupEquiv.map_one.symm))
  apply congrArg Multiplicative.toAdd
  apply (c.projection_eq_one_iff ⟨⁅(l : G),(q : G)⁆,
    by exact (core_commutator_eq_seed D hb).le (by rw [commutator_comm]; exact commutator_mem_commutator l.property q.property)⟩).mpr
  apply core_intrinsicCore_commutator_central D hb
  rw [commutator_comm]
  exact commutator_mem_commutator (mem_map_of_mem L.subtype hlP) q.property

/-- The displacement cocycle has equal values at lifts of the same model actor. -/
theorem coreCocycle_fiber {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) (q : (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (a b : L) (hab : c.quotientMap a = c.quotientMap b) :
    (coreCocycle D c hb q).val a = (coreCocycle D c hb q).val b := by
  have hk : a⁻¹*b ∈ c.quotientMap.ker := by
    change c.quotientMap (a⁻¹*b) = 1
    rw [map_mul,map_inv,hab,inv_mul_cancel]
  have he := (coreCocycle D c hb q).property a (a⁻¹*b)
  rw [mul_inv_cancel_left,coreCocycle_kernel_zero D c hb q _ hk,map_zero,zero_add] at he
  exact he.symm

/-- Descend to the actual quotient marking, using the proved kernel vanishing. -/
def coreModelCocycle {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    cocycles (restrictScalars (k := ZMod 2) c.modelAction) := by
  let s : c.ModelGroup → L := Function.surjInv c.quotientMap_surjective
  have hs : ∀ b, c.quotientMap (s b) = b :=
    Function.rightInverse_surjInv c.quotientMap_surjective
  refine ⟨fun b => (coreCocycle D c hb q).val (s b), ?_⟩
  intro a b
  change (coreCocycle D c hb q).val (s (a*b)) =
    c.modelAction a ((coreCocycle D c hb q).val (s b)) +
      (coreCocycle D c hb q).val (s a)
  rw [coreCocycle_fiber D c hb q (s (a*b)) (s a*s b)
    (by rw [hs,map_mul,hs,hs])]
  have hh := (coreCocycle D c hb q).property (s a) (s b)
  change (coreCocycle D c hb q).val (s a*s b) =
    c.modelAction (c.quotientMap (s a)) ((coreCocycle D c hb q).val (s b)) +
      (coreCocycle D c hb q).val (s a) at hh
  rwa [hs] at hh


/-- Descent retains the original commutator at every actual component lift. -/
theorem coreModelCocycle_apply {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) (l : L) :
    (coreModelCocycle D c hb q).val (c.quotientMap l) = (coreCocycle D c hb q).val l :=
  coreCocycle_fiber D c hb q _ l
    (Function.rightInverse_surjInv c.quotientMap_surjective (c.quotientMap l))

/-- The descended displacement is multiplicative on the original Q. -/
def coreModelCocycleHom {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 →*
      Multiplicative (cocycles (restrictScalars (k := ZMod 2) c.modelAction)) where
  toFun q := Multiplicative.ofAdd (coreModelCocycle D c hb q)
  map_one' := by
    apply Subtype.ext
    funext a
    obtain ⟨l,rfl⟩ := c.quotientMap_surjective a
    change (coreModelCocycle D c hb 1).val (c.quotientMap l) = 0
    rw [coreModelCocycle_apply]
    exact congrArg (fun z : Multiplicative (cocycles
      ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap)) => z.toAdd.val l)
      (coreCocycleHom D c hb).map_one
  map_mul' q r := by
    apply Subtype.ext
    funext a
    obtain ⟨l,rfl⟩ := c.quotientMap_surjective a
    change (coreModelCocycle D c hb (q*r)).val (c.quotientMap l) =
      (coreModelCocycle D c hb q).val (c.quotientMap l) +
        (coreModelCocycle D c hb r).val (c.quotientMap l)
    rw [coreModelCocycle_apply,coreModelCocycle_apply,coreModelCocycle_apply]
    exact congrArg (fun z : Multiplicative (cocycles
      ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap)) => z.toAdd.val l)
      ((coreCocycleHom D c hb).map_mul q r)

/-- Descent preserves the literal kernel C_T(L), with no model-injectivity premise. -/
theorem coreModelCocycleHom_ker {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) : (coreModelCocycleHom D c hb).ker =
      (((T : Subgroup G) ⊓ centralizer (L : Set G)).subgroupOf
        ((L ⊔ (T : Subgroup G)).pCoreIn 2)) := by
  rw [← coreCocycleHom_ker D c hb]
  ext q
  constructor
  · intro h
    apply Subtype.ext
    funext l
    have he := congrArg (fun z : Multiplicative (cocycles
      (restrictScalars (k := ZMod 2) c.modelAction)) => z.toAdd.val (c.quotientMap l)) h
    change (coreCocycle D c hb q).val l = 0
    change (coreModelCocycle D c hb q).val (c.quotientMap l) = 0 at he
    exact (coreModelCocycle_apply D c hb q l).symm.trans he
  · intro h
    apply Subtype.ext
    funext a
    obtain ⟨l,rfl⟩ := c.quotientMap_surjective a
    change (coreModelCocycle D c hb q).val (c.quotientMap l) = 0
    rw [coreModelCocycle_apply]
    exact congrArg (fun z : Multiplicative (cocycles
      ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap)) => z.toAdd.val l) h

/-- The constructed embedding into cocycles of the actual marked natural model. -/
def coreModelQuotientCocycle {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) :
    letI := componentCentralizer_normal_core D
    (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
      (((T : Subgroup G) ⊓ centralizer (L : Set G)).subgroupOf
        ((L ⊔ (T : Subgroup G)).pCoreIn 2))) →*
      Multiplicative (cocycles (restrictScalars (k := ZMod 2) c.modelAction)) := by
  let := componentCentralizer_normal_core D
  exact QuotientGroup.lift _ (coreModelCocycleHom D c hb) (coreModelCocycleHom_ker D c hb).ge

theorem coreModelQuotientCocycle_injective {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) : Function.Injective (coreModelQuotientCocycle D c hb) := by
  let := componentCentralizer_normal_core D
  exact (QuotientGroup.injective_lift_iff _ _ (coreModelCocycleHom_ker D c hb).ge).mpr (coreModelCocycleHom_ker D c hb).symm

/-- The original Q-action becomes the universal action of its actual model quotient. -/
theorem coreModelCocycle_equivariant {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) (l : L) (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    coreModelCocycle D c hb (componentConjugateCore l q) =
      universalAction (restrictScalars (k := ZMod 2) c.modelAction) (c.quotientMap l)
        (coreModelCocycle D c hb q) := by
  apply Subtype.ext
  funext a
  obtain ⟨r,rfl⟩ := c.quotientMap_surjective a
  have he := congrArg (fun z => z.val r) (coreCocycle_equivariant D c hb l q)
  change (coreCocycle D c hb (componentConjugateCore l q)).val r =
    (coreCocycle D c hb q).val r +
      (c.modelAction (c.quotientMap r) ((coreCocycle D c hb q).val l) -
        (coreCocycle D c hb q).val l) at he
  change (coreModelCocycle D c hb (componentConjugateCore l q)).val (c.quotientMap r) =
    (coreModelCocycle D c hb q).val (c.quotientMap r) +
      (c.modelAction (c.quotientMap r) ((coreModelCocycle D c hb q).val (c.quotientMap l)) -
        (coreModelCocycle D c hb q).val (c.quotientMap l))
  simpa only [coreModelCocycle_apply] using he

/-- Under descent the principal layer remains exactly the corrected denominator. -/
theorem coreModelCocycle_principal_iff {F : BinaryField} (c : Coordinates D F)
    (hb : ChapterC.IsShort L) (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    coreModelCocycle D c hb q ∈ (principal (restrictScalars (k := ZMod 2) c.modelAction)).range ↔
      (q : G) ∈ cohomologyDenominator T L V := by
  rw [← coreCocycle_principal_iff D c hb q]
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨w,Subtype.ext (funext (fun l => ?_))⟩
    have he := congrArg (fun z => z.val (c.quotientMap l)) hw
    exact he.trans (coreModelCocycle_apply D c hb q l)
  · rintro ⟨w,hw⟩
    refine ⟨w,Subtype.ext (funext (fun a => ?_))⟩
    obtain ⟨l,rfl⟩ := c.quotientMap_surjective a
    have he := congrArg (fun z => z.val l) hw
    exact he.trans (coreModelCocycle_apply D c hb q l).symm


/-- Vanishing natural H¹ closes the corrected SL₃ quotient branch on the original Q. -/
theorem sl3_core_eq_denominator (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hb : ChapterC.IsShort L) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = cohomologyDenominator T L V := by
  let c := Coordinates.sl3 m
  have hzero : Module.finrank (ZMod 2) (H1 (linearNatural S.field 3)) = 0 :=
    SLHigherNatural.finrank_restrict_sl3_of_card_pow S.field.degree S.field.card_eq |>.trans
      (if_neg (by have := S.nonbinary; omega))
  let : Subsingleton (H1 (linearNatural S.field 3)) := Module.finrank_zero_iff.mp hzero
  apply le_antisymm ?_ (cohomologyDenominator_le_core D S)
  intro q hq
  let q' : (L ⊔ (T : Subgroup G)).pCoreIn 2 := ⟨q,hq⟩
  obtain ⟨w,hw⟩ := principal_of_surjective (linearNatural S.field 3)
    c.quotientMap c.quotientMap_surjective (coreCocycle D c hb q')
      (coreCocycle_kernel_zero D c hb q')
  apply (coreCocycle_principal_iff D c hb q').mp
  exact ⟨w, Subtype.ext (funext (fun l => (hw l).symm))⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
