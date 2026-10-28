module

public import Theory.SpecificGroups.Triality.LeviRankOneMatrices
public import Theory.SpecificGroups.Triality.LeviArmCommutation
public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Root involutions in the genuine binary triality carrier

The central D4 vertex gives the long simple root over GF(q). The orbit of
three arms gives the short simple root over GF(q³), with parameters
(t,F(t),F²(t)). Construct both maps using the proved pinned SL₂ embeddings,
restrict to elementary fixed points, and take the actual central quotient.
The centerlessness of SL₂ in characteristic two proves that both root maps
remain injective. In particular nonzero parameters give actual involutions,
including q = 2. Root classes mean conjugacy to these specified elements.

This supplies concrete markings for Aschbacher–Smith 16.1.4(1), 16.1.6 and
16.5.13–14 (`refs/quasithin.pdf`, pp.1171–1172, 1201–1203). Exhaustion of the
involutions and their centralizer geometry are separate results. The root
construction and orbit-length fields follow GLS3 §§2.4–2.6.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics

variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

/-- The long-root rank-one subgroup in the genuine fixed points. -/
def longRankOneFixed : SL(2, GaloisField 2 n) →* fixedSubgroup P :=
  ((pinnedRankOneMaps P rfl).centralFixedEmbedding).codRestrict _ (fun g =>
    ((pinnedRankOneMaps P rfl).range_centralFixedEmbedding.le ⟨g, rfl⟩).2)

/-- The short-root rank-one subgroup has the full cubic coefficient field. -/
def shortRankOneFixed : SL(2, ExtensionField P) →* fixedSubgroup P :=
  ((pinnedRankOneMaps P rfl).armsFixedEmbedding (armRootCommutation P rfl)).codRestrict _
    (fun g => ((pinnedRankOneMaps P rfl).range_armsFixedEmbedding
      (armRootCommutation P rfl)).le ⟨g, rfl⟩ |>.2)

theorem longRankOneFixed_injective : Function.Injective (longRankOneFixed n hn) := by
  intro a b h
  exact (pinnedRankOneMaps P rfl).centralFixedEmbedding_injective
    (congrArg Subtype.val h)

theorem shortRankOneFixed_injective : Function.Injective (shortRankOneFixed n hn) := by
  intro a b h
  exact (pinnedRankOneMaps P rfl).armsFixedEmbedding_injective (armRootCommutation P rfl)
    (congrArg Subtype.val h)

private theorem map_upper {F E : Type*} [Field F] [Field E] (f : F →+* E) (t : F) :
    SpecialLinearGroup.map f (SpecialLinearGroup.upperUnipotentHom F
      (Multiplicative.ofAdd t)) = SpecialLinearGroup.upperUnipotentHom E
        (Multiplicative.ofAdd (f t)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.upperUnipotentHom, SpecialLinearGroup.map_apply_coe,
      SpecialLinearGroup.transvection_coe]

/-- The pinned long-root formula before the central quotient. -/
theorem longRankOneFixed_upper_val (t : GaloisField 2 n) :
    (longRankOneFixed n hn (SpecialLinearGroup.upperUnipotentHom _
      (Multiplicative.ofAdd t)) : SplitGroup P) =
        positiveRoot P 1 (baseFieldEmbedding P t) := by
  change (pinnedRankOneMaps P rfl).hom 1
    (SpecialLinearGroup.map (baseFieldEmbedding P).toRingHom
      (SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd t))) = _
  exact (congrArg ((pinnedRankOneMaps P rfl).hom 1)
    (map_upper (baseFieldEmbedding P).toRingHom t)).trans
      ((pinnedRankOneMaps P rfl).positive 1 _)

/-- The actual folded short root is the product on the three arms. -/
theorem shortRankOneFixed_upper_val (t : ExtensionField P) :
    (shortRankOneFixed n hn (SpecialLinearGroup.upperUnipotentHom _
      (Multiplicative.ofAdd t)) : SplitGroup P) =
        positiveRoot P 0 t * positiveRoot P 2 (fieldFrobenius P t) *
          positiveRoot P 3 (fieldFrobenius P (fieldFrobenius P t)) := by
  change (pinnedRankOneMaps P rfl).hom 0 _ *
    (pinnedRankOneMaps P rfl).hom 2 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom _) *
    (pinnedRankOneMaps P rfl).hom 3 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom
      (SpecialLinearGroup.map (fieldFrobenius P).toRingHom _)) = _
  simp only [map_upper]
  exact congrArg₂ (· * ·)
    (congrArg₂ (· * ·) ((pinnedRankOneMaps P rfl).positive 0 t)
      ((pinnedRankOneMaps P rfl).positive 2 _))
    ((pinnedRankOneMaps P rfl).positive 3 _)

/-- The long simple root, after elementary restriction and central quotient. -/
def longRootHom : Multiplicative (GaloisField 2 n) →* BinaryCarrier n hn :=
  ((toCarrier P).comp (sl2ElementaryLift P rfl (longRankOneFixed n hn))).comp
    (SpecialLinearGroup.upperUnipotentHom (GaloisField 2 n))

/-- The short simple root, retaining all q³ parameters. -/
def shortRootHom : Multiplicative (ExtensionField P) →* BinaryCarrier n hn :=
  ((toCarrier P).comp (sl2ElementaryLift P rfl (shortRankOneFixed n hn))).comp
    (SpecialLinearGroup.upperUnipotentHom (ExtensionField P))

theorem longRootHom_injective : Function.Injective (longRootHom n hn) :=
  (sl2_toCarrier_injective P rfl _ (longRankOneFixed_injective n hn)).comp
    (SpecialLinearGroup.upperUnipotentHom_injective _)

theorem shortRootHom_injective : Function.Injective (shortRootHom n hn) :=
  (sl2_toCarrier_injective P rfl _ (shortRankOneFixed_injective n hn)).comp
    (SpecialLinearGroup.upperUnipotentHom_injective _)

def longRoot (t : GaloisField 2 n) : BinaryCarrier n hn :=
  longRootHom n hn (Multiplicative.ofAdd t)

def shortRoot (t : ExtensionField P) : BinaryCarrier n hn :=
  shortRootHom n hn (Multiplicative.ofAdd t)

@[simp] theorem longRoot_zero : longRoot n hn 0 = 1 := (longRootHom n hn).map_one
@[simp] theorem shortRoot_zero : shortRoot n hn 0 = 1 := (shortRootHom n hn).map_one

theorem longRoot_add (s t : GaloisField 2 n) :
    longRoot n hn (s + t) = longRoot n hn s * longRoot n hn t :=
  (longRootHom n hn).map_mul _ _

theorem shortRoot_add (s t : ExtensionField P) :
    shortRoot n hn (s + t) = shortRoot n hn s * shortRoot n hn t :=
  (shortRootHom n hn).map_mul _ _

theorem longRoot_injective : Function.Injective (longRoot n hn) :=
  (longRootHom_injective n hn).comp Multiplicative.ofAdd.injective

theorem shortRoot_injective : Function.Injective (shortRoot n hn) :=
  (shortRootHom_injective n hn).comp Multiplicative.ofAdd.injective

@[simp] theorem longRoot_eq_one_iff (t : GaloisField 2 n) :
    longRoot n hn t = 1 ↔ t = 0 := by
  rw [← longRoot_zero n hn]
  exact (longRoot_injective n hn).eq_iff

@[simp] theorem shortRoot_eq_one_iff (t : ExtensionField P) :
    shortRoot n hn t = 1 ↔ t = 0 := by
  rw [← shortRoot_zero n hn]
  exact (shortRoot_injective n hn).eq_iff

theorem longRoot_sq (t : GaloisField 2 n) : longRoot n hn t ^ 2 = 1 := by
  rw [pow_two, ← longRoot_add, CharTwo.add_self_eq_zero, longRoot_zero]

theorem shortRoot_sq (t : ExtensionField P) : shortRoot n hn t ^ 2 = 1 := by
  rw [pow_two, ← shortRoot_add, CharTwo.add_self_eq_zero, shortRoot_zero]

theorem longRoot_orderOf {t : GaloisField 2 n} (ht : t ≠ 0) :
    orderOf (longRoot n hn t) = 2 :=
  orderOf_eq_prime (longRoot_sq n hn t) (by simpa using ht)

theorem shortRoot_orderOf {t : ExtensionField P} (ht : t ≠ 0) :
    orderOf (shortRoot n hn t) = 2 :=
  orderOf_eq_prime (shortRoot_sq n hn t) (by simpa using ht)

/-- The concrete root elements lie in the positive subgroup downstairs. -/
theorem longRoot_mem_unipotent (t : GaloisField 2 n) :
    longRoot n hn t ∈ unipotent P := by
  refine ⟨sl2ElementaryLift P rfl (longRankOneFixed n hn)
    (SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd t)), ?_, rfl⟩
  change (longRankOneFixed n hn _ : SplitGroup P) ∈ positiveSubgroup P
  rw [longRankOneFixed_upper_val]
  exact positiveRoot_mem_positiveSubgroup P 1 _

theorem shortRoot_mem_unipotent (t : ExtensionField P) :
    shortRoot n hn t ∈ unipotent P := by
  refine ⟨sl2ElementaryLift P rfl (shortRankOneFixed n hn)
    (SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd t)), ?_, rfl⟩
  change (shortRankOneFixed n hn _ : SplitGroup P) ∈ positiveSubgroup P
  rw [shortRankOneFixed_upper_val]
  exact (positiveSubgroup P).mul_mem ((positiveSubgroup P).mul_mem
    (positiveRoot_mem_positiveSubgroup P 0 _) (positiveRoot_mem_positiveSubgroup P 2 _))
    (positiveRoot_mem_positiveSubgroup P 3 _)

/-- The two specified root subgroups, as actual embedded subgroups. -/
def longRootSubgroup : Subgroup (BinaryCarrier n hn) := (longRootHom n hn).range

def shortRootSubgroup : Subgroup (BinaryCarrier n hn) := (shortRootHom n hn).range

theorem longRootSubgroup_card : Nat.card (longRootSubgroup n hn) = 2 ^ n := by
  calc
    _ = Nat.card (Multiplicative (GaloisField 2 n)) :=
      Nat.card_congr (MonoidHom.ofInjective (longRootHom_injective n hn)).toEquiv.symm
    _ = 2 ^ n := (Nat.card_congr Multiplicative.toAdd).trans
      (GaloisField.card 2 n (Nat.ne_of_gt hn))

theorem shortRootSubgroup_card : Nat.card (shortRootSubgroup n hn) = 2 ^ (3 * n) := by
  calc
    _ = Nat.card (Multiplicative (ExtensionField P)) :=
      Nat.card_congr (MonoidHom.ofInjective (shortRootHom_injective n hn)).toEquiv.symm
    _ = 2 ^ (3 * n) := (Nat.card_congr Multiplicative.toAdd).trans
      (GaloisField.card 2 (3 * n) (by omega))

/-- Long-root involutions are conjugates of nonidentity values on the actual
central-vertex root curve. -/
def IsLongRootInvolution (r : BinaryCarrier n hn) : Prop :=
  ∃ t : GaloisField 2 n, t ≠ 0 ∧ IsConj (longRoot n hn t) r

/-- Short-root involutions are conjugates of nonidentity values on the actual
folded three-arm root curve. -/
def IsShortRootInvolution (r : BinaryCarrier n hn) : Prop :=
  ∃ t : ExtensionField P, t ≠ 0 ∧ IsConj (shortRoot n hn t) r

theorem IsLongRootInvolution.orderOf_eq_two {r : BinaryCarrier n hn}
    (hr : IsLongRootInvolution n hn r) : orderOf r = 2 := by
  obtain ⟨t, ht, hc⟩ := hr
  obtain ⟨c, hc⟩ := hc
  exact (SemiconjBy.orderOf_eq c.val hc).symm.trans (longRoot_orderOf n hn ht)

theorem IsShortRootInvolution.orderOf_eq_two {r : BinaryCarrier n hn}
    (hr : IsShortRootInvolution n hn r) : orderOf r = 2 := by
  obtain ⟨t, ht, hc⟩ := hr
  obtain ⟨c, hc⟩ := hc
  exact (SemiconjBy.orderOf_eq c.val hc).symm.trans (shortRoot_orderOf n hn ht)

end Triality.Standard.EvenInvolutionGeometry
