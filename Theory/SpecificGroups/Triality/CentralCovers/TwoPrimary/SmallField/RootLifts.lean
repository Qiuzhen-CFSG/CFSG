module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations
public import Theory.SpecificGroups.PSL2.EightCentralCovers
public import Theory.GroupTheory.PerfectCentralCoverTrivialTransport

/-!
# Additive root lifts for the smallest genuine triality group

The actual three-arm Levi is PSL₂(8), whose canonical universal kernel is
proved trivial. Pulling a central extension back to this Levi gives a section
of its literal inclusion. Its first short root and two published folded Weyl
conjugates give additive sections of all three short roots. The last conjugate
retains the required Frobenius rotation of the cubic parameter.

The actual fixed field at q = 2 consists of 0 and 1. Thus an involutory lift
of the highest long-root element gives additive lifts of all three long roots.
`rootSectionsOfHighestLift` combines these with the constructed short lifts.
It makes no assertion about inter-root commutators.

The Weyl calculations extend the private calculations in
`StandardTwoRank.Perfectness`, preserving the same checked D₄ enumeration.
Sources: GLS3 §§2.4 and 6.1, especially Theorem 6.1.4 and Tables 6.1.2–3;
Aschbacher–Smith A.2.4 and I.1.3 (PDF pp.44 and 418).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Triality.Standard
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.PositiveCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators
open PerfectCentralCovering

namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section

private theorem exists_section_of_trivial_kernel {B E : Type*} [Group B] [Group E]
    (f : E →* B) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (H : Subgroup B) [Group.IsPerfect H]
    (hH : (universalProjection H).ker = ⊥) :
    ∃ s : H →* E, f.comp s = H.subtype := by
  let A := H.comap f
  let p : A →* H :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x y) }
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨y, hy⟩ := hf x.val
    exact ⟨⟨y, by change f y ∈ H; rw [hy]; exact x.property⟩, Subtype.ext hy⟩
  have hpc : p.ker ≤ Subgroup.center A := by
    intro x hx
    have hxk : x.val ∈ f.ker := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hk hxk) y.val)
  obtain ⟨l, hl, _⟩ := universalProjection_existsUnique_lift p hp hpc
  let e : UniversalGroup H ≃* H := MulEquiv.ofBijective (universalProjection H)
    ⟨(universalProjection H).ker_eq_bot_iff.mp hH, universalProjection_surjective H⟩
  refine ⟨A.subtype.comp (l.comp e.symm.toMonoidHom), ?_⟩
  ext x
  have hx := DFunLike.congr_fun hl (e.symm x)
  exact congrArg Subtype.val (hx.trans (e.apply_symm_apply x))

private theorem short_zero_mem_arms (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P) :
    short P hp 0 t ∈ levi P .arms := by
  refine ⟨shortElementary P hp 0 t, ?_, rfl⟩
  change elementaryInclusion P _ ∈ splitLevi P .arms
  rw [shortElementary_val]
  have he : shortSplit P 0 t = positiveRoot P 0 t *
      positiveRoot P 2 (fieldFrobenius P t) *
      positiveRoot P 3 (fieldFrobenius P (fieldFrobenius P t)) := by
    change curve P (simplePosition 0) t * curve P (simplePosition 2) _ *
      curve P (simplePosition 3) _ = _
    rw [curve_simple, curve_simple, curve_simple]
  rw [he]
  have hpos (i : Fin 4) (hi : i ≠ 1) (u : ExtensionField P) :
      positiveRoot P i u ∈ splitLevi P .arms :=
    Subgroup.subset_closure ⟨i, hi, u, Or.inl rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (hpos 0 (by decide) _) (hpos 2 (by decide) _)) (hpos 3 (by decide) _)

def shortZeroInArms (P : Parameters) (hp : P.prime = 2) : Multiplicative (ExtensionField P) →* levi P .arms where
  toFun t := ⟨short P hp 0 t.toAdd, by exact short_zero_mem_arms P hp t.toAdd⟩
  map_one' := Subtype.ext (short_zero P hp 0)
  map_mul' s t := Subtype.ext (short_add P hp 0 s.toAdd t.toAdd)

private def numbering : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom.toMonoidHom.comp rootWeylGroup.subtype

private lemma numbering_generator (i : Fin 4) :
    numbering (rootWeylGenerator i) = DiagramFixed.reflection i := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm ((typeDRootPairing 2).reflectionPerm
    (typeDSimpleRootIndex 2 i) (rootEnumeration r)) = reflectionTable i r
  rw [← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

private lemma representative_numbered (w : DihedralGroup 6) (r : Fin 24) :
    (rootRepresentative w).val (rootEnumeration r) =
      rootEnumeration (DiagramFixed.representativeTable w r) := by
  have h : numbering (rootRepresentative w) = DiagramFixed.representative w := by
    cases w <;> simp [rootRepresentative, DiagramFixed.representative, foldedRootReflection,
      map_mul, map_pow, numbering_generator, DiagramFixed.arm]
  have hh := congrFun (congrArg (fun e : Equiv.Perm (Fin 24) => (e : Fin 24 → Fin 24)) h) r
  change rootEnumeration.symm ((rootRepresentative w).val (rootEnumeration r)) = _ at hh
  exact (rootEnumeration.apply_symm_apply _).symm.trans
    (congrArg rootEnumeration (hh.trans (DiagramFixed.representative_apply w r)))

private theorem conjugate_curve (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 12)
    (h : DiagramFixed.representativeTable w (positiveIndex i) = positiveIndex j)
    (t : ExtensionField P) :
    splitRepresentative P hp w * curve P i t * (splitRepresentative P hp w)⁻¹ =
      curve P j t := by
  apply Subtype.ext
  change (splitRepresentative P hp w).val * _ * (splitRepresentative P hp w).val⁻¹ = _
  rw [curve_unit, splitRepresentative_rootCurveUnit_conjugation,
    ← rootEnumeration_positiveIndex, representative_numbered, h, rootEnumeration_positiveIndex]
  rfl

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x*y) * g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem short_one_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    splitRepresentative P hp (.r 2) * shortSplit P 0 t *
      (splitRepresentative P hp (.r 2))⁻¹ = shortSplit P 1 t := by
  simp only [shortSplit, conjugate_mul]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (conjugate_curve P hp (.r 2) 0 4 (by decide) t)
    (conjugate_curve P hp (.r 2) 1 5 (by decide) (fieldFrobenius P t)))
    (conjugate_curve P hp (.r 2) 2 6 (by decide) (fieldFrobenius P (fieldFrobenius P t)))

private theorem short_two_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    splitRepresentative P hp (.r 1) * shortSplit P 0 (fieldFrobenius P t) *
      (splitRepresentative P hp (.r 1))⁻¹ = shortSplit P 2 t := by
  simp only [shortSplit, conjugate_mul]
  calc
    _ = curve P 8 (fieldFrobenius P t) *
        curve P 9 (fieldFrobenius P (fieldFrobenius P t)) *
        curve P 7 (fieldFrobenius P (fieldFrobenius P (fieldFrobenius P t))) :=
      congrArg₂ (· * ·) (congrArg₂ (· * ·)
        (conjugate_curve P hp (.r 1) 0 8 (by decide) (fieldFrobenius P t))
        (conjugate_curve P hp (.r 1) 1 9 (by decide) (fieldFrobenius P (fieldFrobenius P t))))
        (conjugate_curve P hp (.r 1) 2 7 (by decide)
          (fieldFrobenius P (fieldFrobenius P (fieldFrobenius P t))))
    _ = _ := by
      rw [fieldFrobenius_three]
      exact ((shortSplit_curves_commute P 2 0 1 t (fieldFrobenius P t)).mul_right
        (shortSplit_curves_commute P 2 0 2 t (fieldFrobenius P (fieldFrobenius P t)))).eq.symm.trans
          (mul_assoc _ _ _).symm


/-- The literal folded Weyl representative sends the first short root to the second. -/
theorem short_one_conjugate_carrier (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    weylRepresentative P hp (.r 2) * short P hp 0 t *
      (weylRepresentative P hp (.r 2))⁻¹ = short P hp 1 t := by
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul, map_inv, FixedDescent.carrierToSplit_representative,
    short, FixedDescent.carrierToSplit_toCarrier, shortElementary_val]
  exact short_one_conjugate P hp t

/-- The third short marking requires the published Frobenius rotation. -/
theorem short_two_conjugate_carrier (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    weylRepresentative P hp (.r 1) * short P hp 0 (fieldFrobenius P t) *
      (weylRepresentative P hp (.r 1))⁻¹ = short P hp 2 t := by
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul, map_inv, FixedDescent.carrierToSplit_representative,
    short, FixedDescent.carrierToSplit_toCarrier, shortElementary_val]
  exact short_two_conjugate P hp t

def longWeyl : Fin 3 → DihedralGroup 6 := ![.r 1, .r 5, .r 0]

private theorem long_conjugate (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : fixedField P) :
    splitRepresentative P hp (longWeyl i) * longSplit P 2 t *
      (splitRepresentative P hp (longWeyl i))⁻¹ = longSplit P i t := by
  apply conjugate_curve
  fin_cases i <;> decide

/-- The same actual Weyl words transport the highest long root to all three. -/
theorem long_conjugate_carrier (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : fixedField P) :
    weylRepresentative P hp (longWeyl i) * long P hp 2 t *
      (weylRepresentative P hp (longWeyl i))⁻¹ = long P hp i t := by
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [map_mul, map_inv, FixedDescent.carrierToSplit_representative,
    long, FixedDescent.carrierToSplit_toCarrier, longElementary_val]
  exact long_conjugate P hp i t


local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one


theorem exists_arms_section {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ s : levi P .arms →* E, f.comp s = (levi P .arms).subtype := by
  let : Group.IsPerfect (levi P .arms) := levi_arms_isPerfect P (binaryParameters_prime 1 Nat.zero_lt_one)
  apply exists_section_of_trivial_kernel f hf hk
  apply universalProjection_ker_eq_bot_of_mulEquiv (leviArmsEquivPSL2 P (binaryParameters_prime 1 Nat.zero_lt_one))
  exact Theory.SpecificGroups.PSL2Eight.universalProjection_ker_eq_bot

theorem exists_short_zero_lift {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ s : Multiplicative (ExtensionField P) →* E,
      ∀ t, f (s (.ofAdd t)) = short P (binaryParameters_prime 1 Nat.zero_lt_one) 0 t := by
  obtain ⟨s, hs⟩ := exists_arms_section f hf hk
  exact ⟨s.comp (shortZeroInArms P (binaryParameters_prime 1 Nat.zero_lt_one)), fun t => DFunLike.congr_fun hs (shortZeroInArms P (binaryParameters_prime 1 Nat.zero_lt_one) (.ofAdd t))⟩

/-- The unique splitting on the actual cubic-field Levi. -/
def armsSection {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    levi P .arms →* E := (exists_arms_section f hf hk).choose

theorem armsSection_project {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    f.comp (armsSection f hf hk) = (levi P .arms).subtype :=
  (exists_arms_section f hf hk).choose_spec

def shortZeroLift {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    Multiplicative (ExtensionField P) →* E :=
  (armsSection f hf hk).comp (shortZeroInArms P (binaryParameters_prime 1 Nat.zero_lt_one))

theorem shortZeroLift_project {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (t : ExtensionField P) :
    f (shortZeroLift f hf hk (.ofAdd t)) = short P (binaryParameters_prime 1 Nat.zero_lt_one) 0 t :=
  DFunLike.congr_fun (armsSection_project f hf hk) (shortZeroInArms P (binaryParameters_prime 1 Nat.zero_lt_one) (.ofAdd t))

def weylLift {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (w : DihedralGroup 6) : E :=
  (hf (weylRepresentative P (binaryParameters_prime 1 Nat.zero_lt_one) w)).choose

theorem weylLift_project {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (w : DihedralGroup 6) :
    f (weylLift f hf w) = weylRepresentative P (binaryParameters_prime 1 Nat.zero_lt_one) w :=
  (hf (weylRepresentative P (binaryParameters_prime 1 Nat.zero_lt_one) w)).choose_spec

/-- One common system of additive short lifts, with the exact Frobenius marking. -/
def shortRootLift {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    Fin 3 → Multiplicative (ExtensionField P) →* E :=
  ![shortZeroLift f hf hk,
    (MulAut.conj (weylLift f hf (.r 2))).toMonoidHom.comp (shortZeroLift f hf hk),
    (MulAut.conj (weylLift f hf (.r 1))).toMonoidHom.comp
      ((shortZeroLift f hf hk).comp (fieldFrobenius P).toAddMonoidHom.toMultiplicative)]

theorem shortRootLift_project {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (i : Fin 3) (t : ExtensionField P) :
    f (shortRootLift f hf hk i (.ofAdd t)) = short P (binaryParameters_prime 1 Nat.zero_lt_one) i t := by
  fin_cases i
  · exact shortZeroLift_project f hf hk t
  · change f (weylLift f hf (.r 2) * shortZeroLift f hf hk (.ofAdd t) *
      (weylLift f hf (.r 2))⁻¹) = _
    rw [map_mul, map_mul, map_inv, weylLift_project, shortZeroLift_project]
    exact short_one_conjugate_carrier P (binaryParameters_prime 1 Nat.zero_lt_one) t
  · change f (weylLift f hf (.r 1) *
      shortZeroLift f hf hk (.ofAdd (fieldFrobenius P t)) *
      (weylLift f hf (.r 1))⁻¹) = _
    rw [map_mul, map_mul, map_inv, weylLift_project, shortZeroLift_project]
    exact short_two_conjugate_carrier P (binaryParameters_prime 1 Nat.zero_lt_one) t

/-- The long parameters are in the actual fixed field, which here has two values. -/
theorem fixedField_cases (t : fixedField P) : t = 0 ∨ t = 1 := by
  have ht : t.val ^ 2 = t.val := t.property
  rcases eq_zero_or_one_of_sq_eq_self ht with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- An involution gives an additive map out of the actual binary fixed field. -/
def binaryRootLift {E : Type*} [Group E] (z : E) (hz : z ^ 2 = 1) :
    Multiplicative (fixedField P) →* E := by
  classical
  refine { toFun := fun t => if t.toAdd = 0 then 1 else z
           map_one' := by simp
           map_mul' := ?_ }
  intro a b
  have htwo : (1 : fixedField P) + 1 = 0 := by
    apply Subtype.ext
    exact CharTwo.add_self_eq_zero (1 : GaloisField 2 3)
  change (if a.toAdd + b.toAdd = 0 then 1 else z) =
    (if a.toAdd = 0 then 1 else z) * (if b.toAdd = 0 then 1 else z)
  rcases fixedField_cases a.toAdd with ha | ha <;>
    rcases fixedField_cases b.toAdd with hb | hb <;>
    simp [ha, hb, ← pow_two, hz, htwo]

/-- Transport one involutory highest-root lift to all three long roots. -/
def longRootLift {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (z : E) (hz : z ^ 2 = 1) (i : Fin 3) :
    Multiplicative (fixedField P) →* E :=
  (MulAut.conj (weylLift f hf (longWeyl i))).toMonoidHom.comp (binaryRootLift z hz)

theorem longRootLift_project {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (z : E) (hz : z ^ 2 = 1)
    (hp : f z = long P (binaryParameters_prime 1 Nat.zero_lt_one) 2 1) (i : Fin 3) (t : fixedField P) :
    f (longRootLift f hf z hz i (.ofAdd t)) = long P (binaryParameters_prime 1 Nat.zero_lt_one) i t := by
  classical
  rcases fixedField_cases t with rfl | rfl
  · rw [show Multiplicative.ofAdd (0 : fixedField P) = 1 from rfl, map_one,
      map_one]
    exact (long_zero P (binaryParameters_prime 1 Nat.zero_lt_one) i).symm
  · change f (weylLift f hf (longWeyl i) *
      binaryRootLift z hz (.ofAdd (1 : fixedField P)) *
      (weylLift f hf (longWeyl i))⁻¹) = _
    have hval : binaryRootLift z hz (.ofAdd (1 : fixedField P)) = z := by
      simp [binaryRootLift]
    rw [hval, map_mul, map_mul, map_inv, weylLift_project, hp]
    exact long_conjugate_carrier P (binaryParameters_prime 1 Nat.zero_lt_one) i 1

/-- All six additive sections reduce to one involutory lift of the highest long root.
No higher-root commutator relation is asserted by this construction. -/
def rootSectionsOfHighestLift {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (z : E) (hz : z ^ 2 = 1) (hp : f z = long P (binaryParameters_prime 1 Nat.zero_lt_one) 2 1) :
    RootSections 1 Nat.zero_lt_one f where
  shortRoot := shortRootLift f hf hk
  longRoot := longRootLift f hf z hz
  project_short := shortRootLift_project f hf hk
  project_long := longRootLift_project f hf z hz hp


end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
