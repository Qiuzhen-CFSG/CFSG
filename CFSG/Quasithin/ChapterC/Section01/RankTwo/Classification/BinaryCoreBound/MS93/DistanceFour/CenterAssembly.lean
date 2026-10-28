module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Radical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# The center of the binary distance-four core

The exact double-dual quotient supplies the actual natural central kernel.
Squares descend through this kernel to one map on the full quotient. Its
restrictions to both pure dual factors vanish, so lifts in either factor
commute. The literal commutator pairing is additive, symmetric and equivariant
under the same source marking. Noncommutativity makes its cross pairing
nonzero; the established separation calculation makes its radical zero.
Thus the center of the actual commutator core is precisely U_alpha.

The final conditional application uses the existing quotient-branch
constructor. Its independent geometric producers retain their source
obligations; no center, radius-generation, or further module hypothesis is
added here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), binary center passage in (4.6.11)--(4.6.12), printed pp.909--912.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.DoubleDualQuotient
open Linear
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  {common : CommonFacts R source geometry}
  (d : DoubleDualQuotient source common)

omit [Finite M] in
private noncomputable def coordinates : d.quotient.ker ≃* Multiplicative W :=
  (MulEquiv.subgroupCongr d.kernel).trans
    ((subgroupOfEquivOfLe (U_le_core source geometry common)).trans common.natural.equiv)

omit [Finite M] in
private theorem coordinates_action (m : M) (x y : d.quotient.ker)
    (hy : (y : core R (alpha R)) = coreAction (R := R) m x) :
    (d.coordinates y).toAdd =
      (common.natural.marking (source.projection m)).val.mulVec (d.coordinates x).toAdd := by
  apply common.natural.action
  exact congrArg Subtype.val hy

private theorem kernel_central : d.quotient.ker ≤ center (core R (alpha R)) := by
  intro x hx
  have hxU : (x : FreeAmalgam R) ∈ U R (alpha R) := by
    change x ∈ (U R (alpha R)).subgroupOf (core R (alpha R))
    rwa [← d.kernel]
  obtain ⟨y, hy, he⟩ := U_le_center_core source geometry common hxU
  have hxy : y = x := Subtype.ext he
  exact hxy ▸ hy

omit [Finite M] in
private theorem kernel_square (x : d.quotient.ker) : x ^ 2 = 1 := by
  apply d.coordinates.injective
  rw [map_pow, map_one, pow_two]
  change Multiplicative.ofAdd ((d.coordinates x).toAdd + (d.coordinates x).toAdd) =
    Multiplicative.ofAdd 0
  congr 1
  ext i
  exact CharTwo.add_self_eq_zero _

omit [Finite M] in
private theorem coordinates_zero_iff (x : d.quotient.ker) :
    (d.coordinates x).toAdd = 0 ↔ (x : core R (alpha R)) = 1 := by
  constructor
  · intro h
    have he : d.coordinates x = 1 := congrArg Multiplicative.ofAdd h
    exact congrArg Subtype.val (d.coordinates.injective (he.trans d.coordinates.map_one.symm))
  · intro h
    have hx : x = 1 := Subtype.ext h
    rw [hx, map_one]
    rfl

omit [Finite M] in
private theorem square_mem (x : core R (alpha R)) : x ^ 2 ∈ d.quotient.ker := by
  rw [MonoidHom.mem_ker, map_pow, pow_two]
  change Multiplicative.ofAdd ((d.quotient x).toAdd + (d.quotient x).toAdd) =
    Multiplicative.ofAdd 0
  congr 1
  apply Prod.ext <;> ext i <;> exact CharTwo.add_self_eq_zero _

private theorem square_eq_of_image_eq {x y : core R (alpha R)}
    (h : d.quotient x = d.quotient y) : x ^ 2 = y ^ 2 := by
  let c := x * y⁻¹
  have hc : c ∈ d.quotient.ker := by
    change d.quotient (x * y⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hc2 : c ^ 2 = 1 := congrArg Subtype.val (d.kernel_square ⟨c, hc⟩)
  have hcomm : Commute c y := (mem_center_iff.mp (d.kernel_central hc) y).symm
  have he : x = c * y := by simp [c]
  rw [he, hcomm.mul_pow, hc2, one_mul]

omit [Finite M] in
private noncomputable def squareMap (v : W × W) : W :=
  (d.coordinates ⟨(Classical.choose (d.onto (Multiplicative.ofAdd v))) ^ 2,
    d.square_mem _⟩).toAdd

private theorem squareMap_image (x : core R (alpha R)) :
    d.squareMap (d.quotient x).toAdd =
      (d.coordinates ⟨x ^ 2, d.square_mem x⟩).toAdd := by
  unfold squareMap
  congr 2
  apply Subtype.ext
  exact d.square_eq_of_image_eq (Classical.choose_spec (d.onto _))

private theorem squareMap_equivariant (g : S) (v : W × W) :
    d.squareMap (dual g v.1, dual g v.2) = g.val.mulVec (d.squareMap v) := by
  obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
  have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  have hv : (d.quotient x).toAdd = v := congrArg Multiplicative.toAdd hx
  have hact := d.action m x (coreAction (R := R) m x) rfl
  rw [hmg] at hact
  rw [← hv, ← hact, d.squareMap_image, d.squareMap_image, ← hmg]
  apply d.coordinates_action
  exact (map_pow (coreAction (R := R) m) x 2).symm

private theorem squareMap_first (v : W) : d.squareMap (v, 0) = 0 := by
  apply equivariantDualMap_zero (fun w => d.squareMap (w, 0)) _ v
  intro g w
  simpa only [dual, Matrix.mulVec_zero] using d.squareMap_equivariant g (w, 0)

private theorem squareMap_second (v : W) : d.squareMap (0, v) = 0 := by
  apply equivariantDualMap_zero (fun w => d.squareMap (0, w)) _ v
  intro g w
  simpa only [dual, Matrix.mulVec_zero] using d.squareMap_equivariant g (0, w)

private theorem square_eq_one_of_pure (x : core R (alpha R))
    (hx : (d.quotient x).toAdd.1 = 0 ∨ (d.quotient x).toAdd.2 = 0) : x ^ 2 = 1 := by
  apply (d.coordinates_zero_iff ⟨x ^ 2, d.square_mem x⟩).mp
  rw [← d.squareMap_image]
  rcases hx with hx | hx
  · have he : (d.quotient x).toAdd = (0, (d.quotient x).toAdd.2) :=
      Prod.ext hx rfl
    rw [he, d.squareMap_second]
  · have he : (d.quotient x).toAdd = ((d.quotient x).toAdd.1, 0) :=
      Prod.ext rfl hx
    rw [he, d.squareMap_first]

omit [Finite M] in
private theorem commutator_mem (x y : core R (alpha R)) : ⁅x,y⁆ ∈ d.quotient.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private theorem commutator_eq_one_of_pure
    (x y : core R (alpha R))
    (hpure : ((d.quotient x).toAdd.1 = 0 ∧ (d.quotient y).toAdd.1 = 0) ∨
      ((d.quotient x).toAdd.2 = 0 ∧ (d.quotient y).toAdd.2 = 0)) : ⁅x,y⁆ = 1 := by
  have hx : x ^ 2 = 1 := d.square_eq_one_of_pure x (hpure.elim
    (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  have hy : y ^ 2 = 1 := d.square_eq_one_of_pure y (hpure.elim
    (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  have hxy : (x*y) ^ 2 = 1 := by
    apply d.square_eq_one_of_pure
    rw [map_mul, toAdd_mul]
    rcases hpure with h | h
    · apply Or.inl
      change (d.quotient x).toAdd.1 + (d.quotient y).toAdd.1 = 0
      rw [h.1, h.2, add_zero]
    · apply Or.inr
      change (d.quotient x).toAdd.2 + (d.quotient y).toAdd.2 = 0
      rw [h.1, h.2, add_zero]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hy)
  rw [commutatorElement_def, hxi, hyi]
  simpa only [pow_two, mul_assoc] using hxy

/-- The standard central-extension pairing is restricted to the proven exact
kernel by its commutator evaluation formula, without identifying the center. -/
private theorem exists_actual_pairing :
    ∃ b : (W × W) → (W × W) → W,
      (∀ x y z, b (x+y) z = b x z + b y z) ∧
      (∀ x y : core R (alpha R), b (d.quotient x).toAdd (d.quotient y).toAdd =
        (d.coordinates ⟨⁅x,y⁆, d.commutator_mem x y⟩).toAdd) := by
  obtain ⟨B, hB⟩ := CentralExtension.exists_lift_commutator_pairing
    d.quotient d.onto d.kernel_central (MonoidHom.id (Multiplicative (W × W)))
  have hmem (x y : W × W) : ((B x y).toMul : core R (alpha R)) ∈ d.quotient.ker := by
    obtain ⟨a, ha⟩ := d.onto (Multiplicative.ofAdd x)
    obtain ⟨b, hb⟩ := d.onto (Multiplicative.ofAdd y)
    rw [hB x y a b ha hb]
    exact d.commutator_mem a b
  let b : (W × W) → (W × W) → W := fun x y =>
    (d.coordinates ⟨(B x y).toMul, hmem x y⟩).toAdd
  refine ⟨b, ?_, ?_⟩
  · intro x y z
    have he : (⟨(B (x+y) z).toMul, hmem (x+y) z⟩ : d.quotient.ker) =
        ⟨(B x z).toMul, hmem x z⟩ * ⟨(B y z).toMul, hmem y z⟩ := by
      apply Subtype.ext
      change ((B (x+y) z).toMul : core R (alpha R)) =
        (B x z).toMul * (B y z).toMul
      rw [map_add, AddMonoidHom.add_apply]
      rfl
    change (d.coordinates ⟨(B (x+y) z).toMul, _⟩).toAdd = _
    rw [he, map_mul, toAdd_mul]
  · intro x y
    apply congrArg (fun z : d.quotient.ker => (d.coordinates z).toAdd)
    apply Subtype.ext
    exact hB _ _ x y rfl rfl

omit [Finite M] in
private theorem pairing_symmetric
    (b : (W × W) → (W × W) → W)
    (heval : ∀ x y : core R (alpha R), b (d.quotient x).toAdd (d.quotient y).toAdd =
      (d.coordinates ⟨⁅x,y⁆, d.commutator_mem x y⟩).toAdd) (v w : W × W) : b v w = b w v := by
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd w)
  have hv : (d.quotient x).toAdd = v := congrArg Multiplicative.toAdd hx
  have hw : (d.quotient y).toAdd = w := congrArg Multiplicative.toAdd hy
  rw [← hv, ← hw, heval, heval]
  apply congrArg (fun z : d.quotient.ker => (d.coordinates z).toAdd)
  apply Subtype.ext
  have hs : (⁅x,y⁆ : core R (alpha R)) ^ 2 = 1 :=
    congrArg Subtype.val (d.kernel_square ⟨⁅x,y⁆, d.commutator_mem x y⟩)
  have hi : (⁅x,y⁆ : core R (alpha R))⁻¹ = ⁅x,y⁆ :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs)
  exact hi.symm.trans (commutatorElement_inv x y)

omit [Finite M] in
private theorem pairing_equivariant
    (b : (W × W) → (W × W) → W)
    (heval : ∀ x y : core R (alpha R), b (d.quotient x).toAdd (d.quotient y).toAdd =
      (d.coordinates ⟨⁅x,y⁆, d.commutator_mem x y⟩).toAdd)
    (g : S) (v w : W × W) :
    b (dual g v.1, dual g v.2) (dual g w.1, dual g w.2) = g.val.mulVec (b v w) := by
  obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
  have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd w)
  have hv : (d.quotient x).toAdd = v := congrArg Multiplicative.toAdd hx
  have hw : (d.quotient y).toAdd = w := congrArg Multiplicative.toAdd hy
  have hax := d.action m x (coreAction (R := R) m x) rfl
  have hay := d.action m y (coreAction (R := R) m y) rfl
  rw [hmg] at hax hay
  rw [← hv, ← hw, ← hax, ← hay, heval, heval, ← hmg]
  apply d.coordinates_action
  exact (map_commutatorElement (coreAction (R := R) m) x y).symm

include d in
/-- The actual double-dual quotient determines the center of the source core.
Its independent producer retains the complete geometric quotient argument. -/
theorem center_core :
    (center (core R (alpha R))).map (core R (alpha R)).subtype = U R (alpha R) := by
  refine le_antisymm ?_ (U_le_center_core source geometry common)
  obtain ⟨b, hadd, heval⟩ := d.exists_actual_pairing
  have hs := d.pairing_symmetric b heval
  have he := d.pairing_equivariant b heval
  have hfirst (v w : W) : b (v,0) (w,0) = 0 := by
    obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd (v,0))
    obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd (w,0))
    have hv : (d.quotient x).toAdd = (v,0) := congrArg Multiplicative.toAdd hx
    have hw : (d.quotient y).toAdd = (w,0) := congrArg Multiplicative.toAdd hy
    rw [← hv, ← hw, heval]
    apply (d.coordinates_zero_iff _).mpr
    exact d.commutator_eq_one_of_pure x y (Or.inr
      ⟨congrArg Prod.snd hv, congrArg Prod.snd hw⟩)
  have hsecond (v w : W) : b (0,v) (0,w) = 0 := by
    obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd (0,v))
    obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd (0,w))
    have hv : (d.quotient x).toAdd = (0,v) := congrArg Multiplicative.toAdd hx
    have hw : (d.quotient y).toAdd = (0,w) := congrArg Multiplicative.toAdd hy
    rw [← hv, ← hw, heval]
    apply (d.coordinates_zero_iff _).mpr
    exact d.commutator_eq_one_of_pure x y (Or.inl
      ⟨congrArg Prod.fst hv, congrArg Prod.fst hw⟩)
  have hne : ∃ x y, b x y ≠ 0 := by
    by_contra! hz
    apply d.noncommutative
    refine ⟨⟨fun x y => commutatorElement_eq_one_iff_mul_comm.mp ?_⟩⟩
    apply (d.coordinates_zero_iff ⟨⁅x,y⁆, d.commutator_mem x y⟩).mp
    rw [← heval, hz]
  rintro z ⟨x, hx, rfl⟩
  have hrad : ∀ y : W × W, b (d.quotient x).toAdd y = 0 := by
    intro v
    obtain ⟨y, hy⟩ := d.onto (Multiplicative.ofAdd v)
    have hv : (d.quotient y).toAdd = v := congrArg Multiplicative.toAdd hy
    rw [← hv, heval]
    apply (d.coordinates_zero_iff _).mpr
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((mem_center_iff.mp hx y).symm)
  have hq := alternating_pair_separating b hadd hs hfirst hsecond he hne
    (d.quotient x).toAdd hrad
  have hxk : x ∈ d.quotient.ker := congrArg Multiplicative.ofAdd hq
  rw [d.kernel] at hxk
  exact hxk

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.DoubleDualQuotient

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open Subgroup Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The existing two quotient-branch producers now feed the actual core-center
conclusion. Their independent source proofs are the only remaining premises. -/
theorem center_core_of_local_branches
    (source : LocalSource L R) {geometry : Geometry R}
    (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (hsmall : ∀ s : CriticalSegment geometry, s.SmallIntersection →
      Nonempty (SingleQuotient source common (fun g v => g.val.mulVec v)) ∨
        Nonempty (SingleQuotient source common Linear.dual))
    (hlarge : ∀ s : CriticalSegment geometry, ¬ s.SmallIntersection →
      Nonempty (OrbitFactors source common s.middle)) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype = U R (alpha R) := by
  obtain ⟨d⟩ := doubleDualQuotient_of_local_branches source common radius hb hsmall hlarge
  exact d.center_core

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
