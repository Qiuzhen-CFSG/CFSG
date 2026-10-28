module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.Noncommutative
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Square

/-!
# Excluding a single marked natural or dual factor

Conjugation on the actual commutator core and the given marking of U_alpha
supply the action and kernel coordinates. Literal squares are constant on
quotient fibers because U_alpha is central and elementary. In the natural
case their induced equivariant map is additive, forcing commutativity. In
the dual case the existing marked extension calculation makes squares one.
Both conclusions contradict `core_not_commutative`.

The quotient maps in `SingleQuotient` are hypotheses of these obstruction
lemmas, not asserted source constructions. The missing geometric recognition
step must construct such a map before the obstruction applies.

Source: original Meierfrankenfeld--Stellmacher (1993), (4.6.11), p.909.
No duality is assumed in the natural-to-natural square calculation.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open Linear
variable {M : Type*} [Group M] {L R : Subgroup M}
  (source : LocalSource L R) (geometry : Geometry R)
  (common : CommonFacts R source geometry)

noncomputable def coreAction : M →* MulAut (core R (alpha R)) :=
  (core R (alpha R)).normalizerMonoidHom.comp
    ((embedM R).codRestrict _ fun m => core_normalized (R := R) ⟨m, rfl⟩)

theorem coreAction_val (m : M) (x : core R (alpha R)) :
    (coreAction (R := R) m x : FreeAmalgam R) =
      embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ := rfl

noncomputable def kernelCoordinates (q : core R (alpha R) →* Multiplicative W)
    (hk : q.ker = (U R (alpha R)).subgroupOf (core R (alpha R))) :
    q.ker ≃* Multiplicative W :=
  (MulEquiv.subgroupCongr hk).trans
    ((subgroupOfEquivOfLe (U_le_core source geometry common)).trans common.natural.equiv)

theorem kernelCoordinates_action
    (q : core R (alpha R) →* Multiplicative W)
    (hk : q.ker = (U R (alpha R)).subgroupOf (core R (alpha R)))
    (m : M) (x y : q.ker) (hy : (y : core R (alpha R)) = coreAction (R := R) m x) :
    (kernelCoordinates source geometry common q hk y).toAdd =
      (common.natural.marking (source.projection m)).val.mulVec
        (kernelCoordinates source geometry common q hk x).toAdd := by
  apply common.natural.action
  exact congrArg Subtype.val hy

include common in
theorem kernel_central [Finite M] (q : core R (alpha R) →* Multiplicative W)
    (hk : q.ker = (U R (alpha R)).subgroupOf (core R (alpha R))) :
    q.ker ≤ center (core R (alpha R)) := by
  intro x hx
  have hxU : (x : FreeAmalgam R) ∈ U R (alpha R) := by
    change x ∈ (U R (alpha R)).subgroupOf (core R (alpha R))
    rwa [← hk]
  obtain ⟨y, hy, he⟩ := U_le_center_core source geometry common hxU
  have hxy : y = x := Subtype.ext he
  exact hxy ▸ hy

variable {geometry} in
structure SingleQuotient (σ : SL → W → W) where
  quotient : core R (alpha R) →* Multiplicative W
  onto : Function.Surjective quotient
  kernel : quotient.ker = (U R (alpha R)).subgroupOf (core R (alpha R))
  action : ∀ (m : M) (x y : core R (alpha R)),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    (quotient y).toAdd = σ (common.natural.marking (source.projection m)) (quotient x).toAdd

namespace SingleQuotient
variable {source geometry common}
  (d : SingleQuotient source common (fun g v => g.val.mulVec v))

private theorem ker_square (x : d.quotient.ker) : x ^ 2 = 1 := by
  let e := kernelCoordinates source geometry common d.quotient d.kernel
  apply e.injective
  rw [map_pow, map_one, pow_two]
  change Multiplicative.ofAdd ((e x).toAdd + (e x).toAdd) = Multiplicative.ofAdd 0
  congr 1
  ext i
  exact CharTwo.add_self_eq_zero _

private theorem square_eq_of_image_eq [Finite M]
    {x y : core R (alpha R)} (h : d.quotient x = d.quotient y) : x ^ 2 = y ^ 2 := by
  let c := x * y⁻¹
  have hc : c ∈ d.quotient.ker := by
    change d.quotient (x * y⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hc2 : c ^ 2 = 1 := congrArg Subtype.val (d.ker_square ⟨c, hc⟩)
  have hcomm : Commute c y :=
    (mem_center_iff.mp (kernel_central source geometry common d.quotient d.kernel hc) y).symm
  have he : x = c * y := by simp [c]
  calc
    x ^ 2 = (c * y) ^ 2 := congrArg (fun z : core R (alpha R) => z ^ 2) he
    _ = c ^ 2 * y ^ 2 := hcomm.mul_pow 2
    _ = y ^ 2 := by rw [hc2, one_mul]

private noncomputable def squareMap (v : W) : W :=
  (kernelCoordinates source geometry common d.quotient d.kernel
    ⟨(Classical.choose (d.onto (Multiplicative.ofAdd v))) ^ 2,
      DualExtension.square_mem d.quotient _⟩).toAdd

private theorem squareMap_image [Finite M] (x : core R (alpha R)) :
    d.squareMap (d.quotient x).toAdd =
      (kernelCoordinates source geometry common d.quotient d.kernel
        ⟨x ^ 2, DualExtension.square_mem d.quotient x⟩).toAdd := by
  unfold squareMap
  congr 2
  apply Subtype.ext
  exact d.square_eq_of_image_eq (Classical.choose_spec (d.onto _))

private theorem squareMap_equivariant [Finite M] (g : S) (v : W) :
    d.squareMap (g.val.mulVec v) = g.val.mulVec (d.squareMap v) := by
  obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
  have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  have hv : (d.quotient x).toAdd = v := congrArg Multiplicative.toAdd hx
  have haction := d.action m x (coreAction (R := R) m x) rfl
  rw [hmg] at haction
  rw [← hv, ← haction, d.squareMap_image, d.squareMap_image, ← hmg]
  apply kernelCoordinates_action
  exact (map_pow (coreAction (R := R) m) x 2).symm

include d in
theorem natural_impossible [Finite M] (radius : RadiusFacts R geometry) : False := by
  apply core_not_commutative source geometry common radius
  exact ⟨⟨commutative_of_natural_square_map d.quotient d.quotient.ker
    (kernelCoordinates source geometry common d.quotient d.kernel)
    (DualExtension.square_mem d.quotient) d.squareMap d.squareMap_image
    d.squareMap_equivariant⟩⟩

omit d in
theorem dual_impossible [Finite M] (radius : RadiusFacts R geometry)
    (d : SingleQuotient source common dual) : False := by
  let e : DualExtension (A := M) d.quotient := {
    onto := d.onto
    central := kernel_central source geometry common d.quotient d.kernel
    coordinates := kernelCoordinates source geometry common d.quotient d.kernel
    projection := common.natural.marking.toMonoidHom.comp source.projection
    projection_onto := common.natural.marking.surjective.comp source.projection_surjective
    action := coreAction (R := R)
    quotient_action := fun m x => d.action m x _ rfl
    kernel_action := kernelCoordinates_action source geometry common d.quotient d.kernel }
  exact core_not_commutative source geometry common radius ⟨⟨e.commutative⟩⟩

end SingleQuotient
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
