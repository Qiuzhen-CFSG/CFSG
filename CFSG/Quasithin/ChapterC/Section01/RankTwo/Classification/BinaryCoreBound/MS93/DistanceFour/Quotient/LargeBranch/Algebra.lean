module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.Configuration
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Algebra of the marked binary dual factors

Restrict the actual core action to each normalized factor. The natural kernel
coordinates and the prescribed dual action give a `DualExtension`, so every
factor is elementary abelian of order 64. Transitivity on nonzero covectors
shows that its invariant subgroups above U are just U and the whole factor.
Consequently distinct factors intersect in U. A core order bound of 512 then
forces them to generate the core, giving the requested `OrbitFactors` data.

These are conditional assembly lemmas for MS93 (1993), (4.6.12), pp.910--912.
They do not construct the geometric factors or assert the required order bound.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open Linear
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  {common : CommonFacts R source geometry}

namespace DualFactor
variable {A : Subgroup (core R (alpha R))} (d : DualFactor source common A)

noncomputable def factorAction : M →* MulAut A where
  toFun m := {
    toFun x := ⟨coreAction (R := R) m x, d.normalized m x x.property⟩
    invFun x := ⟨coreAction (R := R) m⁻¹ x, d.normalized m⁻¹ x x.property⟩
    left_inv x := by
      apply Subtype.ext
      change coreAction (R := R) m⁻¹ (coreAction m (x : core R (alpha R))) = _
      rw [map_inv]
      exact MulAut.inv_apply_self _ _ _
    right_inv x := by
      apply Subtype.ext
      change coreAction (R := R) m (coreAction m⁻¹ (x : core R (alpha R))) = _
      rw [map_inv]
      exact MulAut.apply_inv_self _ _ _
    map_mul' x y := by apply Subtype.ext; exact map_mul (coreAction (R := R) m) (x : core R (alpha R)) (y : core R (alpha R)) }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : MulAut (core R (alpha R)) => f x) coreAction.map_one
  map_mul' m n := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : MulAut (core R (alpha R)) => f x) (coreAction.map_mul m n)

noncomputable def factorKernelCoordinates : d.quotient.ker ≃* Multiplicative W :=
  (MulEquiv.subgroupCongr d.kernel).trans
    ((subgroupOfEquivOfLe d.contains).trans
      ((subgroupOfEquivOfLe (U_le_core source geometry common)).trans common.natural.equiv))

theorem factorKernelCoordinates_action (m : M) (x y : d.quotient.ker)
    (hy : (y : A) = d.factorAction m x) :
    (d.factorKernelCoordinates y).toAdd =
      (common.natural.marking (source.projection m)).val.mulVec
        (d.factorKernelCoordinates x).toAdd := by
  apply common.natural.action
  exact congrArg (fun z : A => ((z : core R (alpha R)) : FreeAmalgam R)) hy

noncomputable def dualExtension [Finite M] : DualExtension (A := M) d.quotient where
  onto := d.onto
  central := by
    intro x hx
    have hxU : ((x : core R (alpha R)) : FreeAmalgam R) ∈ U R (alpha R) := by
      change x ∈ ((U R (alpha R)).subgroupOf (core R (alpha R))).subgroupOf A
      rwa [← d.kernel]
    obtain ⟨z, hz, he⟩ := U_le_center_core source geometry common hxU
    have hzx : z = (x : core R (alpha R)) := Subtype.ext he
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    simpa only [hzx, coe_mul] using (mem_center_iff.mp hz) (y : core R (alpha R))
  coordinates := d.factorKernelCoordinates
  projection := common.natural.marking.toMonoidHom.comp source.projection
  projection_onto := common.natural.marking.surjective.comp source.projection_surjective
  action := d.factorAction
  quotient_action m x := d.action m x _ rfl
  kernel_action := d.factorKernelCoordinates_action

include d

theorem square_eq_one [Finite M] (x : A) : x ^ 2 = 1 :=
  d.dualExtension.square_eq_one x

theorem isMulCommutative [Finite M] : IsMulCommutative A :=
  ⟨⟨d.dualExtension.commutative⟩⟩

theorem card : Nat.card A = 64 := by
  have hk : Nat.card d.quotient.ker = 8 := by
    rw [Nat.card_congr d.factorKernelCoordinates.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hq : Nat.card (A ⧸ d.quotient.ker) = 8 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective d.quotient d.onto).toEquiv,
      Nat.card_eq_fintype_card]
    decide
  rw [card_eq_card_quotient_mul_card_subgroup d.quotient.ker, hk, hq]

theorem invariant_between (F : Subgroup (core R (alpha R)))
    (hUF : (U R (alpha R)).subgroupOf (core R (alpha R)) ≤ F) (hFA : F ≤ A)
    (hn : ∀ m (x : core R (alpha R)), x ∈ F → coreAction (R := R) m x ∈ F) :
    F = (U R (alpha R)).subgroupOf (core R (alpha R)) ∨ F = A := by
  by_cases hFU : F ≤ (U R (alpha R)).subgroupOf (core R (alpha R))
  · exact Or.inl (le_antisymm hFU hUF)
  right
  apply le_antisymm hFA
  obtain ⟨x, hxF, hxU⟩ := SetLike.not_le_iff_exists.mp hFU
  let xA : A := ⟨x, hFA hxF⟩
  have hx : (d.quotient xA).toAdd ≠ 0 := by
    intro h
    apply hxU
    have hker : xA ∈ d.quotient.ker := congrArg Multiplicative.ofAdd h
    rw [d.kernel] at hker
    exact hker
  intro y hyA
  let yA : A := ⟨y, hyA⟩
  by_cases hy : (d.quotient yA).toAdd = 0
  · apply hUF
    have hker : yA ∈ d.quotient.ker := congrArg Multiplicative.ofAdd hy
    rw [d.kernel] at hker
    exact hker
  obtain ⟨g, hg⟩ := dual_orbit hx hy
  obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
  have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
  let z : A := d.factorAction m xA
  have hzF : (z : core R (alpha R)) ∈ F := hn m x hxF
  have he : d.quotient z = d.quotient yA := by
    apply congrArg Multiplicative.ofAdd
    exact (d.action m xA z rfl).trans (by rw [hmg]; exact hg)
  have hker : yA * z⁻¹ ∈ d.quotient.ker := by
    change d.quotient (yA * z⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [d.kernel] at hker
  have hf := F.mul_mem (hUF hker) hzF
  change (y * (z : core R (alpha R))⁻¹) * z ∈ F at hf
  simpa only [inv_mul_cancel_right] using hf

theorem intersect_of_ne {B : Subgroup (core R (alpha R))}
    (e : DualFactor source common B) (hne : A ≠ B) :
    A ⊓ B = (U R (alpha R)).subgroupOf (core R (alpha R)) := by
  rcases d.invariant_between (A ⊓ B) (le_inf d.contains e.contains) inf_le_left
    (fun m x hx => ⟨d.normalized m x hx.1, e.normalized m x hx.2⟩) with h | h
  · exact h
  · have hAB : A ≤ B := h ▸ inf_le_right
    let : Finite B := Nat.finite_of_card_ne_zero (by rw [e.card]; decide)
    exact (hne (eq_of_le_of_card_ge hAB (by rw [d.card, e.card]))).elim

end DualFactor

namespace LargeBranch

theorem core_finite [Finite M] (source : LocalSource L R) :
    Finite (core R (alpha R)) := by
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  exact Finite.of_injective
    (inclusion ((core_le_Q source).trans (fun _ hx => hx.1))) (inclusion_injective _)

theorem dualFactors_generate_of_card_le [Finite M] (radius : RadiusFacts R geometry)
    {A B : Subgroup (core R (alpha R))}
    (d : DualFactor source common A) (e : DualFactor source common B)
    (hne : A ≠ B) (hbound : Nat.card (core R (alpha R)) ≤ 512) : A ⊔ B = ⊤ := by
  let : Finite (core R (alpha R)) := core_finite source
  have hderived : _root_.commutator (core R (alpha R)) ≤
      (U R (alpha R)).subgroupOf (core R (alpha R)) := by
    change _ ≤ (U R (alpha R)).comap (core R (alpha R)).subtype
    rw [← map_le_iff_le_comap, map_subtype_commutator]
    rw [← radius.radius_derived (alpha R) rfl]
    exact commutator_mono (radius.core_le_radius (alpha R) rfl)
      (radius.core_le_radius (alpha R) rfl)
  let : A.Normal := Normal.of_commutator_le _ (hderived.trans d.contains)
  have hi : Nat.card (A ⊓ B : Subgroup (core R (alpha R))) = 8 := by
    rw [d.intersect_of_ne e hne,
      Nat.card_congr (subgroupOfEquivOfLe (U_le_core source geometry common)).toEquiv]
    exact U_card source geometry common
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B le_normalizer_of_normal
  rw [d.card, e.card, hi] at hp
  apply eq_top_of_le_card
  omega

theorem orbitFactors_of_distinct [Finite M] (radius : RadiusFacts R geometry)
    (c rho : Vertex R) (hrho : (cosetGraph R).dist (alpha R) rho = 2)
    (A B : Subgroup (core R (alpha R))) (hA : A ≤ coreOrbit c) (hB : B ≤ coreOrbit rho)
    (d : DualFactor source common A) (e : DualFactor source common B)
    (hne : A ≠ B) (hbound : Nat.card (core R (alpha R)) ≤ 512) :
    Nonempty (OrbitFactors source common c) :=
  ⟨⟨rho, hrho, A, B, hA, hB, d, e,
    dualFactors_generate_of_card_le radius d e hne hbound, d.intersect_of_ne e hne⟩⟩

end LargeBranch
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
