module

public import Theory.AtlasPort.LinearGroups.G2.EvenBorelAction
public import Theory.FieldTheory.BinaryTorusInvolution
public import Theory.GroupAction.Defs
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Outer actors have large G₂ Borel commutators

The torus projection sends the Borel commutator onto a group containing two
independent copies of the field displacement image. A nontrivial field
actor has nontrivial displacement, so this image has at least four elements.
The torus has odd order, hence the projection kills the commutator's two-core.
This proves the bound on the actual commutator quotient, even when the actor
has a nontrivial inner factor. In particular G₂(4) is not a small exception.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. The actual model
and coefficient action are the licensed ATLAS construction; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.EvenBorelTorus
open Subgroup LieAutomorphismExtensions FiniteField.BinaryTorusInvolution
open scoped Pointwise
variable {F : Type*} [Field F]

private theorem odd_image_card_le_quotient_twoCore
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hodd : Odd (Nat.card H)) :
    Nat.card f.range ≤ Nat.card (G ⧸ pCore 2 G) := by
  have hk : pCore 2 G ≤ f.rangeRestrict.ker := by
    intro x hx
    obtain ⟨k,hk⟩ := pCore_isPGroup (⟨x,hx⟩ : pCore 2 G)
    have hp : f x ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      exact congrArg f (congrArg Subtype.val hk) |>.trans f.map_one
    have he : f x = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left k)
        (orderOf_dvd_of_pow_eq_one hp) (orderOf_dvd_natCard _))
    exact Subtype.ext he
  let q := QuotientGroup.lift (pCore 2 G) f.rangeRestrict hk
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x,hx⟩ := f.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk x,hx⟩
  exact Nat.card_le_card_of_surjective q hq

private theorem displacement_ne_bot (σ : F ≃+* F) (hσ : σ ≠ 1) :
    (displacement σ).range ≠ ⊥ := by
  intro he
  have hu (u : Fˣ) : Units.map σ.toMonoidHom u = u := by
    have h : displacement σ u ∈ (displacement σ).range := ⟨u,rfl⟩
    rw [he, mem_bot] at h
    exact mul_inv_eq_one.mp h
  apply hσ
  apply RingEquiv.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · exact congrArg Units.val (hu (Units.mk0 x hx))

/-- The commutator with a Sylow-stabilizing semilinear actor stays in the Borel. -/
theorem semilinear_commutator_le_borel [CharP F 2]
    (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : unipotent.map (semilinearAction z).toMonoidHom = unipotent) :
    commutatorSubgroup (zpowers (semilinearAction z)) (Model F) borel ≤ borel := by
  have hstab : zpowers (semilinearAction z) ≤
      MulAction.stabilizer (MulAut (Model F)) borel :=
    zpowers_le.mpr (semilinear_map_borel z hz)
  apply (closure_le _).mpr
  rintro x ⟨a,b,hb,rfl⟩
  apply borel.mul_mem (borel.inv_mem hb)
  have ha : borel.map a.val.toMonoidHom = borel := hstab a.property
  rw [← ha]
  exact mem_map_of_mem a.val.toMonoidHom hb

/-- Every nontrivial field part gives more than three elements modulo the
actual commutator's two-core. No pure-field assumption is made. -/
theorem semilinear_commutator_quotient_gt_three [Finite F] [CharP F 2]
    (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : unipotent.map (semilinearAction z).toMonoidHom = unipotent)
    (hσ : z.right ≠ 1) :
    let C := commutatorSubgroup (zpowers (semilinearAction z)) (Model F) borel
    3 < Nat.card (C ⧸ pCore 2 C) := by
  let C := commutatorSubgroup (zpowers (semilinearAction z)) (Model F) borel
  let hCB : C ≤ borel := semilinear_commutator_le_borel z hz
  let f : C →* (Fˣ × Fˣ) := projection.comp (inclusion hCB)
  have hdisp (p : Fˣ × Fˣ) :
      (displacement z.right p.1, displacement z.right p.2) ∈ f.range := by
    let b : borel (K := F) :=
      ⟨torusHom p, (le_sup_right : splitTorus ≤ borel) ⟨p,rfl⟩⟩
    let c : C := ⟨b.val⁻¹ * semilinearAction z b.val,
      subset_closure ⟨⟨semilinearAction z,mem_zpowers _⟩,b.val,b.property,rfl⟩⟩
    refine ⟨c,?_⟩
    have he : inclusion hCB c = b⁻¹ *
        restrictActor (semilinearAction z) (semilinear_map_borel z hz) b := rfl
    change projection (inclusion hCB c) = _
    rw [he, map_mul, map_inv, projection_semilinear z hz, projection_torus]
    ext <;> simp [displacement, mul_comm]
  have hle : (displacement z.right).range.prod (displacement z.right).range ≤ f.range := by
    rintro ⟨x,y⟩ ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩
    exact hdisp (u,v)
  have hcard : 3 < Nat.card ((displacement z.right).range.prod (displacement z.right).range) := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
    have htwo : 1 < Nat.card (displacement z.right).range :=
      (one_lt_card_iff_ne_bot _).mpr (displacement_ne_bot z.right hσ)
    nlinarith
  have hodd : Odd (Nat.card (Fˣ × Fˣ)) := by
    rw [Nat.card_congr torusParameterEquiv.toEquiv]
    exact card_torus_odd
  exact hcard.trans_le ((card_le_of_le hle).trans
    (odd_image_card_le_quotient_twoCore f hodd))

/-- The intrinsic outer-actor bound, conditional only on inner–field coverage.
It includes both source exceptional degrees and in particular G₂(4). -/
theorem outer_commutator_quotient_gt_three [Finite F] [CharP F 2]
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (α : MulAut (Model F)) (hα : unipotent.map α.toMonoidHom = unipotent)
    (hout : α ∉ MulAut.innerSubgroup (Model F)) :
    let C := commutatorSubgroup (zpowers α) (Model F) borel
    3 < Nat.card (C ⧸ pCore 2 C) := by
  obtain ⟨z,rfl⟩ := hcover α
  apply semilinear_commutator_quotient_gt_three z hα
  intro hσ
  apply hout
  have he : semilinearAction z = MulAut.conj z.left := by
    rw [semilinearAction_apply, hσ, map_one, mul_one]
  rw [he]
  exact ⟨z.left,rfl⟩

end Atlas.G2.EvenBorelTorus
