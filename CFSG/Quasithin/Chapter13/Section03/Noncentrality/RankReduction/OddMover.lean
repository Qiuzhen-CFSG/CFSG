module
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Plane
public import Theory.GroupTheory.InvertedOddLift
/-!
# An odd-order mover from the actual cubic plane action

The order-three image of the plane parabolic contains a nontrivial cyclic
actor. Taking an odd power of a lift preserves that image, even in the
central three-cover. Such an actor cannot normalize the source point:
the automorphisms of a four-group fixing a nonidentity point have order
at most two. No splitting of the central covering kernel is required.

Source: Aschbacher–Smith, 13.3.14(b), printed p.891. The subsequent rank
argument only needs odd order; no order-three lift is asserted.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsKleinFour
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section05.AmbientSource
variable {G : Type*} [Group G] [Finite G]
/-- The literal plane parabolic has an odd-order element moving the source point. -/
theorem exists_odd_plane_mover (P E X : Subgroup G) [IsKleinFour E]
    (hP : Nat.card P = 2) (hPE : P ≤ E)
    (hx : Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3) :
    ∃ g : G, g ∈ X ∧ Odd (orderOf g) ∧ g ∈ normalizer (E : Set G) ∧
      g ∉ normalizer (P : Set G) := by
  let N := normalizer (E : Set G)
  let A := (X.subgroupOf N).map (planeAction E)
  have hA : A ≠ ⊥ := by intro h; have hh := hx; change Nat.card A = 3 at hh; simp [h] at hh
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  obtain ⟨x,hxX,hxa⟩ := a.property
  have horder : orderOf (planeAction E x) = 3 := by
    rw [hxa]
    apply orderOf_eq_prime
    · have hh := pow_card_eq_one' (x := a)
      change a ^ Nat.card A = 1 at hh
      rw [show Nat.card A = 3 from hx] at hh
      exact congrArg Subtype.val hh
    · exact fun hh => ha (Subtype.ext hh)
  obtain ⟨r,hr,hro,hrimage⟩ := (planeAction E).exists_odd_power_preserving_zpowers_image x
    (by rw [horder]; decide)
  have hrX : r.val ∈ X := (zpowers_le.mpr hxX) hr
  have hrf : orderOf (planeAction E r) = 3 := by
    have hc := congrArg (fun A : Subgroup (Equiv.Perm (Fin 3)) => Nat.card A) hrimage
    rwa [Nat.card_zpowers, Nat.card_zpowers, horder] at hc
  refine ⟨r.val,hrX,?_,r.property,?_⟩
  · simpa only [Subgroup.orderOf_coe] using hro
  · intro hPnorm
    have hPne : P ≠ ⊥ := by intro he; simp [he] at hP
    obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
    let zE : E := ⟨z.val,hPE z.property⟩
    let B := (zpowers r).map E.normalizerMonoidHom
    have hBc : Nat.card B = 3 := by
      dsimp only [B]
      rw [MonoidHom.map_zpowers,Nat.card_zpowers]
      exact ((IsKleinFour.autEquivPermThree E).orderOf_eq _).symm.trans hrf
    have hsmall : Nat.card B ≤ 2 := card_mulAut_subgroup_le_two_of_fixed_point
      (IsKleinFour.card_four (G := E)) zE
      (fun hh => hz (Subtype.ext (congrArg (fun w : E => w.val) hh))) B (by
        rintro b ⟨w,hw,rfl⟩
        have hwn : w.val ∈ normalizer (P : Set G) :=
          (zpowers_le.mpr (show r ∈ (normalizer (P : Set G)).subgroupOf N from hPnorm)) hw
        have hwc := normalizer_le_centralizer_of_card_two P hP hwn
        apply Subtype.ext
        change w.val * z.val * w.val⁻¹ = z.val
        rw [← mem_centralizer_iff.mp hwc z.val z.property,mul_inv_cancel_right])
    omega
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
