module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient.Contract
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient.Calculation.Geometry

/-!
# Lifting fixed vectors through the marked natural coordinates

The actor contains the projection kernel, so every element of its quotient
normalizer lifts to its actual normalizer. Hence the coordinate image of E
is invariant under the full normalizer of the marked order-four actor.
A nonzero image is its entire natural fixed space; the exact coordinate
kernel and N ≤ E then lift fixed vectors back to E.

Source: MS93 (1993), the fixed-quotient equality in (4.6.7), p.904.
The projection is composed with the natural factor’s own marking.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement.Calculation
open Escape.Propagation.Backward.Products.Selection.Choices
variable {A : Type*} [Group A]

private theorem coordinates_fixed {π : A →* SL} {V N : Subgroup A}
    (n : RankOnePairing.NaturalFactor π ⊤ V N) [N.Normal]
    (J : Subgroup A) (x : V) :
    n.coordinates x ∈ fixedSpace (J.map (n.marking.toMonoidHom.comp π)) ↔
      (x : A) ∈ centralizerModulo V J N := by
  rw [mem_centralizerModulo_iff]
  constructor
  · intro hx
    refine ⟨x.property, ?_⟩
    intro j hj
    let y : V := ⟨j * (x : A) * j⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top j)) _).mp x.property⟩
    have he : n.coordinates y = n.coordinates x := by
      apply Multiplicative.toAdd.injective
      rw [n.action j (mem_top j) x y rfl]
      exact congrArg Multiplicative.toAdd (hx _ (mem_map_of_mem _ hj))
    have hk : y * x⁻¹ ∈ n.coordinates.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [n.kernel] at hk
    exact hk
  · rintro ⟨_, hx⟩ g ⟨j, hj, rfl⟩
    let y : V := ⟨j * (x : A) * j⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top j)) _).mp x.property⟩
    have hk : y * x⁻¹ ∈ n.coordinates.ker := by
      rw [n.kernel]
      exact hx j hj
    have he : n.coordinates y = n.coordinates x := by
      simpa only [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] using hk
    apply Multiplicative.toAdd.injective
    change (n.marking (π j)).val.mulVec (n.coordinates x).toAdd = _
    rw [← n.action j (mem_top j) x y rfl, he]

/-- A normalizer-invariant subgroup with a nonzero moving image contains
the whole fixed preimage in the same marked natural factor. -/
theorem natural_fixed_le {π : A →* SL} {V N E J : Subgroup A}
    (n : RankOnePairing.NaturalFactor π ⊤ V N) [N.Normal]
    (hπ : Function.Surjective π) (hker : π.ker ≤ J)
    (hcard : Nat.card (J.map π) = 4) (hNE : N ≤ E)
    (hfix : ⁅E, J⁆ ≤ N)
    (hnorm : normalizer (J : Set A) ≤ normalizer (E : Set A))
    (hout : ¬ E ⊓ V ≤ N) : centralizerModulo V J N ≤ E := by
  let p := n.marking.toMonoidHom.comp π
  let B := J.map p
  let W := (E.subgroupOf V).map n.coordinates
  have hp : Function.Surjective p := n.marking.surjective.comp hπ
  have hk : p.ker ≤ J := by
    rw [MonoidHom.ker_comp_of_injective π n.marking.toMonoidHom n.marking.injective]
    exact hker
  have hB : Nat.card B = 4 := by
    change Nat.card (J.map (n.marking.toMonoidHom.comp π)) = 4
    rw [← map_map, card_map_of_injective n.marking.injective, hcard]
  have hW : W ≤ fixedSpace B := by
    rintro v ⟨x, hx, rfl⟩
    apply (coordinates_fixed n J x).mpr
    apply mem_centralizerModulo_iff.mpr
    refine ⟨x.property, ?_⟩
    intro j hj
    exact (commutator_comm E J ▸ hfix) (commutator_mem_commutator hj hx)
  have hne : W ≠ ⊥ := by
    obtain ⟨x, hx, hxN⟩ := SetLike.not_le_iff_exists.mp hout
    intro he
    have hv : n.coordinates ⟨x, hx.2⟩ ∈ W := mem_map_of_mem _ hx.1
    rw [he] at hv
    have hh : (⟨x, hx.2⟩ : V) ∈ n.coordinates.ker := mem_bot.mp hv
    rw [n.kernel] at hh
    exact hxN hh
  have hWfull : W = fixedSpace B := by
    apply invariant_fixed_eq B hB W hW hne
    intro g hg v hv
    obtain ⟨a, rfl⟩ := hp g
    have ha : a ∈ normalizer (J : Set A) := by
      have he := comap_normalizer_eq_of_surjective B hp
      rw [show B.comap p = J from comap_map_eq_self hk] at he
      rw [← he]
      exact hg
    obtain ⟨x, hx, rfl⟩ := hv
    let y : V := ⟨a * (x : A) * a⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top a)) _).mp x.property⟩
    have hy : (y : A) ∈ E :=
      (mem_normalizer_iff.mp (hnorm ha) _).mp hx
    refine ⟨y, hy, ?_⟩
    exact n.action a (mem_top a) x y rfl
  intro x hx
  have hxV := (mem_centralizerModulo_iff.mp hx).1
  have hv : n.coordinates ⟨x, hxV⟩ ∈ W :=
    hWfull.symm ▸ (coordinates_fixed n J ⟨x, hxV⟩).mpr hx
  obtain ⟨y, hy, he⟩ := hv
  have hkxy : (⟨x, hxV⟩ : V) * y⁻¹ ∈ n.coordinates.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  rw [n.kernel] at hkxy
  have hh := E.mul_mem (hNE hkxy) hy
  change (x * (y : A)⁻¹) * (y : A) ∈ E at hh
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement.Calculation
