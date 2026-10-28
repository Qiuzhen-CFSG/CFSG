module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.SylowCalculation.Geometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Transport

/-!
# Coordinates for every invariant Sylow flag on five points

The nonidentity element of the invariant line is Sylow-fixed, hence singular:
a nonsingular stabilizer has even index ten. The other two plane elements
form an invariant pair. They cannot both be fixed, since the sum of two
distinct nonzero singular vectors is nonsingular. Thus the pair is exchanged,
and invariance of the quadratic form makes both elements nonsingular.
The simultaneous coordinate calculation then sends z and v into the flag;
orbit–stabilizer gives the literal indices ten and two.

The final theorem applies this calculation to the actual normalizer image
and the pulled-back source flag. It discharges the coordinate premises of
`FlagSource.construction_of_coordinate_witness` in the parent `Flags` module.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Notation 13.2.1
(p.877), the local Sylow step in 13.2.6 (p.879), and the marking paragraph
on p.926. This proves the finite local calculation used by those arguments.
-/

@[expose] public section
open Subgroup BinaryPermutation BinaryPermutation.FiveGeometry BinaryPermutation.FiveCentralizerGeometry
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.FlagCoordinates
open SylowCalculation

private theorem line_generator (H : Subgroup Perm) (P : Sylow 2 H)
    (U : Subgroup (Multiplicative Space)) (hc : Nat.card U = 2)
    (hinv : ∀ p : H, p ∈ (P : Subgroup H) → ∀ x : Multiplicative Space,
      x ∈ U → Multiplicative.ofAdd (rho p.val x.toAdd) ∈ U) :
    ∃ x : Space, x ≠ 0 ∧ zpowers (Multiplicative.ofAdd x) = U ∧
      ∀ p : H, p ∈ (P : Subgroup H) → rho p.val x = x := by
  obtain ⟨a, ha, hu⟩ := (Nat.card_eq_two_iff' (1 : U)).mp hc
  have ha' : a.val ≠ 1 := fun h => ha (Subtype.ext h)
  refine ⟨a.val.toAdd, ha', ?_, ?_⟩
  · apply le_antisymm (zpowers_le.mpr a.property)
    intro b hb
    by_cases h : b = 1
    · exact h ▸ (zpowers a.val).one_mem
    · have he := hu ⟨b, hb⟩ (fun he => h (congrArg Subtype.val he))
      exact (congrArg Subtype.val he).symm ▸ mem_zpowers a.val
  · intro p hp
    have hm := hinv p hp a.val a.property
    have hn : coordinateEquiv p.val a.val ≠ 1 := by
      intro he
      exact ha' ((coordinateEquiv p.val).injective (he.trans (map_one _).symm))
    have he := hu ⟨_, hm⟩ (fun he => hn (congrArg Subtype.val he))
    exact congrArg (fun b : U => b.val.toAdd) he

private theorem complement_pair
    (U₁ U₂ : Subgroup (Multiplicative Space)) (hle : U₁ ≤ U₂)
    (hc₁ : Nat.card U₁ = 2) (hc₂ : Nat.card U₂ = 4)
    (x y : Space) (hx : x ≠ 0) (hxm : Multiplicative.ofAdd x ∈ U₁)
    (hym : Multiplicative.ofAdd y ∈ U₂) (hyn : Multiplicative.ofAdd y ∉ U₁) :
    (U₂ : Set (Multiplicative Space)) \ U₁ =
      {Multiplicative.ofAdd y, Multiplicative.ofAdd (x + y)} := by
  have hxy : Multiplicative.ofAdd y ≠ Multiplicative.ofAdd (x + y) := by
    intro h
    apply hx
    have he : y = x + y := h
    exact add_right_cancel (he.symm.trans (zero_add y).symm)
  apply Eq.symm
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · intro w hw
    rcases hw with rfl | rfl
    · exact ⟨hym, hyn⟩
    · exact ⟨U₂.mul_mem (hle hxm) hym,
        fun h => hyn ((U₁.mul_mem_cancel_left hxm).mp h)⟩
  · rw [Set.ncard_sdiff hle, Set.ncard_pair hxy]
    change Nat.card U₂ - Nat.card U₁ ≤ 2
    omega

/-- Every invariant line–plane flag has standard five-point coordinates, with
stabilizer index ten in the actor and relative index two in its Sylow subgroup. -/
theorem exists_sylow_flag_coordinates
    (H : Subgroup Perm) (hH : alternatingGroup (Fin 5) ≤ H) (P : Sylow 2 H)
    (U₁ U₂ : Subgroup (Multiplicative Space)) (hle : U₁ ≤ U₂)
    (hc₁ : Nat.card U₁ = 2) (hc₂ : Nat.card U₂ = 4)
    (hinv₁ : ∀ p : H, p ∈ (P : Subgroup H) → ∀ x : Multiplicative Space,
      x ∈ U₁ → Multiplicative.ofAdd (rho p.val x.toAdd) ∈ U₁)
    (hinv₂ : ∀ p : H, p ∈ (P : Subgroup H) → ∀ x : Multiplicative Space,
      x ∈ U₂ → Multiplicative.ofAdd (rho p.val x.toAdd) ∈ U₂) :
    ∃ g : Perm, zpowers (Multiplicative.ofAdd (rho g z)) = U₁ ∧
      Multiplicative.ofAdd (rho g v) ∈ U₂ ∧
      Multiplicative.ofAdd (rho g v) ∉ U₁ ∧
      (stabilizer H (rho g v)).index = 10 ∧
      (stabilizer H (rho g v)).relIndex (P : Subgroup H) = 2 := by
  classical
  obtain ⟨x, hx, hxU, hfix⟩ := line_generator H P U₁ hc₁ hinv₁
  have hxm : Multiplicative.ofAdd x ∈ U₁ := hxU ▸ mem_zpowers _
  have hqx : form x = 0 := sylow_fixed_singular H hH P x hfix
  have hnle : ¬ U₂ ≤ U₁ := by
    intro h
    have he := le_antisymm hle h
    rw [he, hc₂] at hc₁
    omega
  obtain ⟨b, hb₂, hb₁⟩ := SetLike.not_le_iff_exists.mp hnle
  let y : Space := b.toAdd
  have hy : y ≠ 0 := by
    intro he
    exact hb₁ ((show b = 1 from he).symm ▸ U₁.one_mem)
  have hpair := complement_pair U₁ U₂ hle hc₁ hc₂ x y hx hxm hb₂ hb₁
  have hpimage (p : H) (hp : p ∈ (P : Subgroup H)) :
      rho p.val y = y ∨ rho p.val y = x + y := by
    have hm : coordinateEquiv p.val b ∈ (U₂ : Set (Multiplicative Space)) \ U₁ := by
      refine ⟨hinv₂ p hp b hb₂, ?_⟩
      intro hn
      have he := hinv₁ p⁻¹ ((P : Subgroup H).inv_mem hp) _ hn
      have heq := (coordinateEquiv p.val).left_inv b
      exact hb₁ (heq ▸ he)
    rw [hpair] at hm
    change _ = _ ∨ _ = _ at hm
    exact hm
  -- A fixed plane would contain two distinct singular vectors with singular sum.
  have hmoving : ∃ p : H, p ∈ (P : Subgroup H) ∧ rho p.val y ≠ y := by
    by_contra hn
    push Not at hn
    have hqy := sylow_fixed_singular H hH P y hn
    have hqxy := sylow_fixed_singular H hH P (x + y) (by
      intro p hp
      rw [map_add, hfix p hp, hn p hp])
    rcases singular_add x y hqx hqy hqxy with h | h | h
    · exact hx h
    · exact hy h
    · exact hb₁ (show Multiplicative.ofAdd y ∈ U₁ from h ▸ hxm)
  obtain ⟨p, hp, hpm⟩ := hmoving
  have hpy : rho p.val y = x + y := (hpimage p hp).resolve_left hpm
  -- The exchanged pair has a common quadratic value, which cannot be zero.
  have hqeq : form (x + y) = form y := hpy ▸ form_invariant p.val y
  have hqy : form y ≠ 0 := by
    intro h
    rcases singular_add x y hqx h (hqeq.trans h) with he | he | he
    · exact hx he
    · exact hy he
    · exact hb₁ (show Multiplicative.ofAdd y ∈ U₁ from he ▸ hxm)
  obtain ⟨g, hgx, hgy⟩ := exists_flag_permutation x y hx hqx hqy (hqeq ▸ hqy)
  refine ⟨g, hgx ▸ hxU, hgy ▸ hb₂, hgy ▸ hb₁, ?_, ?_⟩
  · rw [hgy]
    exact nonsingular_index H hH y hqy
  · rw [hgy]
    let := vectorAction H
    have horbit : MulAction.orbit P y = {y, x + y} := by
      ext w
      rw [MulAction.mem_orbit_iff]
      change (∃ q : P, q • y = w) ↔ (w = y ∨ w = x + y)
      constructor
      · rintro ⟨q, rfl⟩
        exact hpimage q.val q.property
      · rintro (rfl | rfl)
        · exact ⟨1, rfl⟩
        · exact ⟨⟨p, hp⟩, hpy⟩
    change (MulAction.stabilizer P y).index = 2
    rw [MulAction.index_stabilizer, horbit, Set.ncard_pair]
    intro he
    exact hx (add_right_cancel (he.symm.trans (zero_add y).symm))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.FlagCoordinates

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.FlagSource
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.FlagCoordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The source flag supplies all four coordinate clauses for the literal
normalizer image, its Sylow image, and the two preimages under the module map. -/
theorem exists_coordinate_witness (d : FlagSource T L V V₁ V₂) :
    ∃ g : Perm, zpowers (Multiplicative.ofAdd (rho g z)) = d.preimage V₁ ∧
      Multiplicative.ofAdd (rho g v) ∈ d.preimage V₂ ∧
      Multiplicative.ofAdd (rho g v) ∉ d.preimage V₁ ∧
      (stabilizer d.image (rho g v)).index = 10 ∧
      (stabilizer d.image (rho g v)).relIndex (d.imageSylow : Subgroup d.image) = 2 := by
  apply exists_sylow_flag_coordinates d.image d.alternating_le_image d.imageSylow
    (d.preimage V₁) (d.preimage V₂)
  · exact fun _ h => d.one_le_two h
  · exact (d.preimage_card V₁ (d.one_le_two.trans d.two_le_V)).trans d.one_card
  · exact (d.preimage_card V₂ d.two_le_V).trans d.two_card
  · exact d.preimage_invariant V₁ d.one_invariant
  · exact d.preimage_invariant V₂ d.two_invariant

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.FlagSource
