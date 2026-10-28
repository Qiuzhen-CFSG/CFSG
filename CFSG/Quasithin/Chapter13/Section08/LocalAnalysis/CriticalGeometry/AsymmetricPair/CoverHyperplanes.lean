module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverHyperplanes.Geometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Actions
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs

/-!
# The S₆ cover calculations in the asymmetric critical pair

A genuine identification of H/O₂(H) with S₆ and of U_H/V₁ with its
augmentation core transfers the common-center and fixed-hyperplane
calculations. The intertwining equation uses actual conjugation and both
canonical quotient maps. An ambient order-two commutator line disjoint from
V₁ gives an order-two star image, with its transposition and center identified.

For B ≤ W ≤ H, a nontrivial B* in that actor and [W,Cpre] ≤ A force W* = B*.
Here Cpre is defined as the actual preimage in U_H of the fixed subspace of
B*, and A is the ambient line whose image is the common center. Neither the
star-image equality nor the resulting subgroup factorization is an input.

Source: Aschbacher–Smith, 13.8.7, printed p.949, last two paragraphs (PDF p.966).
The parent supplies the cover identification from 13.8.5–6 and the displayed
ambient commutator bounds. This module is independent of the symplectic
placement argument in the preceding source paragraph.
-/

@[expose] public section
open BinaryPermutation Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverHyperplanes

variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]

/-- An actual cover identification, with the two canonical quotient maps
and conjugation retained in its intertwining equation. -/
structure CoverCoordinates where
  groupEquiv : Source.Hstar H ≃* Perm
  linearEquiv : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] Core
  normalizes : H ≤ normalizer (Source.UH H V₃ : Set G)
  intertwines : ∀ (h : H) (u : Source.UH H V₃),
    act (groupEquiv (QuotientGroup.mk' (pCore 2 H) h))
      (linearEquiv (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))) =
    linearEquiv (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
      ⟨(h : G) * (u : G) * (h : G)⁻¹,
        (mem_normalizer_iff.mp (normalizes h.property) u).mp u.property⟩))

variable {H V₃ V₁}
namespace CoverCoordinates
variable (d : CoverCoordinates H V₃ V₁)

/-- The literal star image, expressed in S₆. -/
def modelImage (X : Subgroup G) : Subgroup Perm :=
  (Source.starImage H X).map d.groupEquiv.toMonoidHom

/-- The canonical quotient projection followed by the cover coordinates. -/
noncomputable def coordinates : Additive (Source.UH H V₃) →ₗ[ZMod 2] Core :=
  d.linearEquiv.toLinearMap.comp
    ((QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))).toAdditive.toZModLinearMap 2)

/-- The actual image of an ambient subgroup in the augmentation module. -/
noncomputable def image (A : Subgroup G) : Submodule (ZMod 2) Core :=
  ((AddSubgroup.toZModSubmodule (n := 2)) (A.subgroupOf (Source.UH H V₃)).toAddSubgroup).map
    d.coordinates

/-- The ambient preimage in U_H of the actual fixed subspace of B*. -/
noncomputable def fixedPreimage (B : Subgroup G) : Subgroup G :=
  (((fixed (d.modelImage B)).comap d.coordinates).toAddSubgroup.toSubgroup).map
    (Source.UH H V₃).subtype

lemma coordinates_surjective : Function.Surjective d.coordinates := by
  intro x
  obtain ⟨v, rfl⟩ := d.linearEquiv.surjective x
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  exact ⟨Additive.ofMul u, congrArg (fun z => d.linearEquiv (Additive.ofMul z)) hu⟩

lemma mem_modelImage (X : Subgroup G) (g : Perm) :
    g ∈ d.modelImage X ↔ ∃ h : H, (h : G) ∈ X ∧
      d.groupEquiv (QuotientGroup.mk' (pCore 2 H) h) = g := by
  constructor
  · rintro ⟨s, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨_, ⟨h, hh, rfl⟩, rfl⟩

lemma modelImage_mono {B W : Subgroup G} (h : B ≤ W) : d.modelImage B ≤ d.modelImage W :=
  Subgroup.map_mono (Subgroup.map_mono (subgroupOf_mono H h))

lemma modelImage_ne_bot {X : Subgroup G} (h : Source.starImage H X ≠ ⊥) :
    d.modelImage X ≠ ⊥ := by
  intro he
  exact h ((Subgroup.map_eq_bot_iff_of_injective _ d.groupEquiv.injective).mp he)

lemma modelImage_injective {B W : Subgroup G} (h : d.modelImage B = d.modelImage W) :
    Source.starImage H B = Source.starImage H W :=
  Subgroup.map_injective d.groupEquiv.injective h

lemma mem_image (A : Subgroup G) (u : Source.UH H V₃) (hu : (u : G) ∈ A) :
    d.coordinates (Additive.ofMul u) ∈ d.image A :=
  ⟨Additive.ofMul u, hu, rfl⟩

lemma mem_fixedPreimage (B : Subgroup G) (u : Source.UH H V₃) :
    (u : G) ∈ d.fixedPreimage B ↔ d.coordinates (Additive.ofMul u) ∈ fixed (d.modelImage B) := by
  constructor
  · rintro ⟨v, hv, he⟩
    have : v = u := Subtype.ext he
    exact this ▸ hv
  · intro hu
    exact ⟨u, hu, rfl⟩

/-- The coordinate displacement is the image of the actual group commutator. -/
lemma displacement_mem_image (A : Subgroup G) (h : H) (u : Source.UH H V₃)
    (hcomm : ⁅(h : G), (u : G)⁆ ∈ A) :
    act (d.groupEquiv (QuotientGroup.mk' (pCore 2 H) h))
      (d.coordinates (Additive.ofMul u)) - d.coordinates (Additive.ofMul u) ∈ d.image A := by
  let v : Source.UH H V₃ := ⟨(h : G) * (u : G) * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.normalizes h.property) u).mp u.property⟩
  have hc : ((v / u : Source.UH H V₃) : G) ∈ A := by
    simpa only [coe_div, div_eq_mul_inv, v, coe_mul, coe_inv, commutatorElement_def] using hcomm
  have he : act (d.groupEquiv (QuotientGroup.mk' (pCore 2 H) h))
      (d.coordinates (Additive.ofMul u)) = d.coordinates (Additive.ofMul v) :=
    d.intertwines h u
  rw [he, ← map_sub]
  exact d.mem_image A (v / u) hc

/-- Ambient commutator containment gives the common-center displacement bound. -/
lemma subgroup_displacement (X A : Subgroup G)
    (hc : ⁅X, Source.UH H V₃⁆ ≤ A) :
    ∀ g ∈ d.modelImage X, ∀ x : Core, act g x - x ∈ d.image A := by
  intro g hg x
  obtain ⟨h, hh, rfl⟩ := (d.mem_modelImage X g).mp hg
  obtain ⟨u, rfl⟩ := d.coordinates_surjective x
  exact d.displacement_mem_image A h u.toMul
    (hc (commutator_mem_commutator hh u.toMul.property))

/-- An order-two ambient line survives as a line precisely when it is
disjoint from the quotient denominator. -/
lemma image_finrank_of_card_two (A : Subgroup G) (hAU : A ≤ Source.UH H V₃)
    (hcard : Nat.card A = 2) (hdisj : V₁ ⊓ A = ⊥) :
    Module.finrank (ZMod 2) (d.image A) = 1 := by
  obtain ⟨a, ha, hlast⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
  let u : Source.UH H V₃ := ⟨a.val, hAU a.property⟩
  let v : Core := d.coordinates (Additive.ofMul u)
  have hv : v ≠ 0 := by
    intro hv0
    have hq : QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u = 1 := by
      apply d.linearEquiv.injective
      exact hv0.trans (map_zero d.linearEquiv).symm
    have hz : (u : G) ∈ V₁ := (QuotientGroup.eq_one_iff u).mp hq
    have he : (a : G) = 1 := mem_bot.mp (hdisj ▸ (show (a : G) ∈ V₁ ⊓ A from ⟨hz, a.property⟩))
    exact ha (Subtype.ext he)
  have him : d.image A = Submodule.span (ZMod 2) {v} := by
    apply le_antisymm
    · rintro x ⟨w, hw, rfl⟩
      change w.toMul.val ∈ A at hw
      by_cases hw1 : w.toMul.val = 1
      · have he : w = 0 := Subtype.ext hw1
        rw [he, map_zero]
        exact Submodule.zero_mem _
      · have he := congrArg Subtype.val
          (hlast ⟨w.toMul.val, hw⟩ (fun h => hw1 (congrArg Subtype.val h)))
        have he' : w = Additive.ofMul u := Subtype.ext he
        rw [he']
        exact Submodule.mem_span_singleton_self v
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (d.mem_image A u a.property))
  rw [him]
  exact finrank_span_singleton hv

/-- The source commutator bound on the actual fixed preimage transfers to
restricted displacement on the fixed hyperplane. -/
lemma fixed_displacement (B W A : Subgroup G)
    (hc : ⁅W, d.fixedPreimage B⁆ ≤ A) :
    ∀ g ∈ d.modelImage W, ∀ x ∈ fixed (d.modelImage B), act g x - x ∈ d.image A := by
  intro g hg x hx
  obtain ⟨h, hh, rfl⟩ := (d.mem_modelImage W g).mp hg
  obtain ⟨u, rfl⟩ := d.coordinates_surjective x
  exact d.displacement_mem_image A h u.toMul
    (hc (commutator_mem_commutator hh ((d.mem_fixedPreimage B u.toMul).mpr hx)))

/-- The first cover conclusion in 13.8.7: the actual star image of Uα has
order two and its unique nonidentity actor is a transposition with precisely
the specified center. -/
theorem starImage_order_two (Ualpha A : Subgroup G)
    (hU : Source.starImage H Ualpha ≠ ⊥)
    (hline : Module.finrank (ZMod 2) (d.image A) = 1)
    (hc : ⁅Ualpha, Source.UH H V₃⁆ ≤ A) :
    Nat.card (Source.starImage H Ualpha) = 2 ∧
    ∃ i j : Six, i ≠ j ∧ d.image A = center i j ∧
      d.modelImage Ualpha = zpowers (Equiv.swap i j) := by
  have hdisp := d.subgroup_displacement Ualpha A hc
  refine ⟨?_, common_center_group _ (d.modelImage_ne_bot hU) _ hline hdisp⟩
  have he : Nat.card (d.modelImage Ualpha) = Nat.card (Source.starImage H Ualpha) :=
    Subgroup.card_map_of_injective d.groupEquiv.injective
  rw [← he]
  exact common_center_card_two _ (d.modelImage_ne_bot hU) _ hline hdisp

/-- The order-two source conclusion with its ambient order and disjointness
hypotheses, so no dimension assumption is required of the caller. -/
theorem starImage_order_two_of_commutator_line (Ualpha A : Subgroup G)
    (hUaH : Ualpha ≤ H) (hU : Source.starImage H Ualpha ≠ ⊥)
    (hcard : Nat.card A = 2)
    (hdisj : V₁ ⊓ A = ⊥) (hc : ⁅Source.UH H V₃, Ualpha⁆ = A) :
    Nat.card (Source.starImage H Ualpha) = 2 ∧
    ∃ i j : Six, i ≠ j ∧ d.image A = center i j ∧
      d.modelImage Ualpha = zpowers (Equiv.swap i j) := by
  have hAU : A ≤ Source.UH H V₃ := by
    rw [← hc]
    exact le_normalizer_iff_commutator_le_left.mp (hUaH.trans d.normalizes)
  apply d.starImage_order_two Ualpha A hU (d.image_finrank_of_card_two A hAU hcard hdisj)
  rw [commutator_comm, hc]

/-- The conditional final cover comparison. B* is a nontrivial subgroup of
the common-center actor; the larger W has the source commutator bound on
the actual fixed preimage. The equality of star images is a conclusion. -/
theorem starImage_comparison (Ualpha B W A : Subgroup G)
    (hBW : B ≤ W) (_hWH : W ≤ H)
    (hBU : Source.starImage H B ≤ Source.starImage H Ualpha)
    (hB : Source.starImage H B ≠ ⊥)
    (hline : Module.finrank (ZMod 2) (d.image A) = 1)
    (hUcomm : ⁅Ualpha, Source.UH H V₃⁆ ≤ A)
    (hWcomm : ⁅W, d.fixedPreimage B⁆ ≤ A) :
    Source.starImage H W = Source.starImage H B := by
  apply d.modelImage_injective
  apply subgroup_comparison _ _ (d.modelImage_mono hBW) (d.modelImage_ne_bot hB)
    (d.image A) hline
  · exact fun b hb x => d.subgroup_displacement Ualpha A hUcomm b (Subgroup.map_mono hBU hb) x
  · exact d.fixed_displacement B W A hWcomm

/-- The comparison with only the ambient order-two commutator line as
center input. This is the form used with A = V₁^g, B = V₃^g and W = V^g. -/
theorem starImage_comparison_of_commutator_line (Ualpha B W A : Subgroup G)
    (hUaH : Ualpha ≤ H) (hBW : B ≤ W) (hWH : W ≤ H)
    (hBU : Source.starImage H B ≤ Source.starImage H Ualpha)
    (hB : Source.starImage H B ≠ ⊥)
    (hcard : Nat.card A = 2) (hdisj : V₁ ⊓ A = ⊥)
    (hUcomm : ⁅Source.UH H V₃, Ualpha⁆ = A)
    (hWcomm : ⁅W, d.fixedPreimage B⁆ ≤ A) :
    Source.starImage H W = Source.starImage H B := by
  have hAU : A ≤ Source.UH H V₃ := by
    rw [← hUcomm]
    exact le_normalizer_iff_commutator_le_left.mp (hUaH.trans d.normalizes)
  apply d.starImage_comparison Ualpha B W A hBW hWH hBU hB
    (d.image_finrank_of_card_two A hAU hcard hdisj) _ hWcomm
  rw [commutator_comm, hUcomm]

end CoverCoordinates
end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverHyperplanes

end
