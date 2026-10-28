module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The actual quotients in the generation-one argument

The actor is `H/O₂(H)`, and the module is `U/Z`, as fixed by
`LocalQuotientAction`. The seed space below is the image of `Z_S` in that
module. Fixing it is equivalent to the ambient commutator inclusion
`[Z_S,H] ≤ Z`; it is not a hypothesis built into the action.

We also give the cardinality transfer for a split torus embedded in the
actual image of `M ∩ K₀`, where `K₀ = O²(H)`. Constructing that embedding
from the E.2.2 Borel identifications remains a separate model calculation.
The field exponent is kept distinct from the generation parameter.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.65, printed p.1152, and E.2.2, printed pp.215–216.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G]

/-- The two-residual in the ambient group; this is not `O₂(H)`. -/
noncomputable def residual (H : Subgroup G) : Subgroup G :=
  (pResidual 2 H).map H.subtype

/-- The actual image of a local subgroup in `H/O₂(H)`. -/
def actorImage (H L : Subgroup G) : Subgroup (H ⧸ pCore 2 H) :=
  (L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))

/-- `M₀*`, with `M₀ = M ∩ O²(H)`, before any Borel identification. -/
noncomputable def borelImage (H M : Subgroup G) : Subgroup (H ⧸ pCore 2 H) :=
  actorImage H (M ⊓ residual H)

theorem residual_le (H : Subgroup G) : residual H ≤ H := map_subtype_le _

/-- The literal quotient image of the seed; taking its linear span is harmless
because the seed is a binary subgroup in all applications. -/
def seedSpace {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (_a : LocalQuotientAction H U Z) (ZS : Subgroup G) :
    Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) :=
  Submodule.span (ZMod 2) {v | ∃ z : U, (z : G) ∈ ZS ∧
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) z) = v}

/-- Fixation in the representation means centralization modulo the actual Z. -/
theorem seedSpace_le_fixedSpace_iff
    {H U Z ZS : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (hZU : ZS ≤ U) :
    seedSpace a ZS ≤ fixedSpace a.representation ⊤ ↔ ⁅ZS, H⁆ ≤ Z := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  constructor
  · intro h h₁ hh z hz
    let zU : U := ⟨z, hZU hz⟩
    have hv := h (Submodule.subset_span
      (show Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) zU) ∈
          {v | ∃ z : U, (z : G) ∈ ZS ∧
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) z) = v} from
        ⟨zU, hz, rfl⟩))
      ⟨QuotientGroup.mk' (pCore 2 H) ⟨h₁, hh⟩, mem_top _⟩
    change a.representation (QuotientGroup.mk' (pCore 2 H) ⟨h₁, hh⟩)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) zU)) = _ at hv
    rw [a.conjugation] at hv
    have he := congrArg Additive.toMul hv
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    change h₁ * z * h₁⁻¹ / z ∈ Z at hm
    simpa only [div_eq_mul_inv, commutatorElement_def] using hm
  · intro h
    apply Submodule.span_le.mpr
    rintro v ⟨z, hz, rfl⟩ ⟨hq, _⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) hq
    change a.representation (QuotientGroup.mk' (pCore 2 H) g)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) z)) = _
    rw [a.conjugation]
    apply congrArg Additive.ofMul
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (g : G) * z * (g : G)⁻¹ / z ∈ Z
    simpa only [div_eq_mul_inv, commutatorElement_def] using h g g.property z hz

/-- Orders of actual quotient images divide the order of the subgroup upstairs. -/
theorem card_actorImage_dvd {H L : Subgroup G} (hLH : L ≤ H) :
    Nat.card (actorImage H L) ∣ Nat.card L := by
  have h := (L.subgroupOf H).card_map_dvd (QuotientGroup.mk' (pCore 2 H))
  rwa [Nat.card_congr (subgroupOfEquivOfLe hLH).toEquiv] at h

/-- A split torus in the actual Borel image supplies the needed divisor.
The injective homomorphism must come from a genuine model identification. -/
theorem torus_dvd_intersection
    {F : Type*} [Field F] [Finite F] {H M : Subgroup G} {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (ι : Fˣ →* borelImage H M)
    (hι : Function.Injective ι) :
    2 ^ f - 1 ∣ Nat.card (M ⊓ H : Subgroup G) := by
  have htorus : 2 ^ f - 1 ∣ Nat.card (borelImage H M) := by
    simpa only [Nat.card_units, hF] using card_dvd_of_injective ι hι
  exact htorus.trans ((card_actorImage_dvd (inf_le_right.trans (residual_le H))).trans
    (card_dvd_of_le (inf_le_inf_left M (residual_le H))))

/-- The 3-prime intersection forces odd field exponent once the model torus
has been constructed. No equality with `generationParameter H` is used here. -/
theorem odd_field_exponent_of_borel_torus
    {F : Type*} [Field F] [Finite F] {H M : Subgroup G} {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (ι : Fˣ →* borelImage H M)
    (hι : Function.Injective ι) (hthree : ¬ 3 ∣ Nat.card (M ⊓ H : Subgroup G)) :
    Odd f :=
  odd_field_exponent_of_three_prime_intersection hthree
    (torus_dvd_intersection hF ι hι)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
