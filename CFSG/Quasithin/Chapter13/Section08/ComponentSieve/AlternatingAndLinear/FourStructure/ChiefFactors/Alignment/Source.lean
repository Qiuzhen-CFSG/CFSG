module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed

/-!
# The marked odd subgroup on the literal source seed

Passing to H/O₂(H) preserves whether a subgroup of H is a two-group: the
kernel is already a two-group. In particular the source quotient
L₀/O₂(L₀) of order three guarantees that L₀* is not a two-group.

The action agrees with conjugation on representatives. Consequently an
ambient subgroup centralizing V₃ fixes its image Ṽ₃ in the literal quotient
U_H/V₁. These two statements supply the marked-subgroup hypotheses in the
orientation argument without assuming any conclusion about the heads.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, notation
in §13.2 and the argument in 13.8.25, printed pp.960–961.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
open Subgroup
open scoped commutatorElement
open scoped IsMulCommutative
variable {G : Type*} [Group G]

theorem starImage_isPGroup_iff (H R : Subgroup G) (hRH : R ≤ H) :
    IsPGroup 2 (Source.starImage H R) ↔ IsPGroup 2 R := by
  constructor
  · intro h
    have hk : IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    have hpre := h.comap_of_ker_isPGroup (QuotientGroup.mk' (pCore 2 H)) hk
    have hsub : IsPGroup 2 (R.subgroupOf H) := hpre.to_le (by
      intro r hr
      exact Subgroup.mem_map_of_mem _ hr)
    exact hsub.of_equiv (Subgroup.subgroupOfEquivOfLe hRH)
  · intro h
    exact (h.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm).map _

theorem starImage_not_two_of_cubic_quotient [Finite G]
    (H R : Subgroup G) (hRH : R ≤ H) (hthree : Nat.card (R ⧸ pCore 2 R) = 3) :
    ¬ IsPGroup 2 (Source.starImage H R) := by
  intro h
  have hR := (starImage_isPGroup_iff H R hRH).mp h
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (hR.to_quotient (pCore 2 R)).exists_card_eq
  have hd : 3 ∣ 2 ^ n := by rw [← hn, hthree]
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

variable (H V₃ V₁ R : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

theorem sourceSeed_fixed_of_centralizes
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) (hR : R ≤ centralizer (V₃ : Set G)) :
    ∀ g ∈ Source.starImage H R, ∀ v ∈ sourceSeedSpace H V₃ V₁, ρ g v = v := by
  rintro g ⟨r, hr, rfl⟩ v ⟨u, hu, rfl⟩
  change ρ (QuotientGroup.mk' (pCore 2 H) r)
      (Additive.ofMul (sourceProjection H V₃ V₁ u)) =
    Additive.ofMul (sourceProjection H V₃ V₁ u)
  have hconj : sourceConjugate H V₃ r u = u := by
    apply Subtype.ext
    change (r : G) * u * (r : G)⁻¹ = u
    have hc := Subgroup.mem_centralizer_iff.mp (hR hr) u hu
    calc
      (r : G) * u * (r : G)⁻¹ = (u : G) * r * (r : G)⁻¹ :=
        congrArg (fun x : G => x * (r : G)⁻¹) hc.symm
      _ = u := by group
  rw [hρ, hconj]


/-- Fixation on the source seed only requires centralization modulo V₁.
Normality is required inside U_H, not inside the ambient group. -/
theorem sourceSeed_fixed_of_commutator_le
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) (hR : ⁅R, V₃⁆ ≤ V₁) :
    ∀ g ∈ Source.starImage H R, ∀ v ∈ sourceSeedSpace H V₃ V₁, ρ g v = v := by
  rintro g ⟨r, hr, rfl⟩ v ⟨u, hu, rfl⟩
  change ρ (QuotientGroup.mk' (pCore 2 H) r)
      (Additive.ofMul (sourceProjection H V₃ V₁ u)) =
    Additive.ofMul (sourceProjection H V₃ V₁ u)
  rw [hρ]
  have he : sourceProjection H V₃ V₁ (sourceConjugate H V₃ r u) =
      sourceProjection H V₃ V₁ u := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (r : G) * (u : G) * (r : G)⁻¹ / (u : G) ∈ V₁
    rw [div_eq_mul_inv, ← commutatorElement_def]
    exact (commutator_le.mp hR) r hr u hu
  exact congrArg Additive.ofMul he

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
