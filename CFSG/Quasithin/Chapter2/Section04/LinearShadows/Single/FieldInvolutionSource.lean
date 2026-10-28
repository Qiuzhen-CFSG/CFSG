module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionRootSource

/-!
# Original field-involution coset fusion

The actual field involution has square-root fixed subgroups on O₂(H) and
R/O₂(H). The elementary-layer cocycle argument now proves that all involutions
in its R-coset are conjugate by R, with no additional fixed-count or model
premise. All subgroup and quotient maps are those of the original setup.

Source: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532; used by 2.4.21(2).
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Original 2.4.12(2): every involution in the field-involution coset
is conjugate to that involution by an element of the actual Thompson subgroup. -/
theorem source_field_involution_coset_fusion
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∀ v ∈ T, orderOf v = 2 → v * s⁻¹ ∈ R → ∃ r ∈ R, r * s * r⁻¹ = v :=
  source_field_involution_coset_fusion_of_fixed_cards d hG T hST hsingle hL hM hTM hunique c s hs hs2
    (source_field_involution_core_fixed_card d hG T hST hsingle hL hM hTM hunique c s hs hs2)
    (source_field_involution_sylow_quotient_fixed_card d hG T hST hsingle hL hM hTM hunique c s hs hs2)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
