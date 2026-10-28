module
public import CFSG.Quasithin.Chapter14.Section06.SourceOmegaCoreQuotient
public import Theory.GroupTheory.IrreducibleCenterSeed

/-!
# The normal omega-core overgroup contains the paired irreducible section

The original local hypotheses already establish characteristic two after
quotienting by Ω₁Z(O₂(H)), and put the image of the Sylow omega-center in
the quotient-core omega-center. The finite center-seed argument now
places an irreducible section E/Z₀ in the preimage of that normal subgroup.

In 14.6.9 the model produces S = T₀, B = I ∩ Mc and E = E₁E₂. The
remaining model premises are the literal center bound in S/Z₀ and the
irreducible action on E/Z₀; no quotient characteristic or seed-existence
premise remains. The conclusion is the containment E₀ ≤ F needed in (k).

Source: Aschbacher--Smith, 14.6.9(j)--(k), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

attribute [local instance] omegaCore_normal

/-- Apply the original omega-core quotient to the paired section with
its literal Sylow subgroup and central denominator. -/
theorem source_omegaCore_quotient_contains_irreducible_section
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {H : Subgroup G} (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G))
    (S B E Z₀ : Subgroup H)
    (hST : S ≤ (T.subtype hH.2 : Subgroup H))
    (hSnormal : (S.subgroupOf (T.subtype hH.2 : Subgroup H)).Normal)
    (hES : E ≤ S) (hZS : omegaOneCenterAmbient (pCore 2 H) ≤ S)
    (hZ₀Z : Z₀ ≤ omegaOneCenterAmbient (pCore 2 H))
    [(Z₀.subgroupOf S).Normal]
    (hE : B ≤ normalizer (E : Set H))
    (hirr : IsIrreducibleSection B Z₀ E)
    (hcenter : ((center (S ⧸ Z₀.subgroupOf S)).comap
      (QuotientGroup.mk' (Z₀.subgroupOf S))).map S.subtype ≤ E) :
    let Z1 := omegaOneCenterAmbient (pCore 2 H)
    E ≤ (omegaOneCenterAmbient (pCore 2 (H ⧸ Z1))).comap (QuotientGroup.mk' Z1) := by
  dsimp only
  let Z1 := omegaOneCenterAmbient (pCore 2 H)
  let q := QuotientGroup.mk' Z1
  let F := (omegaOneCenterAmbient (pCore 2 (H ⧸ Z1))).comap q
  obtain ⟨_,himage,hseed⟩ := source_omegaCore_quotient_characteristicTwo hG T hempty hH hHZ
  apply irreducible_section_le_normal_of_omega_quotient
    (T.subtype hH.2 : Subgroup H) S B E Z₀ Z1 F
    (T.subtype hH.2).isPGroup' hST hSnormal hES hZS hZ₀Z hE hirr hcenter
  · exact QuotientGroup.le_comap_mk' Z1 _
  · change omegaOneCenterAmbient ((T.subtype hH.2 : Subgroup H).map q) ≤
      ((omegaOneCenterAmbient (pCore 2 (H ⧸ Z1))).comap q).map q
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z1),himage]
    exact hseed
end CFSG.Quasithin.Chapter14.Section06
