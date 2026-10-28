module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Action
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PCoreImage


/-!
# Residuals, cores and actors in the literal star quotient

The two-core comparison uses the actual two-group kernel of H → H/O₂(H).
Surjective-image functoriality also carries O²(B₀) to O²(B₀*), rather than
to the two-core. Finally the source actor's two-perfectness and its
three-group quotient above O₂ pass to its literal star image, yielding
the required two-and-three cardinality formula.

These are transport steps in Aschbacher–Smith 13.8.16, printed pp.952–953
(combined manuscript of 1 March 2004).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

omit [Finite G] [Finite D] in
theorem three_quotient_of_surjective (f : G →* D) (hf : Function.Surjective f)
    (hq : IsPGroup 3 (G ⧸ pCore 2 G)) : IsPGroup 3 (D ⧸ pCore 2 D) := by
  have hmap : (pCore 2 G).map f ≤ pCore 2 D := by
    exact le_sSup ⟨(inferInstance : (pCore 2 G).Normal).map f hf, pCore_isPGroup.map f⟩
  let q := QuotientGroup.map (pCore 2 G) (pCore 2 D) f (map_le_iff_le_comap.mp hmap)
  exact hq.of_surjective q (QuotientGroup.map_surjective_of_surjective _ _ f
    (QuotientGroup.mk_surjective.comp hf) (map_le_iff_le_comap.mp hmap))

variable (H B : Subgroup G)

omit [Finite G] in
theorem starImage_normalizes (A : Subgroup G) (hn : A ≤ normalizer (B : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H B : Set (Source.Hstar H)) := by
  apply (map_mono (show A.subgroupOf H ≤ normalizer (B.subgroupOf H : Set H) from ?_)).trans
    (le_normalizer_map _)
  apply le_normalizer_iff.mpr
  intro a ha b hb
  exact le_normalizer_iff.mp hn a ha b hb

omit [Finite G] in
private theorem core_subgroupOf (hBH : B ≤ H) :
    (B.pCoreIn 2).subgroupOf H = (B.subgroupOf H).pCoreIn 2 := by
  apply map_injective H.subtype_injective
  rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBH),
    map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hBH]

theorem starImage_twoCore (hBH : B ≤ H) :
    Source.starImage H (B.pCoreIn 2) = (Source.starImage H B).pCoreIn 2 := by
  rw [Source.starImage, core_subgroupOf H B hBH]
  apply map_pCoreIn_of_ker_isPGroup
  change IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup

theorem starImage_twoResidual (hBH : B ≤ H) :
    Source.starImage H ((pResidual 2 B).map B.subtype) =
      (pResidual 2 (Source.starImage H B)).map (Source.starImage H B).subtype := by
  have he : ((pResidual 2 B).map B.subtype).subgroupOf H =
      (pResidual 2 (B.subgroupOf H)).map (B.subgroupOf H).subtype := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hBH),
      map_embedded_pResidual, map_subgroupOf_eq_of_le hBH]
  rw [Source.starImage, he, map_embedded_pResidual]
  rfl

omit [Finite G] in
theorem starImage_twoPerfect (hBH : B ≤ H) (hp : IsPPerfect 2 B) :
    IsPPerfect 2 (Source.starImage H B) := by
  let e := (subgroupOfEquivOfLe hBH).symm
  have hp' := hp.of_surjective e.toMonoidHom e.surjective
  exact hp'.of_surjective ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (B.subgroupOf H))
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective (B.subgroupOf H))

omit [Finite G] in
theorem starImage_three_quotient (hBH : B ≤ H)
    (hq : IsPGroup 3 (B ⧸ pCore 2 B)) :
    IsPGroup 3 (Source.starImage H B ⧸ pCore 2 (Source.starImage H B)) := by
  let e := (subgroupOfEquivOfLe hBH).symm
  have hq' := three_quotient_of_surjective e.toMonoidHom e.surjective hq
  exact three_quotient_of_surjective
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (B.subgroupOf H))
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective (B.subgroupOf H)) hq'

theorem starImage_card (hBH : B ≤ H) (hq : IsPGroup 3 (B ⧸ pCore 2 B)) :
    ∃ r s : ℕ, Nat.card (Source.starImage H B) = 2 ^ r * 3 ^ s :=
  card_two_three (starImage_three_quotient H B hBH hq)

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
