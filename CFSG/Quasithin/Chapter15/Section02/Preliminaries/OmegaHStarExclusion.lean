module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaFullComplete

/-!
# The Omega rank contradiction at the start of15.2.4

For the original H∈H*(T,M), put X=O²(H∩M). The prepared chosen module
supplies X≤C_M(V), exactly15.1.9(4). The imported literal star-rank
bound from `OmegaCentralizerRank` then excludes an isomorphism X* ≃ E₉;
this module only supplies that model-facing adapter.

This consumes the original intersection residual and literal quotient map.
In the wreath case, E.2.2 is the independent producer of the prohibited
E₉ model. The result here discharges the Omega contradiction in the first
paragraph of15.2.4; the remaining non-Omega wreath argument is separate.

Source: Aschbacher--Smith15.2.4, printed pp.1105--1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The actual H* intersection residual cannot have the E₉ star model in
an Omega row; the preceding chosen-module noncentrality remains explicit. -/
theorem source_omega_HStar_star_residual_not_nine
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let X := (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype
    ¬ Nonempty (((X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) ≃*
      Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :=
by
  let X := (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype
  let A := (X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
  have hr : primeRank 3 A ≤ 1 :=
    source_omega_HStar_intersection_star_rank hG T hM hu hV ho hRc hH
  change ¬ Nonempty (A ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
  rintro ⟨e⟩
  have hcube : ∀ z : Multiplicative (ZMod 3) × Multiplicative (ZMod 3), z ^ 3 = 1 := by
    decide +kernel
  have hcard : Nat.card (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) = 3 ^ 2 := by simp
  have hlarge := primeRank_ge_of_elementary_embedding hcube hcard e.symm.toMonoidHom e.symm.injective
  change 2 ≤ primeRank 3 A at hlarge
  omega

/-- The full-module15.2.4 Omega contradiction, with source noncentrality discharged. -/
theorem source_omega_full_HStar_star_residual_not_nine
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc H : Subgroup G} [IsElementaryAbelian 2 (localModule T M)]
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M (localModule T M))
    (ho : SourceCases.Omega (imageRepresentation M (localModule T M) hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let X := (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype
    ¬ Nonempty (((X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) ≃*
      Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :=
  source_omega_HStar_star_residual_not_nine hG T hM.1 hu hV ho
    (source_omega_full_core_noncentral hG T hempty hM hu hmany ho) hH

end CFSG.Quasithin.Chapter15.Section02
end
