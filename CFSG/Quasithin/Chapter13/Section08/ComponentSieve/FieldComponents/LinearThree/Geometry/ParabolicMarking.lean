module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking.Quotients
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking.SourceRadical
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore

/-!
# Source inputs for a compatible binary parabolic marking

The actual image (L₁T)* contains the actual Sylow image T*, is proper, and
is not a two-group. Properness uses the quotient kernel inside T; the last
assertion uses the full conjugation action on V₃/V₁ and the source module.
The intrinsic PSL₃(2) construction then supplies one isomorphism marking
the Sylow image and both parabolics simultaneously.

The descendants also supply the cardinality, transitivity and faithfulness
inputs consumed by `Geometry.cyclic_seed` and `Geometry.H65_of_marking`.
The literal source R₁ is identified with O₂(L₁T) by lifting the core through
the actual action on V. Under the same marking, R₁* is the shear group R,
and the containment of 13.8.8 maps Vα* into R. These are conditional
adapters from the earlier source setup and seed-action facts; this module
does not assert Lemma 13.8.19 or the H.6.5 alternatives.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, §13.8,
printed pp.946 and 953.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
variable {G : Type*} [Group G] [Finite G]

/-- Prepare the intrinsic marking inputs from the source overgroups and
seed action. No maximality or parabolic marking is assumed here. -/
theorem source_parabolic_inputs (H L₁ M V₃ V₁ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    [(V₁.subgroupOf V₃).Normal] [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]
    (act : SourceAction H V₃ V₁)
    (hTH : (T : Subgroup G) ≤ H) (hL₁H : L₁ ≤ H)
    (hPM : L₁ ⊔ (T : Subgroup G) ≤ M) (hHM : ¬ H ≤ M)
    (hPn : L₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (a : SeedAction V₃ V₁ (L₁ ⊔ (T : Subgroup G)) hPn) :
    ∃ S : Sylow 2 (Source.Hstar H),
      (S : Subgroup (Source.Hstar H)) = Source.starImage H (T : Subgroup G) ∧
      (S : Subgroup (Source.Hstar H)) ≤ Source.starImage H (L₁ ⊔ (T : Subgroup G)) ∧
      Source.starImage H (L₁ ⊔ (T : Subgroup G)) ≠ ⊤ ∧
      ¬ IsPGroup 2 (Source.starImage H (L₁ ⊔ (T : Subgroup G))) := by
  obtain ⟨S, hS⟩ := starImage_sylow H T hTH
  refine ⟨S, hS, ?_, ?_, seed_image_not_two act a (sup_le hL₁H hTH)⟩
  · rw [hS]
    exact starImage_mono H le_sup_right
  · exact starImage_ne_top H _ M hPM hHM (kernel_le_source_parabolic H L₁ T hTH)

/-- The stronger containment in 13.8.8, Vα ≤ O₂(L₁T), transports directly
to the line two-core once the compatible parabolic marking is constructed.
This step does not replace the separate source definition of R₁. -/
theorem source_subgroup_image_le_line_core (H X Vα : Subgroup G) (hX : X ≤ H)
    (hα : Vα ≤ X.pCoreIn 2) (e : Source.Hstar H ≃* BinaryLinearThree.Group)
    (hXe : (Source.starImage H X).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL) :
    (Source.starImage H Vα).map e.toMonoidHom ≤ Matrix.PSL3Two.lineParabolicSL.pCoreIn 2 := by
  have h := Subgroup.map_mono (f := e.toMonoidHom) (starImage_mono H hα)
  rw [starImage_core H X hX, map_pCoreIn_of_injective 2 _ _ e.injective, hXe] at h
  exact h

/-- The source Sylow and the two parabolics are marked by one isomorphism.
Maximality of (L₁T)* follows from its earlier seed action and properness.
The other maximal overgroup is the point parabolic under this same marking. -/
theorem exists_source_parabolic_marking (H L₁ M V₃ V₁ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    [(V₁.subgroupOf V₃).Normal] [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]
    (act : SourceAction H V₃ V₁)
    (hTH : (T : Subgroup G) ≤ H) (hL₁H : L₁ ≤ H)
    (hPM : L₁ ⊔ (T : Subgroup G) ≤ M) (hHM : ¬ H ≤ M)
    (hPn : L₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (a : SeedAction V₃ V₁ (L₁ ⊔ (T : Subgroup G)) hPn)
    (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    IsCoatom (Source.starImage H (L₁ ⊔ (T : Subgroup G))) ∧
    ∃ (e : Source.Hstar H ≃* BinaryLinearThree.Group)
      (Q : Subgroup (Source.Hstar H)),
      (Source.starImage H (T : Subgroup G)).map e.toMonoidHom = Matrix.PSL3Two.borelSL ∧
      (Source.starImage H (L₁ ⊔ (T : Subgroup G))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL ∧
      Q.map e.toMonoidHom = Matrix.PSL3Two.pointParabolicSL ∧
      IsCoatom Q ∧ Q ≠ Source.starImage H (L₁ ⊔ (T : Subgroup G)) ∧
      Source.starImage H (T : Subgroup G) ≤ Q ∧
      Source.starImage H (L₁ ⊔ (T : Subgroup G)) ⊓ Q =
        Source.starImage H (T : Subgroup G) ∧
      ∀ X : Subgroup (Source.Hstar H), IsCoatom X →
        (Source.starImage H (T : Subgroup G) ≤ X ↔
          X = Source.starImage H (L₁ ⊔ (T : Subgroup G)) ∨ X = Q) := by
  obtain ⟨S, hS, hSP, hP, h₂⟩ :=
    source_parabolic_inputs H L₁ M V₃ V₁ T act hTH hL₁H hPM hHM hPn a
  simpa only [hS] using
    Matrix.PSL3Two.exists_compatible_parabolic_marking e₀ S _ hSP hP h₂

/-- The intrinsic source parabolic core maps to the literal shear group. -/
theorem source_core_image_eq_R (H P : Subgroup G) (hPH : P ≤ H)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group)
    (hPe : (Source.starImage H P).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL) :
    (Source.starImage H (P.pCoreIn 2)).map e.toMonoidHom = BinaryLinearThree.R := by
  rw [starImage_core H P hPH, map_pCoreIn_of_injective 2 _ _ e.injective, hPe,
    Matrix.PSL3Two.lineParabolicSL_pCoreIn_two_eq_R]

/-- The genuine stronger containment of 13.8.8 gives the required marked
containment of Vα*. -/
theorem source_subgroup_image_le_R (H P Vα : Subgroup G) (hPH : P ≤ H)
    (hα : Vα ≤ P.pCoreIn 2) (e : Source.Hstar H ≃* BinaryLinearThree.Group)
    (hPe : (Source.starImage H P).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL) :
    (Source.starImage H Vα).map e.toMonoidHom ≤ BinaryLinearThree.R := by
  rw [← source_core_image_eq_R H P hPH e hPe]
  exact Subgroup.map_mono (starImage_mono H hα)

/-- The actual R₁* is the embedded intrinsic core of the source parabolic,
and its image under any compatible marking is the specified shear group. -/
theorem sourceR1_images_of_marking (H L L₁ V V₃ V₁ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf V₃).Normal] [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]
    (hT : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hV : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G))
    (hL₁ : (pResidual 2 (sourcePointStabilizer L V₁ T)).map
      (sourcePointStabilizer L V₁ T).subtype = L₁)
    (hPn : L₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (a : SeedAction V₃ V₁ (L₁ ⊔ (T : Subgroup G)) hPn)
    (h3V : V₃ ≤ V) (hPH : L₁ ⊔ (T : Subgroup G) ≤ H)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group)
    (he : (Source.starImage H (L₁ ⊔ (T : Subgroup G))).map e.toMonoidHom =
      Matrix.PSL3Two.lineParabolicSL) :
    Source.starImage H (sourceR1 L V V₁ T hT hV) =
      (Source.starImage H (L₁ ⊔ (T : Subgroup G))).pCoreIn 2 ∧
    (Source.starImage H (sourceR1 L V V₁ T hT hV)).map e.toMonoidHom =
      BinaryLinearThree.R := by
  rw [sourceR1_eq_core_of_marking H L L₁ V V₃ V₁ T hT hV hL₁ hPn a h3V hPH e he]
  exact ⟨starImage_core H _ hPH, source_core_image_eq_R H _ hPH e he⟩

/-- The complete compatible marking required in the opening of 13.8.19.
All marks, including the other parabolic and the actual R₁*, use the same
isomorphism. The input about Vα is exactly the stronger containment in
13.8.8. The earlier source action and normalizer definitions remain explicit. -/
theorem exists_source_marking (H L L₁ M V V₃ V₁ Vα : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    [(V₁.subgroupOf V₃).Normal] [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]
    (act : SourceAction H V₃ V₁)
    (hTH : (T : Subgroup G) ≤ H) (hL₁H : L₁ ≤ H)
    (hPM : L₁ ⊔ (T : Subgroup G) ≤ M) (hHM : ¬ H ≤ M)
    (hT : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hV : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G))
    (hL₁ : (pResidual 2 (sourcePointStabilizer L V₁ T)).map
      (sourcePointStabilizer L V₁ T).subtype = L₁)
    (hPn : L₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (a : SeedAction V₃ V₁ (L₁ ⊔ (T : Subgroup G)) hPn)
    (h3V : V₃ ≤ V) (hα : Vα ≤ (L₁ ⊔ (T : Subgroup G)).pCoreIn 2)
    (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    ∃ (e : Source.Hstar H ≃* BinaryLinearThree.Group)
      (Q : Subgroup (Source.Hstar H)),
      IsCoatom (Source.starImage H (L₁ ⊔ (T : Subgroup G))) ∧
      (Source.starImage H (T : Subgroup G)).map e.toMonoidHom = Matrix.PSL3Two.borelSL ∧
      (Source.starImage H (L₁ ⊔ (T : Subgroup G))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL ∧
      Q.map e.toMonoidHom = Matrix.PSL3Two.pointParabolicSL ∧
      IsCoatom Q ∧ Q ≠ Source.starImage H (L₁ ⊔ (T : Subgroup G)) ∧
      Source.starImage H (T : Subgroup G) ≤ Q ∧
      Source.starImage H (L₁ ⊔ (T : Subgroup G)) ⊓ Q =
        Source.starImage H (T : Subgroup G) ∧
      (∀ X : Subgroup (Source.Hstar H), IsCoatom X →
        (Source.starImage H (T : Subgroup G) ≤ X ↔
          X = Source.starImage H (L₁ ⊔ (T : Subgroup G)) ∨ X = Q)) ∧
      Source.starImage H (sourceR1 L V V₁ T hT hV) =
        (Source.starImage H (L₁ ⊔ (T : Subgroup G))).pCoreIn 2 ∧
      (Source.starImage H (sourceR1 L V V₁ T hT hV)).map e.toMonoidHom =
        BinaryLinearThree.R ∧
      (Source.starImage H Vα).map e.toMonoidHom ≤ BinaryLinearThree.R := by
  obtain ⟨hP, e, Q, heT, heP, heQ, hQ, hQP, hTQ, hPQ, hmax⟩ :=
    exists_source_parabolic_marking H L₁ M V₃ V₁ T act hTH hL₁H hPM hHM hPn a e₀
  obtain ⟨hR, heR⟩ := sourceR1_images_of_marking H L L₁ V V₃ V₁ T hT hV hL₁ hPn a
    h3V (sup_le hL₁H hTH) e heP
  exact ⟨e, Q, hP, heT, heP, heQ, hQ, hQP, hTQ, hPQ, hmax, hR, heR,
    source_subgroup_image_le_R H _ Vα (sup_le hL₁H hTH) hα e heP⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
