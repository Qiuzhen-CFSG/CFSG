module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking

/-!
# The marked H.6.5 input on the source module

The earlier four-group section and its full conjugation action give a
Sylow-fixed cyclic vector whose parabolic orbit spans the two-dimensional
seed. Properness of L₁T and the actual Sylow image construct one marking
of both parabolics. The source centralizer identity makes H* faithful;
the universal earlier H.6.5 then gives its five module alternatives.
The same marking sends the literal R₁* to R and Vα* into R.

`source_H65_input` has exactly the marked-input type consumed by
`LinearThree.Hstar_not_PSL3_of_H65`. It proves that input from earlier
source facts, leaving H.6.5 itself explicit as permitted in this conditional
geometry task. The representation exclusions belong to the consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.19, printed p.953; the standing action and centralizer are on p.946.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
open ParabolicMarking
variable {G : Type*} [Group G] [Finite G]
variable (H L L₁ M V V₃ V₁ Vα : Subgroup G) (T : Sylow 2 G)
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
  (hcentralizer : ∀ h : H,
    (∀ u : Source.UH H V₃,
      QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (conjugateUH H V₃ h u) =
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) → h ∈ pCore 2 H)
  (h65 : H65Theorem (U := Additive (Source.Utilde H V₃ V₁)))

include hTH hL₁H hPM hHM hT hV hL₁ hPn a h3V hα hcentralizer h65

/-- Construct all marks and the cyclic source seed together. No marked
isomorphism, faithfulness, cyclic vector or module alternative is assumed. -/
theorem exists_source_H65_marking
    (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    ∃ (e : Source.Hstar H ≃* BinaryLinearThree.Group)
      (Q : Subgroup (Source.Hstar H)),
      H65Alternatives (act.representation.comp e.symm.toMonoidHom) ∧
      (Source.starImage H Vα).map e.toMonoidHom ≤ BinaryLinearThree.R ∧
      (Source.starImage H (T : Subgroup G)).map e.toMonoidHom = Matrix.PSL3Two.borelSL ∧
      (Source.starImage H (L₁ ⊔ (T : Subgroup G))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL ∧
      Q.map e.toMonoidHom = Matrix.PSL3Two.pointParabolicSL ∧
      IsCoatom (Source.starImage H (L₁ ⊔ (T : Subgroup G))) ∧
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
      Function.Injective act.representation ∧
      Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2 ∧
      (∃ m ∈ seedSpace H V₃ V₁, m ≠ 0 ∧
        (∀ t ∈ Source.starImage H (T : Subgroup G), act.representation t m = m) ∧
        orbitSpan act.representation ⊤ m = ⊤ ∧
        orbitSpan act.representation (Source.starImage H (L₁ ⊔ (T : Subgroup G))) m =
          seedSpace H V₃ V₁) := by
  obtain ⟨e, Q, hP, heT, heP, heQ, hQ, hQP, hTQ, hPQ, hmax, hR, heR, heα⟩ :=
    exists_source_marking H L L₁ M V V₃ V₁ Vα T act hTH hL₁H hPM hHM hT hV hL₁
      hPn a h3V hα e₀
  obtain ⟨hcard, hstable, htrans⟩ := source_seed_inputs act a (sup_le hL₁H hTH)
  have hfaith := faithful_of_source_centralizer act hcentralizer
  have hTP := starImage_mono H (show (T : Subgroup G) ≤ L₁ ⊔ (T : Subgroup G)
    from le_sup_right)
  obtain ⟨S, hS⟩ := starImage_sylow H T hTH
  have htwo : IsPGroup 2 (Source.starImage H (T : Subgroup G)) := hS ▸ S.isPGroup'
  have hclass := H65_of_marking H V₃ V₁ act hfaith h65 _ _ hTP htwo
    hcard hstable htrans e heT heP
  exact ⟨e, Q, hclass, heα, heT, heP, heQ, hP, hQ, hQP, hTQ, hPQ, hmax, hR, heR,
    hfaith, seed_finrank H V₃ V₁ hcard,
    cyclic_seed H V₃ V₁ act _ _ hTP htwo hcard hstable htrans⟩

/-- The exact input requested by `Hstar_not_PSL3_of_H65`. Both its
module alternatives and critical-subgroup bound use the constructed marking. -/
theorem source_H65_input :
    Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) →
      ∃ e : Source.Hstar H ≃* BinaryLinearThree.Group,
        H65Alternatives (act.representation.comp e.symm.toMonoidHom) ∧
        (Source.starImage H Vα).map e.toMonoidHom ≤ BinaryLinearThree.R := by
  rintro ⟨e₀⟩
  obtain ⟨e, _, hc, hα', _⟩ := exists_source_H65_marking H L L₁ M V V₃ V₁ Vα T
    act hTH hL₁H hPM hHM hT hV hL₁ hPn a h3V hα hcentralizer h65 e₀
  exact ⟨e, hc, hα'⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry
