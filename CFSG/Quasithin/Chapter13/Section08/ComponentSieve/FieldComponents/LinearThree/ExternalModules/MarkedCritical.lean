module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.SectionTransfer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.PointRadical
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The marked critical-pair tensor argument: established transfers

Equality of fixed codimensions lifts section fixed vectors. The actual source
centralizer can then be used, after a separate group-theoretic lift, to obtain
a line-valued section displacement from the conjugate of 13.7.3(7).

The point radical has rank two and is quadratic on the natural tensor module,
while fixing the marked seed. Thus the tensor identification and quadraticity
alone do not give the required rank bound. The proper marked pair is excluded
below by the fixed-space separation; the saturated case is exported by the
`SaturatedPair` descendant. No unconditional tensor exclusion is asserted by
this module.

Source: Aschbacher–Smith 13.8.21(1), printed p.957, with 13.7.3(7),
13.8.8–11, 13.8.18 and F.9.13–16 (manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve
open FieldComponents.LinearThree FieldComponents.LinearThree.ExternalModules
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical

open TensorFacts

variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-!
The proper marked critical pair is incompatible with a natural tensor chief
section. The source critical comparison produces a binary line containing
every displacement from the marked source actor. Transporting that line
through the actual chief-section equivalence gives a line in `TensorSpace`,
where the concrete proper-radical calculation produces a displacement outside
it. The two marked images are retained separately: the fixed actor is a
nontrivial proper subgroup `R` of the point radical, while the moving actor is
the full point radical.

This is the source-compatible local deduction used in Aschbacher–Smith
13.8.21(1), printed p.957. All critical denominators, relative normalizers,
and the actual source action remain explicit inputs; no faithfulness or
quadraticity transfer is inferred from the chief section.
-/
theorem source_proper_pair_false [Finite G]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    (act : SourceAction H V₃ V₁)
    (eH : Source.Hstar H ≃* TensorGroup)
    (L N : Subrepresentation act.representation)
    (hchief : IsNaturalTensorChiefSection act.representation eH L N)
    (A B Z : Subgroup G) (R : Subgroup TensorGroup)
    (hAH : A ≤ H)
    (hindex : (Source.DH (Source.UH H V₃) A Z).relIndex (Source.UH H V₃) = 2)
    (hnZ : Source.UH H V₃ ≤ normalizer (Z : Set G))
    (hnV : Source.UH H V₃ ≤ normalizer (V₁ : Set G))
    (hmoved : ¬ ⁅Source.UH H V₃, A⁆ ≤ Z ⊔ V₁)
    (hdis : Disjoint V₁ Z)
    (hsmall : fixedCodim act.representation (Source.starImage H A) ≤ 2)
    (hbound : ⁅Source.UH H V₃ ⊓ centralizer (A : Set G), B⁆ ≤ Z)
    (hZ : Nat.card Z = 2)
    (hAmark : (Source.starImage H A).map eH.toMonoidHom = R)
    (hAproper : R < tensorPointRadical)
    (hA0 : R ≠ ⊥)
    (hBmark : (Source.starImage H B).map eH.toMonoidHom = tensorPointRadical) : False := by
  obtain ⟨_, ⟨e⟩⟩ := hchief
  have he (c : Source.Hstar H) (v) :
      e.toLinearEquiv (sectionRepresentation act.representation L N c v) =
        naturalTensor (eH c) (e.toLinearEquiv v) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap c v
  have he' (c : Source.Hstar H) (v) :
      e.toLinearEquiv (sectionRepresentation act.representation L N c v) =
        naturalTensor (eH.toMonoidHom c) (e.toLinearEquiv v) := by
    change e.toLinearEquiv (sectionRepresentation act.representation L N c v) =
      naturalTensor (eH c) (e.toLinearEquiv v)
    exact he c v
  have hsection : fixedCodim (sectionRepresentation act.representation L N)
      (Source.starImage H A) = 2 := by
    rw [Representation.BinaryOffender.fixedCodim_map_equivariant
      (sectionRepresentation act.representation L N) naturalTensor eH.toMonoidHom
      e.toLinearEquiv he', hAmark]
    exact fixedCodim_proper_radical R hAproper hA0
  obtain ⟨D, hDdim, hdisp⟩ := exists_section_displacement_line H V₃ V₁ act L N A B Z
    hAH hindex hnZ hnV hmoved hdis hsmall hsection hbound hZ
  let D' := D.map e.toLinearEquiv.toLinearMap
  have hD'dim : Module.finrank (ZMod 2) D' ≤ 1 :=
    (Submodule.finrank_map_le e.toLinearEquiv.toLinearMap D).trans hDdim
  obtain ⟨b, hb, w, hw, hnot⟩ := exists_radical_displacement_not_mem R hAproper hA0 D' hD'dim
  have hbmap : b ∈ (Source.starImage H B).map eH.toMonoidHom := by
    rw [hBmark]
    exact hb
  obtain ⟨b', hb', hb'eq⟩ := Subgroup.mem_map.mp hbmap
  obtain ⟨w', hw'eq⟩ := e.toLinearEquiv.surjective w
  have hw' : w' ∈ fixedSpace (sectionRepresentation act.representation L N)
      (Source.starImage H A) := by
    intro a
    apply e.toLinearEquiv.injective
    change e.toLinearEquiv (sectionRepresentation act.representation L N (a : Source.Hstar H) w') =
      e.toLinearEquiv w'
    rw [he', hw'eq]
    exact hw ⟨eH.toMonoidHom a.val,
      hAmark ▸ Subgroup.mem_map_of_mem eH.toMonoidHom a.property⟩
  have hd := hdisp b' hb' w' hw'
  have hdm : e.toLinearEquiv (sectionRepresentation act.representation L N b' w' - w') ∈ D' := by
    exact ⟨_, hd, rfl⟩
  have heqdisp : e.toLinearEquiv (sectionRepresentation act.representation L N b' w' - w') =
      naturalTensor b w - w := by
    rw [map_sub, he', hw'eq]
    change naturalTensor (eH.toMonoidHom b') w - w = _
    rw [hb'eq]
  have hdm' : naturalTensor b w - w ∈ D' := by
    rw [← heqdisp]
    exact hdm
  exact hnot hdm'

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical
