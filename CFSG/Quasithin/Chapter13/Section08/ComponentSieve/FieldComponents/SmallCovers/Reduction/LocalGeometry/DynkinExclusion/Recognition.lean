module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Inputs
public import CFSG.Quasithin.ChapterA.Section01.Representations.HomogeneousBridge
public import Theory.Representation.BinaryOffender.SmallRatioTransport
public import Theory.Representation.Quotient

/-!
# Recognition of an invariant cubic-cover constituent

A.1.42 selects an actual homogeneous Irr⁺ subspace. All three alternatives
of F.9.18(4) are retained. The genuine triple cover rules out the hatted
natural pair, so the selected space is invariant. Its cubic polynomial
removes fixed vectors, and the component-centralizer bound makes its action
faithful. The ambient quadratic actor then restricts with no increase in
fixed codimension, and also remains faithful in the literal action image.
Only at this point is the irreducible B.4.5 input applied.

`Alternatives` is precisely the alternatives field of the accepted
`OrbitInputs` interface. The ratio fields of F.9.18(3) are unnecessary here:
the cubic polynomial makes the invariant section faithful, allowing direct
transport of the given ambient ratio bound. The general image transport
is proved as well. Neither Y = L₁,+ nor the later whole-module-or-quotient
recognition is used.

The universal B.4 input and F.9 alternatives are explicit, undischarged
earlier-result premises, not new classification theorems. Their source
producers remain with B.4 and F.9. This module proves the section passage.

Source: Aschbacher–Smith, A.1.40–42, pp.31–32; B.4.2(8), B.4.5,
pp.86–87; F.9.18(3–4), pp.325–326; 13.8.21(2), p.956.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.Recognition

universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
  (P : Sylow 2 D) (hgen : L ⊔ (P : Subgroup D) = ⊤)

/-- The complete three-way F.9.18(4) alternative on every homogeneous member
of this source module, including the hatted nonisomorphic pair. -/
def Alternatives : Prop :=
  ∀ (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ L P I),
    (⊤ ≤ subspaceStabilizer ρ I) ∨
    (orbitSpan ρ P I = I ∧ IsFFModule (imageRepresentation
      (orbitSubrepresentation ρ hI.normalizes hI.isIrrPlus hgen).toRepresentation)) ∨
    OrbitInvariance.HattedNaturalPair ρ L P I hI

omit [Finite D] [FiniteDimensional (ZMod 2) V] in
theorem alternatives_of_orbitInputs (src : OrbitInvariance.OrbitInputs ρ L P hgen) :
    Alternatives ρ L P hgen := src.alternatives

/-- Exactly the small-ratio field of the shared irreducible classification
interface. The unrelated FF ratio-one conclusion is not needed for exclusion.
This is a classification premise, not a theorem asserting its truth. -/
def SmallInput : Prop :=
  ∀ (J : Subgroup D) (_hLJ : L ≤ J)
    (W : Type v) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) J W),
    Function.Injective σ → IsIrreducible (σ.comp (L.subgroupOf J).subtype) →
    quadraticRatio σ ≤ 2 → Nonempty (ModuleRecognition.HexacodeModel (L.subgroupOf J) σ)

omit [Finite D] [L.Normal] in
theorem smallInput_of_irreducibleInputs (inputs : ModuleRecognition.IrreducibleInputs.{u,v} L) :
    SmallInput.{u,v} L := inputs.small

omit [L.Normal] in
/-- Top-subgroup transport for the universal irreducible input preserves
the actual actor, component image, and intertwining coordinates. -/
theorem model_of_irreducible (inputs : SmallInput.{u,v} L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    (hq : quadraticRatio ρ ≤ 2) : Nonempty (ModuleRecognition.HexacodeModel L ρ) := by
  let J : Subgroup D := ⊤
  let t : J ≃* D := Subgroup.topEquiv
  let τ := ρ.comp J.subtype
  have hiτ : IsIrreducible (τ.comp (L.subgroupOf J).subtype) :=
    (irreducible_comp_surjective_iff (subgroupOfEquivOfLe (show L ≤ J from le_top)).toMonoidHom
      (subgroupOfEquivOfLe (show L ≤ J from le_top)).surjective (ρ.comp L.subtype)).mpr hi
  obtain ⟨m⟩ := inputs J le_top V τ (hf.comp J.subtype_injective) hiτ
    (quadraticRatio_comp_equiv_le_two ρ t hq)
  refine ⟨{
    actor := m.actor.comp t.symm.toMonoidHom
    faithful := m.faithful.comp t.symm.injective
    component_image := ?_
    coordinates := m.coordinates
    intertwines := fun g v => m.intertwines (t.symm g) v }⟩
  rw [← Subgroup.map_map]
  have hm : L.map t.symm.toMonoidHom = L.subgroupOf J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_map, map_subgroupOf_eq_of_le (show L ≤ J from le_top)]
    change L.map (MonoidHom.id D) = L
    exact Subgroup.map_id L
  rw [hm]
  exact m.component_image

/-- Homogeneous existence, invariance, irreducibility, and faithful ratio
transport, before applying any irreducible classification to the ambient module. -/
theorem exists_section [Nontrivial V]
    (e : L ≃* HexEvenAutomorphisms)
    (hcent : centralizer (L : Set D) ≤ L)
    (z : D) (hzorder : orderOf z = 3)
    (hzcenter : zpowers z = (center L).map L.subtype)
    (hp : CubicPolynomial ρ z)
    (src : Alternatives ρ L P hgen) (hq : quadraticRatio ρ ≤ 2) :
    ∃ J : Subrepresentation ρ,
      IsIrrPlusWith ρ L P J.toSubmodule ∧
      Function.Injective J.toRepresentation ∧
      IsIrreducible (J.toRepresentation.comp L.subtype) ∧
      quadraticRatio J.toRepresentation ≤ 2 ∧
      quadraticRatio (imageRepresentation J.toRepresentation) ≤ 2 := by
  let : Theory.GroupTheory.IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : Theory.GroupTheory.IsQuasisimple L := Theory.GroupTheory.IsQuasisimple.of_mulEquiv e.symm
  have hzL : z ∈ L := by
    have hz := mem_zpowers z
    rw [hzcenter] at hz
    obtain ⟨w, _, rfl⟩ := hz
    exact w.property
  obtain ⟨I₀, hI₀⟩ := exists_isIrrPlus_of_not_fixed ρ L (by
    intro hfixed
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hp.fixed_eq_zero (hfixed Submodule.mem_top ⟨z, hzL⟩)))
  obtain ⟨I, _, hI⟩ := ChapterA.exists_chapter15_isIrrPlusWith_le_orbitSpan
    ρ (show (P : Subgroup D) ≤ normalizer (L : Set D) by
      rw [Subgroup.normalizer_eq_top]; exact le_top) P.isPGroup' hI₀
  have hPI : (P : Subgroup D) ≤ subspaceStabilizer ρ I := by
    rcases src I hI with h | ⟨h, _⟩ | h
    · exact le_top.trans h
    · rw [← h]
      exact orbitSpan_invariant ρ P I
    · exact (OrbitInvariance.not_hattedNaturalPair ρ L P e I hI h).elim
  let J := orbitSubrepresentation ρ hI.normalizes hI.isIrrPlus hgen
  have heq : J.toSubmodule = I := orbitSpan_eq_self ρ hPI
  have hn : J ≠ ⊥ := by
    intro h
    apply hI.isIrrPlus.ne_bot ρ
    rw [← heq, h]
    rfl
  have hcz : centralizer (L : Set D) ≤ zpowers z := by
    rw [hzcenter]
    intro x hx
    refine ⟨⟨x, hcent hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro l
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx l l.property
  have hf := faithful_subrepresentation_of_cubicPolynomial ρ L z hzL hzorder hcz hp J hn
  have hqJ := quadraticRatio_subrepresentation_le_two ρ J hq
  refine ⟨J, heq.symm ▸ hI, hf, ?_, hqJ, quadraticRatio_image_le_two _ hf hqJ⟩
  exact OrbitInvariance.irreducible_of_cubic ρ L z hzL hp J.toSubmodule
    (heq.symm ▸ hI.isIrrPlus)

/-- The classification is applied only to the constructed faithful section
with irreducible component restriction and its proved quadratic bound. -/
theorem exists_model [Nontrivial V]
    (e : L ≃* HexEvenAutomorphisms)
    (hcent : centralizer (L : Set D) ≤ L)
    (z : D) (hzorder : orderOf z = 3)
    (hzcenter : zpowers z = (center L).map L.subtype)
    (hp : CubicPolynomial ρ z)
    (src : Alternatives ρ L P hgen)
    (inputs : SmallInput.{u,v} L)
    (hq : quadraticRatio ρ ≤ 2) :
    ∃ J : Subrepresentation ρ,
      IsIrrPlusWith ρ L P J.toSubmodule ∧
      Nonempty (ModuleRecognition.HexacodeModel L J.toRepresentation) := by
  obtain ⟨J, hJ, hf, hi, hqJ, _⟩ := exists_section ρ L P hgen e hcent z hzorder
    hzcenter hp src hq
  exact ⟨J, hJ, model_of_irreducible J.toRepresentation L inputs hf hi hqJ⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.Recognition
