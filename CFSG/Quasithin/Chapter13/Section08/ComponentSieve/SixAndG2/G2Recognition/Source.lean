module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.Constituent
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.CentralSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceG2Exclusion
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer

/-!
# The literal derived-G₂ section in the original 13.8.27 argument

From the surviving quotient K/O₂(K) ≅ G₂(2)′ and the earlier source
component, orbit and critical-pair data, the no-strong-FF and no-transvection
arguments make the whole original U_H/V₁ the unique noncentral Irr⁺ member.
Recognition on its quotient by component-fixed vectors constructs both an
intrinsic marking and the natural intertwiner on `ComponentSection` itself.
Neither the natural quotient nor its marking is an input.

The final two theorems apply this recognition to the existing natural/Weyl
cover comparison and to the literal source filtration. The independent
parabolic bounds remain explicit in the latter application. The earlier
field/component/geometry inputs are discharged by the 13.8.27 assembly owner;
this module proves the conditional recognition branch, not the full dichotomy.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.27,
printed p.963 (PDF p.980), using 13.8.21–22 and B.4.2/B.4.5.
The concrete octonion model retains the attribution in LICENSES/ATLAS.txt.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open CriticalGeometry
open AlternatingAndLinear.FourStructure.CriticalTransfer
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

variable {G : Type*} [Group G] [Finite G] {L T H V V₃ V₁ K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Earlier source inputs to the G₂ branch of 13.8.27. The component marking,
 critical pair, relative indices, quotient action and all F.9.18 alternatives
 are literal. Section recognition and constituent uniqueness are conclusions. -/
structure SourceHypotheses
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (c : CriticalPair L T H V) where
  seed_le : V₃ ≤ H
  line_le : V₁ ≤ Source.UH H V₃
  line_card : Nat.card V₁ = 2
  line_central : H ≤ centralizer (V₁ : Set G)
  component_le : K ≤ H
  component : (K.subgroupOf H).IsCComponent
  model : Nonempty ((K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)))
  fitting : generalizedFitting (Source.Hstar H) = Source.starImage H K
  conjugates : IsConjugation H V₃ V₁ ρ
  centralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H
  generated : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆
  sylow : Sylow 2 (Source.Hstar H)
  sylow_generation : Source.starImage H K ⊔ (sylow : Subgroup (Source.Hstar H)) = ⊤
  orbit : letI : (Source.starImage H K).Normal := fitting ▸ inferInstance
    OrbitInputs ρ (Source.starImage H K) sylow sylow_generation
  forward : c.Ugamma V₃ ≤ H
  reverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom
  elementary : IsElementaryTwo (Source.starImage H (c.Ugamma V₃))
  quadratic : IsQuadratic ρ (Source.starImage H (c.Ugamma V₃))
  bound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
    2 * rank (Source.starImage H (c.Ugamma V₃))
  critical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
      (Source.UH H V₃)) ≤
    Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃))

variable (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (c : CriticalPair L T H V) (d : SourceHypotheses (K := K) ρ c)

/-- The canonical source projection, with its actual conjugation identity. -/
def sourceSection : ConjugationSection H (Source.UH H V₃) V₁ ρ where
  le := conjugateSpanBy_le_self d.seed_le
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  centralizes := d.line_central
  line_le := d.line_le
  quotient := {
    toFun := fun u => Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  surjective := QuotientGroup.mk'_surjective _
  kernel := QuotientGroup.ker_mk' _
  conjugates := d.conjugates

private theorem model_properties {D : Type*} [Group D]
    (e : D ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    IsQuasisimple D ∧ center D = ⊥ := by
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : IsSimpleGroup D := e.isSimpleGroup
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center D = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D) inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp h))
  exact ⟨⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩, hz⟩

private theorem source_component_properties
    (d : SourceHypotheses (K := K) ρ c) :
    IsQuasisimple (Source.starImage H K) ∧
    centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥ := by
  obtain ⟨e⟩ := d.model
  have he := model_properties ((Components.componentStarEquiv H K d.component_le d.component).symm.trans e)
  refine ⟨he.1, bot_unique ?_⟩
  intro x hx
  have hxL : x ∈ Source.starImage H K := by
    rw [← d.fitting] at hx ⊢
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hx
  have hz : (⟨x, hxL⟩ : Source.starImage H K) ∈ center (Source.starImage H K) := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp hx l l.property)
  rw [he.2, mem_bot] at hz
  exact congrArg Subtype.val hz

include d

/-- Derive the unique noncentral constituent on the original quotient from the
 literal critical-pair inequality and the complete earlier orbit alternatives. -/
theorem source_isIrrPlus : IsIrrPlus ρ (Source.starImage H K) ⊤ := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  let : (Source.starImage H K).Normal := d.fitting ▸ inferInstance
  obtain ⟨hq, hc⟩ := source_component_properties ρ c d
  let := hq
  obtain ⟨e⟩ := d.model
  let eL := (Components.componentStarEquiv H K d.component_le d.component).symm.trans e
  have hf := faithful_of_centralizer_le_core ρ d.conjugates d.centralizer
  have hgen : subspaceCommutator ρ ⊤ (Source.starImage H K) = ⊤ :=
    (commutatorImage_eq_subspaceCommutator K d.component_le ρ d.conjugates).symm.trans
      (commutatorImage_eq_top d.generated)
  let s := sourceSection ρ c d
  obtain ⟨hdim, hline, hcomm, _⟩ := critical_pair_linear_bounds s (c.gb : G)
    d.forward d.reverse d.line_card hf d.critical
  let B := s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))
  let S := s.image (c.Aone V₁)
  have hcrit : B ≤ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)) ∨
      ∃ S : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)),
        IsAtom S ∧ ∀ a ∈ Source.starImage H (c.Ugamma V₃), ∀ v ∈ B, ρ a v - v ∈ S := by
    by_cases hz : S = ⊥
    · left
      intro v hv a
      have hh := hcomm a a.property v hv
      change ρ a v - v ∈ S at hh
      rw [hz] at hh
      exact sub_eq_zero.mp hh
    · right
      refine ⟨S, Submodule.isAtom_iff_finrank_eq_one.mpr ?_, hcomm⟩
      have hn : Module.finrank (ZMod 2) S ≠ 0 := fun hh => hz (Submodule.finrank_eq_zero.mp hh)
      change Module.finrank (ZMod 2) S ≤ 1 at hline
      omega
  exact whole_isIrrPlus ρ (Source.starImage H K) hf hc eL hgen d.sylow d.sylow_generation
    d.orbit _ d.elementary B hcrit hdim

/-- Recognize the literal commutator image modulo its component-fixed vectors.
 The intrinsic marking is constructed together with the natural intertwiner. -/
theorem section_model :
    ∃ eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)),
      HasSectionModel H V₃ V₁ ρ K d.component_le
        (Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2)) eK := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  let : (Source.starImage H K).Normal := d.fitting ▸ inferInstance
  obtain ⟨hq, hc⟩ := source_component_properties ρ c d
  let := hq
  obtain ⟨e⟩ := d.model
  let j := Components.componentStarEquiv H K d.component_le d.component
  let eL := j.symm.trans e
  have htop : commutatorImage H V₃ V₁ K = ⊤ := commutatorImage_eq_top d.generated
  let I : Subrepresentation ρ := ⟨commutatorImage H V₃ V₁ K, by
    intro g v hv
    rw [htop]
    trivial⟩
  have hI : IsIrrPlus ρ (Source.starImage H K) I.toSubmodule := by
    change IsIrrPlus ρ (Source.starImage H K) (commutatorImage H V₃ V₁ K)
    rw [htop]
    exact source_isIrrPlus ρ c d
  obtain ⟨e', f, hf⟩ := central_section_natural ρ (Source.starImage H K) hc eL I hI
    _ d.elementary d.quadratic d.bound
  refine ⟨j.trans e', commutatorImage_invariant K d.component_le ρ d.conjugates, f, ?_⟩
  intro k u
  let a := j (QuotientGroup.mk' (pCore 2 K) k)
  have ha : (a : Source.Hstar H) = QuotientGroup.mk' (pCore 2 H) (inclusion d.component_le k) :=
    Components.componentStarEquiv_mk H K d.component_le d.component k
  have hh := hf a (Submodule.Quotient.mk u)
  change f (Submodule.Quotient.mk
    (I.toRepresentation (a : Source.Hstar H) u)) = _ at hh
  change f (Submodule.Quotient.mk
    ⟨ρ (a : Source.Hstar H) u, I.apply_mem_toSubmodule a u.property⟩) = _ at hh
  have he : e' a = (j.trans e') (QuotientGroup.mk' (pCore 2 K) k) := rfl
  rw [he] at hh
  convert hh using 1
  · congr 2
  · rfl

/-- Uniqueness concerns the actual Irr⁺ family, not an unconnected module label. -/
theorem unique_constituent
    (I : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)))
    (hI : IsIrrPlus ρ (Source.starImage H K) I) : I = ⊤ :=
  hI.eq_of_le ρ (source_isIrrPlus ρ c d) le_top

/-- Apply the existing Weyl-cover comparison to the newly recognized literal section. -/
theorem source_natural_or_weyl :
    ∃ eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)),
      (∃ E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2),
        ∀ a v, E (ρ (modelActor d.component_le d.component eK a) v) =
          Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2) a (E v)) ∨
      (∃ E : Atlas.G2.Natural.TraceZero (ZMod 2) ≃ₗ[ZMod 2] Additive (Source.Utilde H V₃ V₁),
        ∀ a w, E (Atlas.G2.Natural.OrthogonalCover.binaryAction (ZMod 2) a w) =
          ρ (modelActor d.component_le d.component eK a) (E w)) := by
  obtain ⟨eK, hs⟩ := section_model ρ c d
  obtain ⟨_, _, hnat | hweyl⟩ := SourceG2Cover.natural_or_weyl_of_section
    d.component_le d.component ρ d.conjugates d.generated eK hs
  · exact ⟨eK, Or.inl ⟨hnat.choose, hnat.choose_spec.1⟩⟩
  · exact ⟨eK, Or.inr ⟨hweyl.choose, hweyl.choose_spec.1⟩⟩

/-- Concrete application to the original source filtration. Recognition is
 discharged; the independent parabolic estimates remain with their producer. -/
theorem source_exclusion
    [IsElementaryAbelian 2 (Source.VH H V)]
    [((Source.UH H V₃).subgroupOf H).Normal]
    (hV : V ≤ H) (hV₃ : V₃ ≤ V)
    (hDC : ¬ Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ≤ Source.HC H V₃)
    (ha : 2 ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hm : 3 ≤ rank
      (((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.VH H V).subgroupOf H).map
        (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H))))
    (hb : 3 ≤ rank (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.UH H V₃)) :
    False := by
  obtain ⟨eK, hs⟩ := section_model ρ c d
  exact SourceG2Exclusion.source_exclusion_of_section c hV hV₃ d.line_le d.line_card
    d.line_central d.component_le d.component ρ d.conjugates d.centralizer d.generated
    eK hs d.forward hDC ha hm hb

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition

end
