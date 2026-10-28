module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SevenGeometry
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneImage
public import Theory.Representation.BinaryPermutation.SevenTriangle.Marking
/-!
# The original contained seven-letter case of 13.7.6(3b)

The constructed full action carries the actual source plane point and seed
plane to a duad and its triangle. A single coordinate permutation now gives
the printed e₅,₆ and e₅,₇ markings. The original commutator generation,
H=KT factorization and covered local quotient are all proved from the genuine
earlier source hypotheses. No desired module or geometric conclusion is an
additional premise.

Source: Aschbacher–Smith, 13.7.6(3b), printed p.939, L₁≤K case.
-/
@[expose] public section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
open SevenParabolic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d

/-- Original13.7.6(3b) in the contained-L₁ branch, with one simultaneous printed flag marking. -/
theorem seven_source_case_of_one_le
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hrank : primeRank 3 (centralizer (V₂ : Set G)) ≤ 1)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (alternatingNaturalRepresentation (Fin 7)) eK) :
    Section08.Source.UH H V₃ = ⁅Section08.Source.UH H V₃,K⁆ ∧
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
    ∃ (f : Section08.Source.Hstar H →* Equiv.Perm (Fin 7))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 7)),
      Function.Injective f ∧
      (∀ a w, eV (ρ a w) = coreRepresentation (Fin 7) (f a) (eV w)) ∧
      (sectionImage H V₃ V₁ V₂).map eV.toLinearMap = Submodule.span (ZMod 2) {pair56} ∧
      (sectionImage H V₃ V₁ V₃).map eV.toLinearMap = Submodule.span (ZMod 2) {pair56,pair57} := by
  obtain ⟨hprod,_,f,eV,i,j,k,hf,_,he,hij,hik,hjk,hU,v,a,b,hab,hv⟩ :=
    seven_seed_geometry_of_one_le d hH hF9 hKH hK hL₁K ρ hρ hrank eK hs
  have hcover := (seven_covered_of_one_le d h hH hF9 hcentral hKH hK hL₁K ρ hρ hrank eK hs).1
  have hgen := (component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K).2.symm
  let u := seedVector H V₃ V₁ ⟨v,d.plane_le_seed v.property⟩
  have hp : eV u = SevenTriangle.pair a b := Subtype.ext hv
  have hu : u ≠ 0 := by
    intro hz
    have hw := SevenTriangle.pair_weight a b hab
    rw [←hp,hz,map_zero] at hw
    have hw0 : weight (0 : Space) = 0 := by decide
    omega
  let U := (sectionImage H V₃ V₁ V₃).map eV.toLinearMap
  have hd : Module.finrank (ZMod 2) U = 2 := (eV.finrank_map_eq _).trans
    (sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card)
  have hweight : ∀ w ∈ U, w ≠ 0 → weight w = 2 := by
    rw [show U = _ from hU]
    exact SevenTriangle.Marking.triangle_plane_weights i j k hij hik hjk
  have hum : eV u ∈ U := Submodule.mem_map_of_mem
    (show u ∈ sectionImage H V₃ V₁ V₃ from
      ⟨⟨v,le_conjugateSpanBy V₃ H (d.plane_le_seed v.property)⟩,d.plane_le_seed v.property,rfl⟩)
  obtain ⟨g,hpoint,hplane⟩ := SevenTriangle.Marking.canonical_flag U hd hweight (eV u) hum
    (fun heq => hu (eV.injective (heq.trans (map_zero eV).symm)))
  let c := LinearEquiv.ofBijective (action g) ((action).apply_bijective g)
  let eW := eV.trans c
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have heW : ∀ a w, eW (ρ a w) = coreRepresentation (Fin 7) (f' a) (eW w) := by
    intro a w
    change action g (eV (ρ a w)) = action (g * f a * g⁻¹) (action g (eV w))
    rw [he]
    simp only [← Module.End.mul_apply,← map_mul,mul_assoc,inv_mul_cancel,mul_one]
  refine ⟨hgen,hprod,hcover,f',eW,(MulAut.conj g).injective.comp hf,heW,?_,?_⟩
  · change (sectionImage H V₃ V₁ V₂).map ((action g).comp eV.toLinearMap) = _
    rw [Submodule.map_comp,plane_section_span d v hu,Submodule.map_span,
      Set.image_singleton,Submodule.map_span,Set.image_singleton]
    change Submodule.span (ZMod 2) {action g (eV u)} = _
    rw [hpoint]
  · change (sectionImage H V₃ V₁ V₃).map ((action g).comp eV.toLinearMap) = _
    rw [Submodule.map_comp]
    exact hplane
/-- In the ordinary local case, the original contained component cannot have the seven-letter natural section. -/
theorem not_seven_natural_of_ordinary_one_le
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (hordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hrank : primeRank 3 (centralizer (V₂ : Set G)) ≤ 1)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ¬ HasSectionModel H V₃ V₁ ρ K hKH
      (alternatingNaturalRepresentation (Fin 7)) eK := by
  intro hs
  obtain ⟨e⟩ := (seven_covered_of_one_le d h hH hF9 hcentral hKH hK hL₁K ρ hρ hrank eK hs).1
  obtain ⟨e₀⟩ := hordinary
  have hc := Nat.card_congr (centerCongr (e.symm.trans e₀)).toEquiv
  rw [Representation.Hexacode.even_center_card,
    alternatingGroup.center_eq_bot (by simp),card_bot] at hc
  omega
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
