module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents.Recognition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Head
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group

/-!
# Applying recognized constituents to the original A₆ critical pair

The abstract K/O₂(K) model and the generalized-Fitting identity give the
quasisimple, self-centralizing actor K*. The original critical actor's bound
passes to both W and Ũ_H/W. Invariant Irr⁺ members of those sections now
construct both marked natural subquotients required by the strict-case
contradiction; neither subquotient marking nor a four-dimensional upper
quotient is an input.

For a central maximal kernel the head recognition constructs its component
marking and linear equivalence, then applies the literal component-section
and SourceSix consumers. It retains the original K, both full modules and
the L₁ chief-factor conclusion. Selecting the invariant constituents and
proving centrality in the full source setup remain with
qt-d-138-six-section-recognition, using the earlier field/component/geometry
owners and qt-d-1381-source. These are conditional applications, not an
assertion of the complete 13.8.26 statement.

Source: Aschbacher–Smith 13.8.21–23 and 13.8.26, printed pp.956–958, 962.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
open NaturalSix

/-- Derive both structural inputs from the actual A₆ generalized Fitting subgroup. -/
theorem component_properties {J : Type*} [Group J] [Finite J]
    (C : Subgroup J) (hfit : C = generalizedFitting J) (e : C ≃* Alternating) :
    IsQuasisimple C ∧ centralizer (C : Set J) = ⊥ := by
  let : Group.IsPerfect Alternating := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup Alternating := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple Alternating := ⟨((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e.symm
  let : IsSimpleGroup Alternating := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  have hz : center C = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center C) inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp h))
  refine ⟨inferInstance, bot_unique ?_⟩
  intro x hx
  have hxC : x ∈ C := by
    rw [hfit] at hx ⊢
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hx
  have hxZ : (⟨x, hxC⟩ : C) ∈ center C := by
    rw [mem_center_iff]
    intro c
    exact Subtype.ext (mem_centralizer_iff.mp hx c c.property)
  rw [hz, mem_bot] at hxZ
  exact congrArg Subtype.val hxZ

open CriticalGeometry AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences

variable {G F : Type*} [Group G] [Finite G] [AddCommGroup F] [Module (ZMod 2) F]
  {L T H V V₃ V₁ K : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]


/-- The literal strict-case contradiction, with both natural models constructed. -/
theorem source_no_two_invariant_constituents
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hf : Function.Injective ρ) (hVgH : c.Vgamma ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hline : Nat.card V₁ = 2)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)))
    (τ : Representation (ZMod 2) (Source.Hstar H) F)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (hquad : ⁅c.Ugamma V₃, ⁅c.Ugamma V₃, Source.VH H V⁆⁆ ≤ Source.UH H V₃)
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)))
    (hlarge : rank (Source.starImage H (c.Ugamma V₃)) = 1 →
      ∃ B : Subgroup (Source.Hstar H), Source.starImage H (c.Ugamma V₃) < B ∧
        ∀ b ∈ B, ∀ v ∈ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)),
          ρ b v - v ∈ s.image (c.Aone V₁))
    (W : Subrepresentation ρ)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Alternating)
    (hfit : Source.starImage H K = generalizedFitting (Source.Hstar H))
    (IW : Subrepresentation W.toRepresentation)
    (hIW : IsIrrPlus W.toRepresentation (Source.starImage H K) IW.toSubmodule)
    (IQ : Subrepresentation W.quotientRepresentation)
    (hIQ : IsIrrPlus W.quotientRepresentation (Source.starImage H K) IQ.toSubmodule)
    (L₁ : Subgroup G) (hL : L₁ ≤ H) (hT : T ≤ H)
    (S : Sylow 2 (Source.Hstar H)) (hS : (S : Subgroup _) = Source.starImage H T)
    (hi : (Source.starImage H T).relIndex (Source.starImage H (L₁ ⊔ T)) = 3)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnorm : L₁ ⊔ T ≤ normalizer (V : Set G))
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (y : H) (hplace : c.Vgamma.map (MulAut.conj (y : G)).toMonoidHom ≤
      (L₁ ⊔ T).pCoreIn 2) : False := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  let : (Source.starImage H K).Normal := hfit ▸ inferInstance
  let e := (Components.componentStarEquiv H K hKH hK).symm.trans eK
  obtain ⟨hC, hc⟩ := component_properties (Source.starImage H K) hfit e
  let := hC
  obtain ⟨mW, _, haW⟩ := natural_section_of_invariant_irrPlus W.toRepresentation
    (Source.starImage H K) hfit hc e IW hIW _ hA
    ((fixedCodim_subrepresentation_le ρ W _).trans hbound)
  obtain ⟨mQ, _, haQ⟩ := natural_section_of_invariant_irrPlus W.quotientRepresentation
    (Source.starImage H K) hfit hc e IQ hIQ _ hA
    (by have hb := fixedCodim_quotient_add_subrepresentation_le ρ W (Source.starImage H (c.Ugamma V₃)); omega)
  exact source_no_two_faithful_sections_of_original_parabolic c ρ s hf hVgH
    hreverse hline hcritical τ t hquad hA hbound hlarge W mW mQ haW haQ
    L₁ hL hT S hS hi hflag hindex hnorm hnc y hplace

open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension

/-- Construct the intrinsic section marking and apply the full SourceSix conclusion. -/
theorem source_alternative_of_central_head_constituent
    (T : Sylow 2 G) {L V V₂ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (e₀ : (K ⧸ pCore 2 K) ≃* Alternating)
    (hfit : Source.starImage H K = generalizedFitting (Source.Hstar H))
    (W : Subrepresentation ρ) (hmax : IsCoatom W)
    (hW : W.toSubmodule ≤ fixedSpace ρ (Source.starImage H K))
    (IQ : Subrepresentation W.quotientRepresentation)
    (hIQ : IsIrrPlus W.quotientRepresentation (Source.starImage H K) IQ.toSubmodule)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    let := d.uh_elementary hH
    ∃ eK : (K ⧸ pCore 2 K) ≃* Alternating,
    HasSectionModel H V₃ V₁ ρ K hKH alternatingAction eK ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Alternating) ∧
      SourceSix.MarkedFullAction hKH eK ρ ∧
      CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
        (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
          (le_sup_left.trans hH.1.2) ρ) := by
  let := d.uh_elementary hH
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  let : (Source.starImage H K).Normal := hfit ▸ inferInstance
  let : IsIrreducible W.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom W hmax
  let e := (Components.componentStarEquiv H K hKH hK).symm.trans e₀
  obtain ⟨hC, hc⟩ := component_properties (Source.starImage H K) hfit e
  let := hC
  have hb : fixedCodim W.quotientRepresentation A ≤ 2 * rank A := by
    have hh := fixedCodim_quotient_add_subrepresentation_le ρ W A
    omega
  obtain ⟨eC, E', he⟩ := head_marked_of_invariant_irrPlus W.quotientRepresentation
    (Source.starImage H K) hfit hc e IQ hIQ A hA hb
  exact ⟨(Components.componentStarEquiv H K hKH hK).trans eC,
    source_alternative_of_central_head T d earlier hH hKH hK ρ hρ hgen eC W hW E' he⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
