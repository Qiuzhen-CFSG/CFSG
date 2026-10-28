module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SourceAssembly.Local
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.Theta
public import Theory.GroupTheory.IndexTwoConjugatePair

/-!
# The original higher-field Borel dichotomy

The common involution line and transitivity of the local A₆ action identify
H ∩ M with H ∩ N(V). Maximal-local uniqueness gives N(V) ≤ M; conversely
an element of H ∩ M fixes the common line, so its conjugate of V contains
the whole nonzero L-orbit and hence equals V.

Together with the genuine solvable-overgroup and theta theorems, this
constructs the earlier Borel input from SourceContext. The concrete model
bridge supplies every automorphism hypothesis. The resulting dichotomy
retains the marked inverter and the covered zero-direction fixation.
This is the source reduction in 13.8.20; its two contradictions remain
with qt-d-138-fields-source. No Borel, exclusion or containment conclusion
is assumed.
Source: Aschbacher–Smith, 13.8.20, printed p.954 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalBorel LocalBorel.CentralizingCalculation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The original common line and transitive A6 action determine the overlap normalizer. -/
theorem source_overlap_normalizer
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    H ⊓ M = H ⊓ normalizer (V : Set G) := by
  let d := c.localSetup
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  have hV1 : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hnV : normalizer (V : Set G) ≤ M := by
    rw [d.local_normalizer]
    apply normalizer_le_of_unique_maximalTwoLocal
      (c.maximal.sylow_normalized_maximal_unique d.normalizes_L
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
      hF9.elementary.isPGroup
    · intro he
      change V = ⊥ at he
      have hle : Nat.card V₁ ≤ Nat.card V := card_le_of_le hV1
      rw [he,card_bot,d.line_card] at hle
      omega
    · exact d.normalizes_V
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1,?_⟩
    have hxL : x ∈ normalizer (L : Set G) := d.local_normalizer ▸ hx.2
    have hLn : L ≤ normalizer (V.conjBy x : Set G) :=
      normalizes_conjugate_of_normalizes hxL (le_sup_left.trans d.normalizes_V)
    obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
    have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
    have hfix : x * (z : G) * x⁻¹ = z := by
      have he := mem_centralizer_iff.mp (hF9.H_centralizes hx.1) z z.property
      calc
        x * (z : G) * x⁻¹ = (z : G) * x * x⁻¹ := by rw [he]
        _ = z := mul_inv_cancel_right _ _
    have hzc : (z : G) ∈ V.conjBy x := ⟨z,hV1 z.property,hfix⟩
    have hle : V ≤ V.conjBy x := by
      intro y hy
      by_cases hy1 : y = 1
      · exact hy1 ▸ one_mem _
      obtain ⟨l,hl,he⟩ := local_nonzero_transitive d (hV1 z.property) hy hz1 hy1
      exact he ▸ (mem_normalizer_iff.mp (hLn hl) z).mp hzc
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (eq_of_le_of_card_ge hle (by
      change Nat.card (V.map (MulAut.conj x).toMonoidHom) ≤ Nat.card V
      rw [card_map_of_injective (MulAut.conj x).injective])).symm
  · exact inf_le_inf_left H hnV

/-- Construct all preceding local inputs to the Borel reduction. -/
def sourceInput
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
    (hn : 1 < n) (m : TorusModels.Assembly.Model.{u,0} (Source.starImage H K) n unitary four) :
    SourceInput.{u,0} T H K L V V₁ V₂ V₃ M G₁ n unitary four where
  standing := c.localSetup
  member := c.component.local_overgroup
  component_le := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  model := m
  degree := hn
  generated := c.component.generated.symm
  universal := SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339
  intersection := source_overlap_normalizer c
  theta := (Section07.ModelExclusions.theta_intersection (localNaturalSetup c.localSetup)
    c.maximal c.component.local_overgroup).symm

/-- The actual higher-field source gives its Borel dichotomy, including the
prescribed inverter and, in the covered case, the fixed zero direction. -/
theorem source_borel_alternatives
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    letI : (Source.starImage H K).Normal :=
      c.component.normal.map _ (QuotientGroup.mk'_surjective _)
    ∃ (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H),
      borel H K (T : Subgroup G) hKH hT ≤ M ∧
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      ((Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
          InvertsTwoCoreQuotient (one L T V₁) t.val ∧
          SylowBorelAlternative.{u,0} H K (T : Subgroup G) (one L T V₁)
            (QuotientGroup.mk' (pCore 2 H)
              ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩)) ∨
        (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
          InvertsTwoCoreQuotient (plus L T V₁) t.val ∧
          coreAction (zero L) ⟨t.val,L_normalizes_zero L t.property.2⟩ = 1 ∧
          SylowBorelAlternative.{u,0} H K (T : Subgroup G) (plus L T V₁)
            (QuotientGroup.mk' (pCore 2 H)
              ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩))) := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  obtain ⟨n,hn,unitary,four,m⟩ := torus_model_of_higher_field hfield
  let i := sourceInput c hn (Placement.model_transport m
    (Components.componentStarEquiv H K hKH c.component.component).symm)
  refine ⟨i.component_le,i.sylow_H,?_⟩
  rcases local_quotient_alternatives c.localSetup with ⟨e,he⟩ | ⟨e,he⟩
  · obtain ⟨a⟩ := LocalFitting.ordinary_natural c.localSetup e he
    obtain ⟨hB,t,hinv,hb⟩ := i.sylowBorelAlternative_ordinary a
    exact ⟨hB,t,Or.inl ⟨⟨e⟩,hinv,hb⟩⟩
  · obtain ⟨a⟩ := local_covered_flag_model c.localSetup e he
    obtain ⟨hB,t,hinv,hz,hb⟩ := i.sylowBorelAlternative_covered a
      (CoverFactorization.source_factorization a)
    exact ⟨hB,t,Or.inr ⟨⟨e⟩,hinv,hz,hb⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
