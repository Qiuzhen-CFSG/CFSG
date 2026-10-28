module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Source
public import Theory.Quasithin.Rank

/-!
# Application with the full known-simple catalogue

The original counterexample makes G₁ a strongly quasithin K-group two-local.
Its two-core quotient therefore has the required SQTK property. The actual
flag supplies a nonzero plane vector, and normalization constructs the
literal conjugation action on U_H/V₁. Applying the completed overgroup and
symmetry family removes these applicability inputs as well.

The earlier module alternative is quantified over the actual action and plane
vector, so its construction can proceed independently. The final 13.8.27
assembly `qt-d-138-six-g2-source` discharges that earlier classification,
the universal embedding and uniform component reductions, and the original
F.9/centralizer inputs. This theorem completes only clauses (2--3).

Source: Aschbacher--Smith, 13.8.27(2--3), printed p.963.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
open AlternatingAndLinear.LinearReduction.Overgroup
open CriticalGeometry CriticalGeometry.AsymmetricPair SourceCompletion
open TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {K : Subgroup G}

private theorem source_action_and_vector
    {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M) :
    let _ := d.uh_elementary hHz
    ∃ _Q : CenterQuotientAction H (Source.UH H V₃) V₁,
      ∃ b : Source.UH H V₃, (b : G) ∈ V₂ ∧ (b : G) ∉ V₁ := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  obtain ⟨Q⟩ := exists_centerQuotientAction (U := Source.UH H V₃) (Z := V₁)
    (le_normalizer_conjugateSpanBy V₃ H)
    (hHz.2.1.trans d.first_normalizer.le)
  have hn : ¬ V₂ ≤ V₁ := by
    intro h
    have hc := card_le_of_le h
    rw [d.plane_card, d.line_card] at hc
    omega
  obtain ⟨b, hb, hbZ⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨Q, ⟨b, (d.plane_le_seed.trans (le_conjugateSpanBy V₃ H)) hb⟩, hb, hbZ⟩

private theorem source_ambient_sqtk
    {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    IsSQTK KnownSimple.IsKnownSimple (G₁ ⧸ pCore 2 G₁) := by
  have hp : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using d.line_card)
  have hn : V₁ ≠ ⊥ := by
    intro he
    have hc := d.line_card
    rw [he, card_bot] at hc
    contradiction
  have hloc : IsTwoLocal G₁ := ⟨V₁, hn, hp, d.first_normalizer⟩
  have hG := d.counterexample.qtke.twoLocal_sqtk hloc
  refine ⟨?_, hG.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G₁) pCore_isPGroup).trans
    (hG.stronglyQuasithin p hp ho)

/-- Actual known-simple source application. The global counterexample supplies
its K-group input, and the source flag constructs the literal quotient action
and a nonzero plane vector. Only the earlier module alternatives remain. -/
theorem source_case_one_known
    (earlier : EarlierEmbeddings.{u} KnownSimple.IsKnownSimple)
    {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hmodels : letI := d.uh_elementary hHz
      ∀ (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
        (b : Source.UH H V₃), (b : G) ∈ V₂ → (b : G) ∉ V₁ →
      (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) →
      (Nonempty (Q.Model linearFourRepresentation) ∨
        Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
        ∃ N : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)),
          (N.moduleEquiv (CenterQuotientAction.vector b)).val =
            (Pi.single (4 : Fin 7) (1 : ZMod 2) : Fin 7 → ZMod 2) + Pi.single (5 : Fin 7) 1) ∨
      Nonempty (CoverHyperplanes.CoverCoordinates H V₃ V₁))
    (hcase : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∨
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    let _ : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∧
      ⁅V, c.Ugamma V₃⁆ = V₁ ∧ V₁ ≤ c.Ugamma V₃ ∧ ¬ c.Vgamma ≤ Source.QH H ∧
      ∃ action : V →* MulAut (c.Ugamma V₃),
        (∀ v : V, ∀ u : c.Ugamma V₃,
          (action v u : G) = (v : G) * (u : G) * (v : G)⁻¹) ∧
        (∃ v : V, action v ≠ 1) ∧
        (∀ v : V, binaryLinear (action v) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (c.Ugamma V₃))) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  obtain ⟨Q, b, hb, hbZ⟩ := source_action_and_vector d hHz
  exact source_case_one earlier d facts hKH hK (source_ambient_sqtk d) hHz hF9 c
    hcentral Q b hb hbZ (hmodels Q b hb hbZ) hcase

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
