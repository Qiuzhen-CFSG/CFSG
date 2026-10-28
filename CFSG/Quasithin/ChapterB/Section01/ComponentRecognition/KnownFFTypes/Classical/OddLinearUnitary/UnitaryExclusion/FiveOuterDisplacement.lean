module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.ModelInversion
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.SmallModules
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.SourceReduction
public import Theory.Representation.BinaryOddDisplacement.CentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Assembly of the small PSU₃(5) outer-involution displacement estimate

An involution outside the actual generalized Fitting subgroup acts outerly on
its central quotient: self-centralization excludes an inner action on the
component, and perfectness detects innerness on its central quotient.

Given the concrete inverted order-seven element, the commutator with any lift
has projective order seven. The small-module bound gives displacement at least
18 for this actual commutator, while the commutator rank inequality bounds it
by twice the involution's displacement. This gives nine, hence the seven used
by the parameter reduction. All actions and dimensions remain those of the
original binary representation, including when its component is a central cover.

The concrete inversion theorem and universal small-module calculation discharge
both inputs in `FiveOuterDisplacement.Inputs`, giving the unconditional
`SourceFiveOuterDisplacement`. The conditional interfaces remain available.
The final theorem applies this estimate to the existing K.2 parameter consumer;
its degree and conjugate-generation inputs remain with their independent owners.

Sources: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]

/-- The source's stronger bound nine follows from the independent concrete
inversion and small-module calculations, retaining every central cover. -/
theorem source_five_outer_displacement_ge_nine_of_seven_inputs
    (hmodel : FiveModelOuterSevenInversion)
    (hmodule : FiveSmallModuleProjectiveSevenBound.{u, v})
    (h : SourceHypotheses ρ L 5)
    (hlo : 20 ≤ Module.finrank (ZMod 2) V)
    (hhi : Module.finrank (ZMod 2) V ≤ 24)
    (t : G) (htL : t ∉ L) (ht : t ^ 2 = 1) :
    9 ≤ fixedCodim ρ (zpowers t) := by
  let : L.Normal := h.fitting ▸ (inferInstance : (generalizedFitting G).Normal)
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h.quotient
  let S := BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup S := e.symm.isSimpleGroup
  let φ : G →* MulAut S :=
    (MulAut.centralQuotientAction e).comp (MulAut.conjNormal : G →* MulAut L)
  have hφ : φ t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hcentral : centralizer (L : Set G) ≤ L := by
    rw [← h.fitting]
    exact centralizer_generalizedFitting_le G
  have houter : ¬ ∃ s : S, φ t = MulAut.conj s := by
    intro hs
    obtain ⟨l, hl⟩ :=
      (MulAut.centralQuotientAction_inner_iff e (MulAut.conjNormal t)).mp hs
    have hm : t ∈ (MulAut.innerSubgroup L).comap MulAut.conjNormal := ⟨l, hl.symm⟩
    rw [MulAut.conjNormal_comap_innerSubgroup] at hm
    exact htL ((sup_le le_rfl hcentral) hm)
  obtain ⟨s, hs, hinv⟩ := hmodel J hcard hconj (φ t) hφ houter
  obtain ⟨x, hx, hcodim⟩ := exists_small_displacement_of_inverted_centralQuotient
    ρ L e t s (by rw [hs]; decide) hinv
  rw [e.orderOf_eq, hs] at hx
  have h18 := hmodule ρ L h hlo hhi x hx
  omega

/-- Conditional assembly of the exact outer-displacement input consumed by
K.2, exposing the independent inversion and small-module calculations. -/
theorem source_five_outer_displacement_of_seven_inputs
    (hmodel : FiveModelOuterSevenInversion)
    (hmodule : FiveSmallModuleProjectiveSevenBound.{u, v}) :
    SourceFiveOuterDisplacement.{u, v} := by
  intro G V _ _ _ _ _ ρ L _ h hlo hhi t htL ht
  exact (by decide : 7 ≤ 9).trans
    (source_five_outer_displacement_ge_nine_of_seven_inputs
      ρ L hmodel hmodule h hlo hhi t htL ht)

/-- Actual application to the K.2 parameter reduction. The earlier degree
and conjugate-generation inputs are independent of the two seven-element inputs. -/
theorem source_parameter_eq_three_of_seven_inputs
    (hdegree : PrimeDegreeBound.{u, v})
    (hconjugates : SourceConjugateBounds.{u, v})
    (hmodel : FiveModelOuterSevenInversion)
    (hmodule : FiveSmallModuleProjectiveSevenBound.{u, v})
    {p : ℕ} (h : SourceHypotheses ρ L p) (hq : cubicRatio ρ ≤ 2) : p = 3 :=
  source_parameter_eq_three_of_inputs ρ L hdegree hconjugates
    (source_five_outer_displacement_of_seven_inputs hmodel hmodule) h hq

/-- Every outer involution moves at least nine binary dimensions in the source
degree window. Both the model inversion and small-module inputs are discharged,
without imposing absolute irreducibility or choosing a particular central cover. -/
theorem source_five_outer_displacement_ge_nine
    (h : SourceHypotheses ρ L 5)
    (hlo : 20 ≤ Module.finrank (ZMod 2) V)
    (hhi : Module.finrank (ZMod 2) V ≤ 24)
    (t : G) (htL : t ∉ L) (ht : t ^ 2 = 1) :
    9 ≤ fixedCodim ρ (zpowers t) :=
  source_five_outer_displacement_ge_nine_of_seven_inputs ρ L
    five_model_outer_seven_inversion five_small_module_projective_seven_bound
    h hlo hhi t htL ht

/-- The exact unconditional outer-displacement input for the K.2 reduction. -/
theorem source_five_outer_displacement : SourceFiveOuterDisplacement.{u, v} :=
  source_five_outer_displacement_of_seven_inputs
    five_model_outer_seven_inversion five_small_module_projective_seven_bound

/-- The literal K.2 parameter reduction with the outer-displacement premise
discharged. Final degree and conjugate-generation assembly belongs to the
parameter theorem's owner. -/
theorem source_parameter_eq_three_of_degree_and_conjugates
    (hdegree : PrimeDegreeBound.{u, v})
    (hconjugates : SourceConjugateBounds.{u, v})
    {p : ℕ} (h : SourceHypotheses ρ L p) (hq : cubicRatio ρ ≤ 2) : p = 3 :=
  source_parameter_eq_three_of_inputs ρ L hdegree hconjugates
    source_five_outer_displacement h hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
