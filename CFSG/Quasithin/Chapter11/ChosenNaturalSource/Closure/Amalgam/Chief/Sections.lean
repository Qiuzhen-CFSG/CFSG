module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Action
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Image
public import Theory.Representation.NormalComponentConstituents
public import Theory.Representation.BinaryOffender.MarkedChiefDetection

/-!
# Applying the full G.6.4 to an actual moved chief section

Every nontrivial seed action on a chief section of U^g has displacement
exactly one. Irreducibility kills the two-core of its faithful image and
makes the conjugates of that displacement span the section. The actual
(KT)^g is an SQTK cover, obtained from the source point normalizer. These
facts supply every hypothesis of the full known-simple G.6.4.

The section and its nontrivial seed action remain explicit. Constructing
a section on which the conjugated generalized-Fitting lift survives, and
excluding the classified models, are separate source obligations.
Source: Aschbacher--Smith, 11.5.8, p.784, and G.6.1--4, pp.345--346.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
open Chapter12.Section02
universe u

private theorem classified_of_irreducible
    {H W : Type u} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (σ : Representation (ZMod 2) H W) (hi : σ.IsIrreducible)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (t : H) (ht : t ^ 2 = 1)
    (hm : t ∉ σ.ker)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) ≤ 1) :
    ChapterG.Section06.Conclusion (imageRepresentation σ) (actionHom σ t) := by
  let τ := imageRepresentation σ
  let a := actionHom σ t
  have hiτ := imageRepresentation_irreducible σ hi
  let := hiτ
  have hf := imageRepresentation_injective σ
  have ha : a ≠ 1 := by
    intro he
    apply hm
    exact LinearMap.ext ((actionHom_eq_one_iff σ t).mp he)
  have hrpos : Module.finrank (ZMod 2) (LinearMap.range (τ a - 1)) ≠ 0 := by
    intro hz
    have he : τ a - 1 = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    apply ha
    apply hf
    exact (sub_eq_zero.mp he).trans (map_one τ).symm
  have hrexact : Module.finrank (ZMod 2) (LinearMap.range (τ a - LinearMap.id)) = 1 := by
    change Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) ≠ 0 at hrpos
    change Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) = 1
    exact le_antisymm hr (Nat.one_le_iff_ne_zero.mpr hrpos)
  have hgen : conjugateDisplacementSpan τ a ⊤ = ⊤ := by
    rw [← commutator_conjugateSpanBy_zpowers, conjugateSpanBy_zpowers_top]
    apply subspaceCommutator_top_eq_top_of_normal_faithful_irreducible τ hf hiτ
    intro he
    exact ha (mem_bot.mp (he ▸ subset_normalClosure (Set.mem_singleton a)))
  apply ChapterG.Section06.lemma_G_6_4 (q := actionHom σ) _ hrexact
  exact {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := hH
    quotient_surjective := σ.asGroupHom.rangeRestrict_surjective
    twoCore := QuadraticFourGroup.twoCore_eq_bot_of_faithful_irreducible τ hf
    faithful := hf
    involution := by change (actionHom σ t) ^ 2 = 1; rw [← map_pow, ht, map_one]
    nonidentity := ha
    displacement_rank := hrexact.le.trans (by decide)
    generated := hgen }

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)

theorem actor_sqtk (h : LocalInputs E) (hp : E.point ≠ ⊥) :
    IsSQTK KnownSimple.IsKnownSimple (actor E g) := by
  have hG₁ := E.input.source.simpleQTKE.twoLocal_sqtk
    (D.centralQuotientPreimage_twoLocal E.point hp)
  have hKT : IsSQTK KnownSimple.IsKnownSimple (KT E) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (KT_le_G₁ E h))).mp
      (hG₁.subgroup ((KT E).subgroupOf E.G₁))
  exact (IsSQTK.equiv ((KT E).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective)).mp hKT

variable [IsElementaryAbelian 2 (localClosure E)]

theorem chief_classification (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (hp : E.point ≠ ⊥) (p : OddPair E g)
    (A B : Subrepresentation (action E g)) (hAB : A ⋖ B) (v : V)
    (hm : seed E g p v ∉ (sectionRepresentation (action E g) A B).ker) :
    ChapterG.Section06.Conclusion
      (imageRepresentation (sectionRepresentation (action E g) A B))
      (actionHom (sectionRepresentation (action E g) A B) (seed E g p v)) := by
  let σ := sectionRepresentation (action E g) A B
  let : Finite (B.toSubmodule ⧸ (sectionLower (action E g) A B).toSubmodule) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hi := MathieuCode.Hexad.ChiefFlag.Actions.irreducible_section_of_covBy hAB
  have hr := fixedCodim_section_le (action E g) A B (zpowers (seed E g p v))
  rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank] at hr
  have ht : seed E g p v ^ 2 = 1 := by
    let := D.elementary
    have hv : v ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) v v.property)
    rw [← map_pow, hv, map_one]
  exact classified_of_irreducible σ hi (actor_sqtk E g h hp) (seed E g p v) ht hm
    (hr.trans (seed_displacement_le_one E g h hab hs p v))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
