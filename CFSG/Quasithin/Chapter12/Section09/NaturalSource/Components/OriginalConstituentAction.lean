module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianNatural
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalInput
public import Theory.Representation.BinaryConjugationSection.NormalizingActors

/-!
# The whole point centralizer on the original chosen central quotient

The original point centralizer normalizes the chosen constituent and its
point component. Literal conjugation therefore extends the component action
to the entire point centralizer, on I and on I/C_I(K₁). The projection and
every original conjugator are retained; no splitting of the central
attachment and no natural-four reduction are used.
Source: Aschbacher--Smith 12.9.4, printed pp.859--860.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {J I H : Subgroup G}

private def chosenCoordinates (c : ChosenModule T J I) :
    letI := c.elementary
    c.space ≃ₗ[ZMod 2] Additive I := by
  let := c.elementary
  exact (MulEquiv.toAdditiveRight c.spaceEquiv).toLinearEquiv (ZMod.map_smul _)

private def wholeChosenAction (c : ChosenModule T J I)
    (hHI : H ≤ normalizer (I : Set G)) : Representation (ZMod 2) H c.space := by
  let := c.elementary
  exact (chosenCoordinates c).symm.conjRingEquiv.toMonoidHom.comp
    (BinaryConjugationSection.originalNormalizerAction hHI)

omit [Finite G] in
private theorem wholeChosenAction_component (c : ChosenModule T J I)
    (hHI : H ≤ normalizer (I : Set G)) (hJH : J ≤ H) (j : J) :
    wholeChosenAction c hHI (inclusion hJH j) = c.chosenAction j := by
  let := c.elementary
  apply LinearMap.ext
  intro v
  apply (chosenCoordinates c).injective
  change (chosenCoordinates c) ((chosenCoordinates c).symm
    (BinaryConjugationSection.originalNormalizerAction hHI (inclusion hJH j)
      ((chosenCoordinates c) v))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [BinaryConjugationSection.originalNormalizerAction_apply_coe]
  change (j : G) * (c.spaceEquiv (Multiplicative.ofAdd v) : G) * (j : G)⁻¹ =
    (c.spaceEquiv (Multiplicative.ofAdd (c.chosenAction j v)) : G)
  rw [c.spaceEquiv_apply, c.spaceEquiv_apply]
  rfl

private def wholeChosenCentral (c : ChosenModule T J I)
    (hHI : H ≤ normalizer (I : Set G)) (hJH : J ≤ H)
    (hHJ : H ≤ normalizer (J : Set G)) :
    Subrepresentation (wholeChosenAction c hHI) where
  toSubmodule := (fixedSpace (reducedRepresentation (J ⊔ (T : Subgroup G)))
    (J.subgroupOf (J ⊔ (T : Subgroup G)))).comap c.space.subtype
  apply_mem_toSubmodule := by
    let K := J.subgroupOf H
    let : K.Normal := (normal_subgroupOf_iff_le_normalizer hJH).mpr hHJ
    have he : fixedSpace (wholeChosenAction c hHI) K =
        (fixedSpace (reducedRepresentation (J ⊔ (T : Subgroup G)))
          (J.subgroupOf (J ⊔ (T : Subgroup G)))).comap c.space.subtype := by
      ext v
      constructor
      · intro hv j
        let j' : J := ⟨j.val, j.property⟩
        have hh := hv ((subgroupOfEquivOfLe hJH).symm j')
        change wholeChosenAction c hHI (inclusion hJH j') v = v at hh
        rw [wholeChosenAction_component] at hh
        exact congrArg Subtype.val hh
      · intro hv j
        let j' : J := ⟨j.val, j.property⟩
        have hh := hv ((subgroupOfEquivOfLe (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left)).symm j')
        change wholeChosenAction c hHI (inclusion hJH j') v = v
        rw [wholeChosenAction_component]
        exact Subtype.ext hh
    intro a v hv
    rw [← he] at hv ⊢
    exact (fixedSubrepresentation (wholeChosenAction c hHI) K).apply_mem_toSubmodule a hv

omit [Finite G] in
/-- The chosen central quotient admits the literal action of every common
normalizer containing its component, with the same component restriction and
the same original quotient map. -/
theorem exists_chosen_central_action_of_normalizes
    (c : ChosenModule T J I) (hHI : H ≤ normalizer (I : Set G))
    (hJH : J ≤ H) (hHJ : H ≤ normalizer (J : Set G)) :
    ∃ ρ : Representation (ZMod 2) H c.chosenCentralQuotient,
      (∀ j : J, ρ (inclusion hJH j) = c.chosenCentralAction j) ∧
      ∀ (a : H) (v : I),
        ρ a (c.toCentralQuotient v).toAdd =
          (c.toCentralQuotient (I.normalizerMonoidHom (inclusion hHI a) v)).toAdd := by
  let := c.elementary
  let ρ := (wholeChosenCentral c hHI hJH hHJ).quotientRepresentation
  refine ⟨ρ, ?_, ?_⟩
  · intro j
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change Submodule.Quotient.mk (wholeChosenAction c hHI (inclusion hJH j) v) =
        Submodule.Quotient.mk (c.chosenAction j v)
      rw [wholeChosenAction_component]
  · intro a v
    change Submodule.Quotient.mk
        (wholeChosenAction c hHI a (c.spaceEquiv.symm v).toAdd) =
      Submodule.Quotient.mk (c.spaceEquiv.symm
        (I.normalizerMonoidHom (inclusion hHI a) v)).toAdd
    congr 1
    apply (chosenCoordinates c).injective
    change (chosenCoordinates c) ((chosenCoordinates c).symm
      (BinaryConjugationSection.originalNormalizerAction hHI a
        ((chosenCoordinates c) (c.spaceEquiv.symm v).toAdd))) = _
    rw [LinearEquiv.apply_symm_apply]
    change BinaryConjugationSection.originalNormalizerAction hHI a
      (Additive.ofMul (c.spaceEquiv (c.spaceEquiv.symm v))) =
        Additive.ofMul (c.spaceEquiv (c.spaceEquiv.symm
          (I.normalizerMonoidHom (inclusion hHI a) v)))
    rw [c.spaceEquiv.apply_symm_apply, c.spaceEquiv.apply_symm_apply]
    apply Additive.toMul.injective
    exact BinaryConjugationSection.originalNormalizerAction_apply hHI a (Additive.ofMul v)

variable {L V : Subgroup G}

/-- The actual original point centralizer acts on the unchanged chosen
central quotient, before any natural-four identification. -/
theorem nonabelian_caseFive_chosen_point_action
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (c : ChosenModule T C.K1 I) (hiZ : I ≤ F.ZU) :
    ∃ ρ : Representation (ZMod 2) F.H c.chosenCentralQuotient,
      (∀ j : C.K1, ρ (inclusion C.point_le j) = c.chosenCentralAction j) ∧
      ∀ (a : F.H) (v : I),
        ∃ v' : I, (v' : G) = a * v * (a : G)⁻¹ ∧
          ρ a (c.toCentralQuotient v).toAdd = (c.toCentralQuotient v').toAdd := by
  have hHI := nonabelian_caseFive_point_normalizes_chosen
    modules h preferred earlier F hne g hgP hgH B h5 C c hiZ
  have hHK : F.H ≤ normalizer (C.K1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal
  obtain ⟨ρ, hj, he⟩ := exists_chosen_central_action_of_normalizes c hHI C.point_le hHK
  exact ⟨ρ, hj, fun a v => ⟨I.normalizerMonoidHom (inclusion hHI a) v, rfl, he a v⟩⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
