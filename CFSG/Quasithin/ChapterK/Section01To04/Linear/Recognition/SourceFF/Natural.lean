module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.Preparation
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.FieldDescent
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Natural
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Source
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear

/-!
# Natural descent on the original SL₃ component

The absolute natural model descends to the natural or dual-natural binary
action. Faithfulness of these models kills the exact covering kernel. In the
dual case inverse transpose is retained in the component identification, so
both alternatives give a genuine natural action equivalence. Normality of
the original component then gives the ambient scalar equation in those same
coordinates, discharging the input of the completed natural offender theorem.

Source: Aschbacher–Smith K.3.2(a) and K.3.2.1, printed pp.454–455.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.SourceFF
open ChapterB.QuasisimpleSource ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  {K : GroupClass.{u}} {L : Subgroup G} {B : BinaryField}

private theorem transpose_inv (x : SL(3,B.Carrier)) :
    x⁻¹.transpose = x.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  change (x⁻¹).val.transpose * x.val.transpose = 1
  rw [← Matrix.transpose_mul]
  change (x * x⁻¹).val.transpose = 1
  rw [mul_inv_cancel]
  exact Matrix.transpose_one

/-- Descent preserves the actual covering map and incorporates the graph
twist in the component identification when the absolute model is dual. -/
theorem naturalAction_of_absolute (h : SourceHypothesis K ρ L)
    (C : LinearCover B 3 L)
    (hs : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      schurDegree (inflated ρ C) = B.degree)
    (hm : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      HasAbsoluteNaturalModel (inflated ρ C)) :
    Nonempty (ActionEquiv (ρ.comp L.subtype) (linearNatural B 3)) := by
  rcases B with @⟨F, hField, hFinite, hChar, hAlg, r, hr, hF⟩
  have hAlgEq : hAlg = ZMod.algebra F 2 := Subsingleton.elim _ _
  subst hAlg
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let B : BinaryField := { Carrier := F, degree := r, degree_pos := hr, card_eq := hF }
  let := h.finite_module
  let := inflated_irreducible ρ C h.irreducible
  have models := descend_absolute_natural (inflated ρ C) B.degree B.card_eq hs hm
  have hker := (natural_cover_recognition B.Carrier C.projection C.surjective
    (ρ.comp L.subtype) B.card_eq models).1
  let j : SL(3,B.Carrier) ≃* L :=
    MulEquiv.ofBijective C.projection ⟨(MonoidHom.ker_eq_bot_iff _).mp hker, C.surjective⟩
  rcases models with models | models
  · obtain ⟨e⟩ := models
    refine ⟨⟨j.symm, e.toLinearEquiv, ?_⟩⟩
    intro l v
    have he := IntertwiningMap.isIntertwining (inflated ρ C)
      (naturalBinary B.Carrier) e.toIntertwiningMap (j.symm l) v
    change e ((ρ.comp L.subtype) (j (j.symm l)) v) =
      linearNatural B 3 (j.symm l) (e v) at he
    change e.toIntertwiningMap ((ρ.comp L.subtype) l v) =
      linearNatural B 3 (j.symm l) (e.toIntertwiningMap v)
    rw [j.apply_symm_apply] at he
    exact he
  · obtain ⟨e⟩ := models
    refine ⟨⟨j.symm.trans (Matrix.PSL3.OuterSolvable.graphSL B.Carrier),
      e.toLinearEquiv, ?_⟩⟩
    intro l v
    have he := IntertwiningMap.isIntertwining (inflated ρ C)
      (dualBinary B.Carrier) e.toIntertwiningMap (j.symm l) v
    change e ((ρ.comp L.subtype) (j (j.symm l)) v) =
      linearNatural B 3 (Matrix.SpecialLinearGroup.transpose (j.symm l)⁻¹) (e v) at he
    change e ((ρ.comp L.subtype) l v) =
      linearNatural B 3 ((Matrix.SpecialLinearGroup.transpose (j.symm l))⁻¹) (e v)
    simpa only [j.apply_symm_apply, transpose_inv,
      Representation.Equiv.toLinearEquiv_apply] using he

/-- Any actual natural identification of a normal component forces the
ambient action to be semilinear in those precise coordinates. -/
theorem semilinear_of_natural [L.Normal]
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural B 3)) :
    Natural.IsSemilinearExtension ρ L B 3 e := by
  let τ : Representation (ZMod 2) G (Fin 3 → B.Carrier) :=
    e.linearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (l : L) (v : Fin 3 → B.Carrier) :
      τ l v = Matrix.mulVec (e.groupEquiv l).val v := by
    change e.linearEquiv ((ρ.comp L.subtype) l (e.linearEquiv.symm v)) = _
    rw [e.intertwines, e.linearEquiv.apply_symm_apply]
    rfl
  intro g
  obtain ⟨σ, hσ⟩ := Representation.SL3OddNaturalNormalizer.normalizer_semilinear
    L e.groupEquiv τ hτ g
  refine ⟨σ, ?_⟩
  intro c v
  have he := hσ c (e.linearEquiv v)
  change e.linearEquiv (ρ g (e.linearEquiv.symm (c • e.linearEquiv v))) =
    σ c • e.linearEquiv (ρ g (e.linearEquiv.symm (e.linearEquiv v))) at he
  simpa only [e.linearEquiv.symm_apply_apply] using he

/-- The natural branch supplies every input of the existing source offender
calculation, including the ambient semilinear scalar equation. -/
theorem naturalSourceInput_of_absolute (h : SourceHypothesis K ρ L)
    (C : LinearCover B 3 L)
    (hs : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      schurDegree (inflated ρ C) = B.degree)
    (hm : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      HasAbsoluteNaturalModel (inflated ρ C)) :
    Nonempty (Natural.SourceInput ρ L B 3 K) := by
  let := h.finite_group
  obtain ⟨e⟩ := naturalAction_of_absolute h C hs hm
  let : L.Normal := by rw [← h.fitting]; infer_instance
  exact ⟨⟨h.sqtk, h.fitting.symm, h.quasisimple, h.faithful, h.irreducible,
    h.cubic_le_two, Or.inl rfl, e, semilinear_of_natural e⟩⟩

/-- Apply the completed natural offender theorem to the same original
action after absolute natural descent. The full B.4.2 row and sharp ratio
are conclusions, together with containment of every best offender. -/
theorem source_natural_of_absolute (h : SourceHypothesis K ρ L)
    (C : LinearCover B 3 L)
    (hs : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      schurDegree (inflated ρ C) = B.degree)
    (hm : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      HasAbsoluteNaturalModel (inflated ρ C)) :
    Nonempty (ActionEquiv (ρ.comp L.subtype) (linearNatural B 3)) ∧
      quadraticRatio ρ = 1 / 2 ∧
      (∀ A, IsBestOffender ρ A → A ≤ L) ∧ offenderSubgroup ρ = L ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
        ρ L (offenderSubgroup ρ) := by
  let := h.finite_group
  let := h.finite_module
  obtain ⟨hn⟩ := naturalSourceInput_of_absolute h C hs hm
  obtain ⟨hq, ha, hg, hc⟩ := Natural.source_natural ρ L B 3 hn
  exact ⟨⟨hn.natural⟩, by simpa using hq, ha, hg, hc⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.SourceFF
