module

public import Theory.Representation.SL2NaturalOffenders.Ratios.FixedLine

/-!
# The natural PSL₂ branch of K.3.1

An actual group equivalence and binary intertwiner identify the module. Changing
coordinates then applies the intrinsic natural SL₂ offender theorem: both ratios
are one, and the unique offender in the specified Sylow subgroup is its literal
intersection with the normal layer. The same actor is quadratic and has the
field's binary dimension. This proves the model calculation K.3.1.1; it does not
assert that every module with cubic ratio at most two is natural.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.1.1,
printed p.454. The natural module remains separate from the four-dimensional
orthogonal module, including the two different modules for PSL₂(4).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender
open scoped ENNReal

variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Algebra (ZMod 2) F]

/-- The literal natural-module identification; the linear map intertwines the
specified normal subgroup's action with matrix multiplication. -/
structure NaturalModel (ρ : Representation (ZMod 2) G V) (L : Subgroup G) where
  groupEquiv : L ≃* Matrix.SpecialLinearGroup (Fin 2) F
  coordinates : V ≃ₗ[ZMod 2] (Fin 2 → F)
  intertwines : ∀ (g : L) (v : V),
    coordinates (ρ (g : G) v) = Matrix.mulVec (groupEquiv g).val (coordinates v)

namespace NaturalModel
variable {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (M : NaturalModel (F := F) ρ L)

/-- The original ambient action, conjugated by the supplied binary coordinates. -/
def coordinateAction : Representation (ZMod 2) G (Fin 2 → F) :=
  M.coordinates.conjRingEquiv.toMonoidHom.comp ρ

@[simp] theorem coordinateAction_apply (g : G) (v : V) :
    M.coordinateAction g (M.coordinates v) = M.coordinates (ρ g v) := by
  change M.coordinates (ρ g (M.coordinates.symm (M.coordinates v))) = _
  rw [M.coordinates.symm_apply_apply]

theorem coordinateAction_natural (g : L) (v : Fin 2 → F) :
    M.coordinateAction (g : G) v = Matrix.mulVec (M.groupEquiv g).val v := by
  change M.coordinates (ρ (g : G) (M.coordinates.symm v)) = _
  rw [M.intertwines, M.coordinates.apply_symm_apply]

theorem coordinateAction_injective (hfaith : Function.Injective ρ) :
    Function.Injective M.coordinateAction :=
  M.coordinates.conjRingEquiv.injective.comp hfaith

theorem fixedCodim_eq (A : Subgroup G) :
    fixedCodim ρ A = fixedCodim M.coordinateAction A := by
  simpa using fixedCodim_map_equivariant ρ M.coordinateAction (MonoidHom.id G)
    M.coordinates (fun g v => (M.coordinateAction_apply g v).symm) A

theorem offender_iff (A : Subgroup G) :
    IsOffender ρ A ↔ IsOffender M.coordinateAction A := by
  simp only [IsOffender, M.fixedCodim_eq]

theorem quadratic_iff (A : Subgroup G) :
    IsQuadratic ρ A ↔ IsQuadratic M.coordinateAction A := by
  constructor
  · exact quadratic_of_equivariant_surjection ρ M.coordinateAction
      M.coordinates.toLinearMap M.coordinates.surjective
      (fun g v => (M.coordinateAction_apply g v).symm) A
  · apply quadratic_of_equivariant_surjection M.coordinateAction ρ
      M.coordinates.symm.toLinearMap M.coordinates.symm.surjective
    intro g v
    change M.coordinates.symm (M.coordinates (ρ g (M.coordinates.symm v))) = _
    rw [M.coordinates.symm_apply_apply]
    rfl

theorem cubic_iff (A : Subgroup G) :
    IsCubic ρ A ↔ IsCubic M.coordinateAction A := by
  have hd (g : G) (v : V) :
      displacement M.coordinateAction g (M.coordinates v) =
        M.coordinates (displacement ρ g v) := by
    simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply,
      M.coordinateAction_apply, map_sub]
  constructor
  · intro h a ha b hb c hc v
    obtain ⟨w, rfl⟩ := M.coordinates.surjective v
    rw [hd, hd, hd, h a ha b hb c hc w, map_zero]
  · intro h a ha b hb c hc v
    apply M.coordinates.injective
    rw [map_zero, ← hd, ← hd, ← hd]
    exact h a ha b hb c hc _

variable [Finite F]
include M

theorem ratios_eq_one [Finite G] [L.Normal]
    (hF : 2 < Nat.card F) (hfaith : Function.Injective ρ) :
    quadraticRatio ρ = 1 ∧ cubicRatio ρ = 1 := by
  have h := Representation.SL2NaturalOffenders.Ratios.ratios_eq_one L M.groupEquiv
    M.coordinateAction M.coordinateAction_natural hF (M.coordinateAction_injective hfaith)
  have hq : quadraticRatio ρ = quadraticRatio M.coordinateAction := by
    unfold quadraticRatio
    congr 1
    ext A
    simp only [M.quadratic_iff, actionRatio, M.fixedCodim_eq]
  have hc : cubicRatio ρ = cubicRatio M.coordinateAction := by
    unfold cubicRatio
    congr 1
    ext A
    simp only [M.cubic_iff, actionRatio, M.fixedCodim_eq]
  exact ⟨hq.trans h.1, hc.trans h.2⟩

/-- The source's unique Sylow offender, on the original module. -/
theorem offender_iff_eq_sylowInf [Finite G] [L.Normal]
    (hF : 2 < Nat.card F) (hfaith : Function.Injective ρ)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T) :
    IsOffender ρ A ↔ A = (T : Subgroup G) ⊓ L :=
  (M.offender_iff A).trans
    (Representation.SL2NaturalOffenders.Ratios.offender_iff_eq_sylowInf L M.groupEquiv
      M.coordinateAction M.coordinateAction_natural hF (M.coordinateAction_injective hfaith) T hAT)

/-- The literal Sylow intersection is quadratic, with equal actor rank and
fixed codimension equal to the binary degree of the defining field. -/
theorem sylowInf_calculation [Finite G] [L.Normal] (T : Sylow 2 G) :
    IsQuadratic ρ ((T : Subgroup G) ⊓ L) ∧
    rank ((T : Subgroup G) ⊓ L) = Module.finrank (ZMod 2) F ∧
    fixedCodim ρ ((T : Subgroup G) ⊓ L) = Module.finrank (ZMod 2) F := by
  obtain ⟨P, hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  rw [← hP]
  exact ⟨(M.quadratic_iff _).mpr
      (Representation.SL2NaturalOffenders.Ratios.sylowImage_quadratic L M.groupEquiv
        M.coordinateAction M.coordinateAction_natural P),
    Representation.SL2NaturalOffenders.Ratios.sylowImage_rank L M.groupEquiv P,
    (M.fixedCodim_eq _).trans
      (Representation.SL2NaturalOffenders.Ratios.sylowImage_fixedCodim L M.groupEquiv
        M.coordinateAction M.coordinateAction_natural P)⟩

/-- Every ambient actor is semilinear on the supplied natural coordinates. -/
theorem semilinear [L.Normal] (g : G) :
    ∃ σ : F ≃+* F, ∀ (c : F) (v : Fin 2 → F),
      M.coordinateAction g (c • v) = σ c • M.coordinateAction g v :=
  Representation.SL2NaturalOffenders.normalizer_semilinear L M.groupEquiv
    M.coordinateAction M.coordinateAction_natural g

/-- An involution outside the layer has a nontrivial field part. This conclusion
uses the original faithful action, not a chosen full linear normalizer. -/
theorem outer_involution_field_part [L.Normal] (hfaith : Function.Injective ρ)
    {a : G} (ha : a ^ 2 = 1) (haL : a ∉ L) :
    ∃ σ : F ≃+* F, σ ≠ RingEquiv.refl F ∧
      ∀ (c : F) (v : Fin 2 → F),
        M.coordinateAction a (c • v) = σ c • M.coordinateAction a v := by
  obtain ⟨σ, hσ⟩ := M.semilinear a
  refine ⟨σ, ?_, hσ⟩
  intro he
  apply haL
  apply Representation.SL2NaturalOffenders.mem_of_linear_square_one L M.groupEquiv
    M.coordinateAction (M.coordinateAction_injective hfaith) M.coordinateAction_natural ha
  simpa [he] using hσ

/-- Best-offender generation is transported to the original vector space. -/
theorem generatedBy_bestOffenders_sylow [Finite G] [FiniteDimensional (ZMod 2) V]
    [L.Normal] (hF : 2 < Nat.card F) (hfaith : Function.Injective ρ) (T : Sylow 2 G) :
    generatedBy {A | IsBestOffender ρ A} (T : Subgroup G) = (T : Subgroup G) ⊓ L := by
  have hn := Representation.SL2NaturalOffenders.Ratios.not_strong L M.groupEquiv
    M.coordinateAction M.coordinateAction_natural hF (M.coordinateAction_injective hfaith)
  have hnρ : ¬ IsStrongFFModule ρ := by
    rintro ⟨A, hA, hlt⟩
    exact hn ⟨A, hA, (M.fixedCodim_eq A) ▸ hlt⟩
  have hb (A : Subgroup G) : IsBestOffender ρ A ↔ IsBestOffender M.coordinateAction A := by
    rw [isBestOffender_iff_of_not_strong ρ hnρ,
      isBestOffender_iff_of_not_strong M.coordinateAction hn, M.fixedCodim_eq]
  have he : generatedBy {A | IsBestOffender ρ A} (T : Subgroup G) =
      generatedBy {A | IsBestOffender M.coordinateAction A} (T : Subgroup G) := by
    simp only [generatedBy, Set.mem_ofPred_eq, hb]
  exact he.trans (Representation.SL2NaturalOffenders.Ratios.generatedBy_bestOffenders_sylow
    L M.groupEquiv M.coordinateAction M.coordinateAction_natural hF
    (M.coordinateAction_injective hfaith) T)

/-- The commutator and common fixed space are literally equal on the original
module; this is the line asserted at the beginning of K.3.1.1. -/
theorem sylowInf_commutator_eq_fixedSpace [Finite G] [L.Normal] (T : Sylow 2 G) :
    subspaceCommutator ρ ⊤ ((T : Subgroup G) ⊓ L) =
      fixedSpace ρ ((T : Subgroup G) ⊓ L) := by
  obtain ⟨P, hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  let A := (T : Subgroup G) ⊓ L
  have hc : subspaceCommutator M.coordinateAction ⊤ A = fixedSpace M.coordinateAction A := by
    rw [show A = (P : Subgroup L).map L.subtype from hP.symm]
    exact Representation.SL2NaturalOffenders.Ratios.sylowImage_commutator_eq_fixedSpace
      L M.groupEquiv M.coordinateAction M.coordinateAction_natural P
  apply Submodule.map_injective_of_injective M.coordinates.injective
  have hm := subspaceCommutator_map_embedding M.coordinateAction ρ (MonoidHom.id G)
    M.coordinates.toLinearMap M.coordinateAction_apply A ⊤
  have hf := fixedSpace_map_equivariant ρ M.coordinateAction (MonoidHom.id G)
    M.coordinates (fun g v => (M.coordinateAction_apply g v).symm) A
  have ht : (⊤ : Submodule (ZMod 2) V).map M.coordinates.toLinearMap = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨w, rfl⟩ := M.coordinates.surjective v
    exact ⟨w, Submodule.mem_top, rfl⟩
  rw [ht, Subgroup.map_id] at hm
  rw [Subgroup.map_id] at hf
  exact hm.symm.trans (hc.trans hf.symm)

end NaturalModel
end CFSG.Quasithin.ChapterK.RankOne
