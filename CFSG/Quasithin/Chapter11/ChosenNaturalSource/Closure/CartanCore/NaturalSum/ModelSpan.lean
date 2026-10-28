module
public import Theory.Representation.FixedIsotypicCentralizer
public import Theory.Representation.IsotypicCopies
public import Theory.Representation.SpecialLinearNatural
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.Algebra.Module.ZMod

/-!+# Natural binary modules under ambient conjugation

Every automorphism of SL₂ over a finite binary field is inner times a field
automorphism. Its natural module therefore has a binary-linear intertwiner
with the untwisted module. The span of copies of the natural module is
invariant under any ambient action normalizing this SL₂ action. If one copy
generates under that ambient action, the whole module is its isotypic
component and hence a finite direct sum of natural copies.

This is the representation-theoretic step of Aschbacher--Smith 11.5.5(3),
printed p.780. It includes the field of four elements.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.NaturalSum
open Representation Module
open scoped MonoidAlgebra
variable (F : Type*) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev Model := Fin 2 → F
abbrev Actor := Matrix.SpecialLinearGroup (Fin 2) F

def natural : Representation (ZMod 2) (Actor F) (Model F) :=
  restrictScalars (k := ZMod 2) (specialLinearNatural 2)

private def coefficients (s : F ≃+* F) : Model F ≃ₗ[ZMod 2] Model F where
  toFun v i := s (v i)
  invFun v i := s.symm (v i)
  left_inv v := by ext i; exact s.symm_apply_apply _
  right_inv v := by ext i; exact s.apply_symm_apply _
  map_add' v w := by ext i; exact s.map_add _ _
  map_smul' c v := by ext i; exact ZMod.map_smul s c (v i)

omit [Finite F] [CharP F 2] in
private theorem coefficients_intertwines (s : F ≃+* F) (g : Actor F) (v : Model F) :
    coefficients F s (natural F g v) =
      natural F (Theory.PSL2.sl2FieldAut s g) (coefficients F s v) := by
  ext i
  simp [coefficients, natural, Representation.restrictScalars, specialLinearNatural_apply,
    Theory.PSL2.sl2FieldAut, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Every group automorphism preserves the binary natural type, with an
actual intertwiner accounting for the field twist. -/
theorem natural_automorphism (a : MulAut (Actor F)) :
    ∃ e : Model F ≃ₗ[ZMod 2] Model F,
      ∀ g v, e (natural F g v) = natural F (a g) (e v) := by
  obtain ⟨r, s, rfl⟩ := Theory.PSL2.sl2_semilinear_coverage a
  let c := coefficients F s
  let b := LinearEquiv.ofBijective (natural F r) (Representation.apply_bijective _ _)
  refine ⟨c.trans b, ?_⟩
  intro g v
  change natural F r (coefficients F s (natural F g v)) =
    natural F (r * Theory.PSL2.sl2FieldAut s g * r⁻¹)
      (natural F r (coefficients F s v))
  rw [coefficients_intertwines]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

instance natural_irreducible : (natural F).IsIrreducible := by
  refine { eq_bot_or_eq_top := ?_ }
  intro P
  by_cases hp : P = ⊥
  · exact Or.inl hp
  right
  apply top_unique
  have hne : P.toSubmodule ≠ ⊥ := fun he => hp (Subrepresentation.toSubmodule_injective he)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ P.toSubmodule.zero_mem
  obtain ⟨g, hg⟩ := Matrix.SL2.exists_mulVec_eq F v w hv0 hw
  have h := P.apply_mem_toSubmodule g hv
  change Matrix.mulVec g.val v ∈ P.toSubmodule at h
  rwa [hg] at h

variable {F}
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- A translated natural copy has an actual injective natural marking,
and its image is exactly the translate of the original seed image. -/
theorem exists_conjugate_natural_embedding (ρ : Representation (ZMod 2) H W)
    (σ : Representation (ZMod 2) (Actor F) W)
    (hc : ∀ h : H, ∃ a : MulAut (Actor F),
      ∀ g v, ρ h (σ g v) = σ (a g) (ρ h v))
    (j : (natural F).IntertwiningMap σ) (hj : Function.Injective j) (h : H) :
    ∃ j' : (natural F).IntertwiningMap σ, Function.Injective j' ∧
      j'.range.toSubmodule = j.range.toSubmodule.map (ρ h) := by
  obtain ⟨a, ha⟩ := hc h
  obtain ⟨e, he⟩ := natural_automorphism F a.symm
  let j' : (natural F).IntertwiningMap σ := {
    toLinearMap := (ρ h).comp (j.toLinearMap.comp e.toLinearMap)
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      change ρ h (j (e (natural F g v))) = σ g (ρ h (j (e v)))
      rw [he, j.isIntertwining, ha, a.apply_symm_apply] }
  refine ⟨j', (Representation.apply_bijective ρ h).1.comp (hj.comp e.injective), ?_⟩
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨j (e v), ⟨e v, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨v, rfl⟩, rfl⟩
    refine ⟨e.symm v, ?_⟩
    change ρ h (j (e (e.symm v))) = ρ h (j v)
    rw [e.apply_symm_apply]

/-- The span of natural copies is stable under an action normalizing the
actual matrix action, without a semisimplicity assumption. -/
theorem natural_typeSpan_stable (ρ : Representation (ZMod 2) H W)
    (σ : Representation (ZMod 2) (Actor F) W)
    (hc : ∀ h : H, ∃ a : MulAut (Actor F),
      ∀ g v, ρ h (σ g v) = σ (a g) (ρ h v))
    (h : H) (v : W) (hv : v ∈ typeSpan σ (natural F)) :
    ρ h v ∈ typeSpan σ (natural F) := by
  obtain ⟨a, ha⟩ := hc h
  obtain ⟨e, he⟩ := natural_automorphism F a.symm
  let R := typeSpan σ (natural F)
  let P : Subrepresentation σ := {
    toSubmodule := R.toSubmodule.comap (ρ h)
    apply_mem_toSubmodule g v hv := by
      change ρ h (σ g v) ∈ R.toSubmodule
      rw [ha]
      exact R.apply_mem_toSubmodule (a g) hv }
  have hle : R ≤ P := by
    apply iSup_le
    intro j w hw
    obtain ⟨x, rfl⟩ := hw
    let j' : (natural F).IntertwiningMap σ := {
      toLinearMap := (ρ h).comp (j.toLinearMap.comp e.toLinearMap)
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        change ρ h (j (e (natural F g v))) = σ g (ρ h (j (e v)))
        rw [he, j.isIntertwining, ha, a.apply_symm_apply] }
    change ρ h (j x) ∈ R
    apply (show j'.range ≤ R from le_iSup _ j')
    refine ⟨e.symm x, ?_⟩
    change ρ h (j (e (e.symm x))) = _
    rw [e.apply_symm_apply]
  exact hle hv

variable [FiniteDimensional (ZMod 2) W]

/-- A generating natural seed yields finite natural coordinates for the
whole action. Semisimplicity is derived from the isotypic component. -/
theorem natural_span_coordinates (ρ : Representation (ZMod 2) H W)
    (σ : Representation (ZMod 2) (Actor F) W)
    (hc : ∀ h : H, ∃ a : MulAut (Actor F),
      ∀ g v, ρ h (σ g v) = σ (a g) (ρ h v))
    (j : (natural F).IntertwiningMap σ)
    (hgen : ∀ P : Subrepresentation ρ, j.range.toSubmodule ≤ P.toSubmodule → P = ⊤) :
    ∃ n : ℕ, ∃ e : W ≃ₗ[ZMod 2] (Fin n → Model F),
      ∀ g v, e (σ g v) = fun i => natural F g (e v i) := by
  let R := typeSpan σ (natural F)
  let P : Subrepresentation ρ := {
    toSubmodule := R.toSubmodule
    apply_mem_toSubmodule := natural_typeSpan_stable ρ σ hc }
  have hp : P = ⊤ := hgen P (show j.range ≤ R from le_iSup _ j)
  have hr : R = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    change P.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule
    exact congrArg Subrepresentation.toSubmodule hp
  have ht : isotypicComponent (ZMod 2)[Actor F] σ.asModule (natural F).asModule = ⊤ := by
    apply top_unique
    intro v _
    exact typeSpan_le_isotypicComponent σ (natural F)
      (show v ∈ R from hr.symm ▸ Submodule.mem_top)
  let C := isotypicComponent (ZMod 2)[Actor F] σ.asModule (natural F).asModule
  let c : σ.asModule ≃ₗ[(ZMod 2)[Actor F]] C :=
    Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ ht.symm)
  let : IsSemisimpleModule (ZMod 2)[Actor F] σ.asModule := IsSemisimpleModule.congr c
  let : Module.Finite (ZMod 2) σ.asModule := σ.asModuleEquiv.symm.finiteDimensional
  let : Module.Finite (ZMod 2)[Actor F] σ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) (ZMod 2)[Actor F] _
  obtain ⟨n, ⟨b⟩⟩ := (IsIsotypicOfType.of_isotypicComponent_eq_top ht).linearEquiv_fun
  let e : W ≃ₗ[ZMod 2] (Fin n → Model F) :=
    σ.asModuleEquiv.symm.trans ((b.restrictScalars (ZMod 2)).trans
      (LinearEquiv.piCongrRight fun _ => (natural F).asModuleEquiv))
  refine ⟨n, e, ?_⟩
  intro g v
  have hh := b.map_smul (MonoidAlgebra.single g (1 : ZMod 2)) (σ.asModuleEquiv.symm v)
  have hv : MonoidAlgebra.single g (1 : ZMod 2) • σ.asModuleEquiv.symm v =
      σ.asModuleEquiv.symm (σ g v) := by
    apply σ.asModuleEquiv.injective
    simp only [Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single, one_smul, LinearEquiv.apply_symm_apply]
  rw [hv] at hh
  funext i
  have hi := congrArg (natural F).asModuleEquiv (congrFun hh i)
  change (natural F).asModuleEquiv (b (σ.asModuleEquiv.symm (σ g v)) i) =
    natural F g ((natural F).asModuleEquiv (b (σ.asModuleEquiv.symm v) i))
  simpa only [Pi.smul_apply, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul] using hi


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.NaturalSum
