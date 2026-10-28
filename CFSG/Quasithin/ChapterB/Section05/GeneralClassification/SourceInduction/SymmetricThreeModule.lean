module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModuleContract
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ModuleDecomposition
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.PairRecognition.Model

/-!
# Extracting the S₃ factor module in B.5.8 and B.5.11

The specified two-dimensional moved space is faithful because its complementary
summand is fixed. Passing to its image modulo the global fixed space is an
actual equivariant linear isomorphism. The existing binary-plane recognition
then identifies this faithful action with the natural SL₂(2) action, including
the group isomorphism and intertwiner. This proves the entire S₃ branch of the
common factor-module output, with no earlier-source input.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.6(2), B.5.8
and B.5.11, printed pp.105–109.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

private noncomputable def quotientImageEquivOfDisjoint (U : Subrepresentation ρ)
    (hd : Disjoint U.toSubmodule ρ.invariants) :
    U.toSubmodule ≃ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule := by
  let f : U.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule := {
    toFun := fun v => ⟨ρ.invariants.mkQ v, ⟨v, v.property, rfl⟩⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have hmem : (v : V) ∈ ρ.invariants :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
    exact Subtype.ext ((disjoint_iff.mp hd).le ⟨v.property, hmem⟩)
  · rintro ⟨q, v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

/-- The complete S₃ branch of factor extraction on the literal moved space
and its image in V/C_V(D). Faithfulness is the original action's hypothesis. -/
theorem SymmetricThreeCase.factor_module [Finite D] [Module.Finite (ZMod 2) V]
    (c : SymmetricThreeCase ρ) (hf : Function.Injective ρ) :
    Nonempty (FactorModuleConclusion ρ) := by
  let U := (MovedSection.ofNormal ρ ⊤).space
  have hu : U.toSubmodule = moved ρ ⊤ := rfl
  have hd : Disjoint U.toSubmodule ρ.invariants := hu ▸ c.decomposition.disjoint
  let e := quotientImageEquivOfDisjoint ρ U hd
  let τ := (((fixed ρ).quotientImage U).toRepresentation.comp (⊤ : Subgroup D).subtype)
  have hU : Function.Injective (U.toRepresentation.comp (⊤ : Subgroup D).subtype) := by
    apply faithful_on_supplement ρ hf ⊤ (fixed ρ) U
    · change ρ.invariants ⊔ U.toSubmodule = ⊤
      rw [hu, sup_comm]
      exact c.decomposition.sup_eq_top
    · intro v hv g
      exact hv g
  have hequiv (g : (⊤ : Subgroup D)) (v : U.toSubmodule) :
      e (U.toRepresentation g v) = τ g (e v) := rfl
  have ht : Function.Injective τ := by
    intro a b hab
    apply hU
    apply LinearMap.ext
    intro v
    apply e.injective
    exact (hequiv a v).trans ((LinearMap.congr_fun hab (e v)).trans (hequiv b v).symm)
  have hdim : Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule = 2 := by
    rw [← e.finrank_eq]
    exact c.dimension
  let eg : (⊤ : Subgroup D) ≃* Equiv.Perm (Fin 3) := Subgroup.topEquiv.trans c.equiv
  let t := eg.symm (Equiv.swap 0 1)
  let u := eg.symm (Equiv.swap 1 2)
  have htt : t * t = 1 := by
    apply eg.injective
    simp only [map_mul, map_one, t, MulEquiv.apply_symm_apply, Equiv.swap_mul_self]
  have huu : u * u = 1 := by
    apply eg.injective
    simp only [map_mul, map_one, u, MulEquiv.apply_symm_apply, Equiv.swap_mul_self]
  have htn : t ≠ 1 := by
    intro he
    have hh := congrArg eg he
    have hn : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
    apply hn
    simpa only [t, MulEquiv.apply_symm_apply, map_one] using hh
  have hun : u ≠ 1 := by
    intro he
    have hh := congrArg eg he
    have hn : (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
    apply hn
    simpa only [u, MulEquiv.apply_symm_apply, map_one] using hh
  have htu : t ≠ u := by
    intro he
    have hh := congrArg eg he
    have hn : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ≠ Equiv.swap 1 2 := by decide
    apply hn
    simpa only [t, u, MulEquiv.apply_symm_apply] using hh
  obtain ⟨a, f, ha⟩ := Glauberman.BlockConstruction.PairRecognition.exists_natural_model
    τ ht hdim t u htt huu htn hun htu
  have hn : FactorNatural τ := .linearTwo BinaryField.two ⟨⟨a, f, ha⟩⟩
  exact ⟨⟨U, hu ▸ c.decomposition.sup_eq_top, .natural hu hn⟩⟩

end CFSG.Quasithin.ChapterB.SourceInduction
