module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.Configuration

/-!
# The natural S₃ quotient summand in B.5.8

Faithfulness restricts to the moved plane because the complementary space
is fixed. Its global fixed-quotient image is equivariantly the same plane,
so the binary-plane recognition supplies the actual SL₂(2) identification.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.8, p.106.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
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


/-- The first factor is the literal natural SL₂(2) quotient summand. -/
theorem Configuration.firstCase [Module.Finite (ZMod 2) V] {A : Subgroup D} (c : Configuration ρ A)
    (hf : Function.Injective ρ) : SourceFactorCase ρ c.first c.firstSpace := by
  let U := c.firstSpace
  have hd : Disjoint U.toSubmodule ρ.invariants :=
    c.decomposition.disjoint.mono_right c.invariants_le_second
  let e := quotientImageEquivOfDisjoint ρ U hd
  let τ := (((fixed ρ).quotientImage U).toRepresentation.comp c.first.subtype)
  have hU : Function.Injective (U.toRepresentation.comp c.first.subtype) := by
    apply faithful_on_supplement ρ hf c.first c.secondSpace U
    · exact c.decomposition.symm.sup_eq_top
    · exact c.secondSpace_eq.le
  have hequiv (g : c.first) (v : U.toSubmodule) :
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
  let eg : c.first ≃* Equiv.Perm (Fin 3) := c.firstEquiv
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
  exact .natural c.firstSpace_eq hn

end CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
