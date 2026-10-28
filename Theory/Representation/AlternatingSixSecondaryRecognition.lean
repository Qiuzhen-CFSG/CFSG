module

public import Theory.Representation.AlternatingSixInvolutionDegree
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.SubrepresentationLattice

/-!
# The whole secondary A₆ module from a small even actor

An even involution costs at least two dimensions on every nontrivial binary
A₆ section. With fixed codimension at most three, a proper nonzero invariant
subspace therefore forces either a fixed submodule or a trivial quotient.
Zero fixed space and full component movement exclude these two alternatives.
When the bound is two, three conjugate involutions bound the degree by six;
the binary A₆ small-degree theorem then gives dimension four.

The original S₆ action and its literal A₆ subgroup are retained. In
particular, an equality offender of rank two satisfies the same argument as
a strict offender: strict offending and a change of marking are unnecessary.
The complete S₆ catalogue then gives one of the two literal natural models,
with an equivariant linear equivalence using the original group action.
Source: Aschbacher--Smith 12.7.20, printed p.846, using the binary A₆
displacement bounds and small-degree classification.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.AlternatingSixSecondaryRecognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
local notation "S6" => Equiv.Perm (Fin 6)
local notation "A6" => alternatingGroup (Fin 6)

private theorem alternating_irreducible
    (σ : Representation (ZMod 2) A6 V) (hf : Function.Injective σ)
    (hz : fixedSpace σ ⊤ = ⊥) (hm : subspaceCommutator σ ⊤ ⊤ = ⊤)
    (t : A6) (ht : orderOf t = 2) (hc : fixedCodim σ (zpowers t) ≤ 3) :
    IsIrreducible σ := by
  have hlo := AlternatingSixInvolutionDisplacement.displacement_lower σ hf t ht
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hlo
  have hd := fixedCodim_add_finrank σ (zpowers t)
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank (ZMod 2) V by omega)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun U => ?_⟩
  rcases AlternatingSixInvolutionDisplacement.submodule_or_quotient_trivial_of_fixedCodim_le_three
      σ U t ht (mem_zpowers t) hc with hU | hQ
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have hvz : v ∈ fixedSpace σ ⊤ := fun g =>
      congrArg Subtype.val (LinearMap.congr_fun (hU g.val) (⟨v,hv⟩ : U))
    exact hz ▸ hvz
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rw [← hm]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    exact (Submodule.Quotient.eq U.toSubmodule).mp
      (LinearMap.congr_fun (hQ g) (U.toSubmodule.mkQ v))

private theorem restricted_involution_codim_le
    (ρ : Representation (ZMod 2) S6 V) (A : Subgroup S6)
    (t : A6) (htA : t.val ∈ A) :
    fixedCodim (ρ.comp (A6).subtype) (zpowers t) ≤ fixedCodim ρ A := by
  have hfix : fixedSpace ρ A ≤ fixedSpace (ρ.comp (A6).subtype) (zpowers t) := by
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
    exact fixedSpace_antitone ρ (zpowers_le.mpr htA)
  have hdim := Submodule.finrank_mono hfix
  have h₁ := fixedCodim_add_finrank ρ A
  have h₂ := fixedCodim_add_finrank (ρ.comp (A6).subtype) (zpowers t)
  omega

/-- A small actor containing an even involution makes the whole, fixed-free,
fully moved module irreducible for the original A₆ subgroup. -/
theorem irreducible_of_small_even_actor
    (ρ : Representation (ZMod 2) S6 V) (hf : Function.Injective ρ)
    (hz : fixedSpace ρ A6 = ⊥) (hm : subspaceCommutator ρ ⊤ A6 = ⊤)
    (A : Subgroup S6) (t : S6) (ht : orderOf t = 2)
    (heven : t ∈ A6) (htA : t ∈ A) (hc : fixedCodim ρ A ≤ 3) :
    IsIrreducible (ρ.comp (A6).subtype) := by
  let b : A6 := ⟨t,heven⟩
  have hb : orderOf b = 2 :=
    (orderOf_injective (A6).subtype Subtype.coe_injective b).symm.trans ht
  apply alternating_irreducible (ρ.comp (A6).subtype) (hf.comp Subtype.coe_injective)
    _ _ b hb ((restricted_involution_codim_le ρ A b htA).trans hc)
  · simpa only [fixedSpace_comp_map, ← MonoidHom.range_eq_map, range_subtype] using hz
  · simpa only [subspaceCommutator_comp_map, ← MonoidHom.range_eq_map, range_subtype] using hm

/-- Fixed codimension at most two gives dimension four on the actual whole
module, including the even rank-two equality-offender case. -/
theorem irreducible_finrank_four_of_even_actor
    (ρ : Representation (ZMod 2) S6 V) (hf : Function.Injective ρ)
    (hz : fixedSpace ρ A6 = ⊥) (hm : subspaceCommutator ρ ⊤ A6 = ⊤)
    (A : Subgroup S6) (t : S6) (ht : orderOf t = 2)
    (heven : t ∈ A6) (htA : t ∈ A) (hc : fixedCodim ρ A ≤ 2) :
    IsIrreducible (ρ.comp (A6).subtype) ∧ Module.finrank (ZMod 2) V = 4 := by
  have hi := irreducible_of_small_even_actor ρ hf hz hm A t ht heven htA (by omega)
  let σ := ρ.comp (A6).subtype
  let : IsIrreducible σ := hi
  let b : A6 := ⟨t,heven⟩
  have hb : orderOf b = 2 :=
    (orderOf_injective (A6).subtype Subtype.coe_injective b).symm.trans ht
  have hfσ : Function.Injective σ := hf.comp Subtype.coe_injective
  have hlow := AlternatingSixInvolutionDisplacement.displacement_lower σ hfσ b hb
  have hupp := (restricted_involution_codim_le ρ A b htA).trans hc
  rw [fixedCodim_zpowers_eq_displacement_rank] at hupp
  change Module.finrank (ZMod 2) (σ b - LinearMap.id).range ≤ 2 at hupp
  have he : Module.finrank (ZMod 2) (σ b - LinearMap.id).range = 2 := by omega
  have hd := _root_.AlternatingSix.InvolutionDisplacement.finrank_le_six σ hfσ b hb he
  have hcases := _root_.AlternatingSix.BinarySmallDegrees.finrank_eq_one_or_four σ hd
  have hbound := fixedCodim_add_finrank σ (zpowers b)
  rw [fixedCodim_zpowers_eq_displacement_rank, he] at hbound
  exact ⟨hi, by omega⟩

/-- The actual whole secondary action is one of the two literal marked
natural S₆ models. The group action is unchanged in both equivalences. -/
theorem natural_models_of_even_actor
    (ρ : Representation (ZMod 2) S6 V) (hf : Function.Injective ρ)
    (hz : fixedSpace ρ A6 = ⊥) (hm : subspaceCommutator ρ ⊤ A6 = ⊤)
    (A : Subgroup S6) (t : S6) (ht : orderOf t = 2)
    (heven : t ∈ A6) (htA : t ∈ A) (hc : fixedCodim ρ A ≤ 2) :
    Nonempty (ρ.Equiv BinaryAlternatingSix.firstNatural) ∨
      Nonempty (ρ.Equiv BinaryAlternatingSix.secondNatural) := by
  obtain ⟨hi,hd⟩ := irreducible_finrank_four_of_even_actor ρ hf hz hm A t ht heven htA hc
  let : IsIrreducible (ρ.comp (A6).subtype) := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp (A6).subtype)
  let : IsIrreducible ρ := by
    rw [Representation.IsIrreducible, isSimpleOrder_iff]
    refine ⟨inferInstance, fun P => ?_⟩
    let Q : Subrepresentation (ρ.comp (A6).subtype) :=
      ⟨P.toSubmodule, fun g _ hv => P.apply_mem_toSubmodule g.val hv⟩
    rcases eq_bot_or_eq_top Q with hQ | hQ
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        (congrArg (fun W : Subrepresentation (ρ.comp (A6).subtype) => W.toSubmodule) hQ))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        (congrArg (fun W : Subrepresentation (ρ.comp (A6).subtype) => W.toSubmodule) hQ))
  rcases BinaryAlternatingSix.symmetric_classify ρ with he | he | he | he
  · obtain ⟨e⟩ := he
    have hh : Module.finrank (ZMod 2) V = 1 := e.toLinearEquiv.finrank_eq.trans (by simp)
    omega
  · exact Or.inl he
  · exact Or.inr he
  · obtain ⟨e⟩ := he
    have hh := e.toLinearEquiv.finrank_eq.trans BinaryAlternatingSix.tensor_finrank
    omega

end Representation.AlternatingSixSecondaryRecognition
