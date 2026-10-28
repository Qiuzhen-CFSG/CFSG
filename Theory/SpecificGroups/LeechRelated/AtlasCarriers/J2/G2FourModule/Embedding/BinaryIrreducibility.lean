module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule
public import Theory.Representation.G2NaturalFaithfulness
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.BinaryIrreducibility.ScalarRestriction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.BinaryIrreducibility.NaturalForm
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.BinaryIrreducibility.FixedVectors
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.BinaryIrreducibility.SmallDegree
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Binary irreducibility of every embedded Hall--Janko natural module

Simplicity and the small general-linear-group orders force every invariant
F₄-subspace of dimension at most three to be fixed pointwise. Such a subspace
is zero: the nonzero-vector stabilizers in G₂(4) are too small to contain J₂.
The invariant nondegenerate polar form takes any larger proper subspace to
a nonzero subspace of dimension at most three. Thus the F₄ action is irreducible.

A proper irreducible binary submodule then has a disjoint scalar translate,
so its binary dimension is at most six. Its F₄-span is the whole module, making
its action faithful. The order obstruction for GL(n,2), n ≤ 6, excludes it.
The result applies to every injective homomorphism of the actual carrier and
to the literal action of every `MarkedEmbedding`. Only inherited simplicity
is assumed; no embedding existence or arbitrary-module recognition is used.

Source: Aschbacher--Smith, K.4.5, printed p.460/PDF p.471. The imported concrete
models and order certificates retain their ATLAS attribution and license.
-/

public noncomputable section
namespace Sporadic.LeechRelated.J2.G2FourModule
namespace Embedding
open BinaryIrreducibility

variable [IsSimpleGroup Carrier]

private theorem small_subrepresentation_eq_bot
    (f : Carrier →* M) (hf : Function.Injective f)
    (S : Subrepresentation ((Atlas.G2.Natural.action F).comp f))
    (hd : Module.finrank F S.toSubmodule ≤ 3) : S = ⊥ := by
  have hker : S.toRepresentation.ker = ⊤ :=
    (MonoidHom.normal_ker S.toRepresentation).eq_bot_or_eq_top.resolve_left (fun h =>
      not_injective_four_of_finrank_le_three S.toRepresentation hd
        (S.toRepresentation.ker_eq_bot_iff.mp h))
  have htriv (j : Carrier) : S.toRepresentation j = 1 :=
    show j ∈ S.toRepresentation.ker from hker ▸ Subgroup.mem_top j
  apply Subrepresentation.toSubmodule_injective
  apply eq_bot_iff.mpr
  intro v hv
  exact fixed_vector_eq_zero f hf v fun j => by
    have h := congrArg Subtype.val (LinearMap.congr_fun (htriv j) ⟨v, hv⟩)
    exact h

/-- Every injective copy of the actual simple J₂ carrier acts irreducibly on
the six-dimensional natural F₄ quotient. -/
theorem natural_four_irreducible (f : Carrier →* M) (hf : Function.Injective f) :
    Representation.IsIrreducible ((Atlas.G2.Natural.action F).comp f) := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank F V by simp [F, V])
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  by_contra hproper
  have hStop : S.toSubmodule ≠ ⊤ :=
    fun h => hproper (Subrepresentation.toSubmodule_injective h)
  by_cases hd : Module.finrank F S.toSubmodule ≤ 3
  · exact hS (small_subrepresentation_eq_bot f hf S hd)
  let B := Atlas.G2.Natural.InvariantPolar.form F
  let P : Subrepresentation ((Atlas.G2.Natural.action F).comp f) := {
    toSubmodule := B.orthogonal S.toSubmodule
    apply_mem_toSubmodule := by
      intro j y hy x hx
      have he := Atlas.G2.Natural.InvariantPolar.form_invariant F (f j)
        (Atlas.G2.Natural.action F (f j)⁻¹ x) y
      rw [Representation.self_inv_apply] at he
      change Atlas.G2.Natural.InvariantPolar.form F x
        (Atlas.G2.Natural.action F (f j) y) = 0
      rw [he]
      apply hy
      simpa only [MonoidHom.comp_apply, map_inv] using S.apply_mem_toSubmodule j⁻¹ hx }
  have hdim : Module.finrank F P.toSubmodule = 6 - Module.finrank F S.toSubmodule := by
    change Module.finrank F (B.orthogonal S.toSubmodule) = _
    exact (LinearMap.BilinForm.finrank_orthogonal
      (Atlas.G2.Natural.InvariantPolar.form_nondegenerate F) S.toSubmodule).trans
      (by rw [Atlas.G2.Natural.finrank_space])
  have hsmall : Module.finrank F P.toSubmodule ≤ 3 := by omega
  have hP := small_subrepresentation_eq_bot f hf P hsmall
  have hz : Module.finrank F P.toSubmodule = 0 := by
    rw [hP]
    exact finrank_bot F (Atlas.G2.Natural.Space F)
  have hlt := Submodule.finrank_lt hStop
  rw [Atlas.G2.Natural.finrank_space] at hlt
  omega

/-- Restriction of the natural action through any injective J₂ homomorphism
remains irreducible over the binary prime field. -/
theorem natural_binary_irreducible (f : Carrier →* M) (hf : Function.Injective f) :
    Representation.IsIrreducible
      ((Atlas.G2.Natural.BinarySemilinear.innerRepresentation F).comp f) := by
  let : Representation.IsIrreducible ((Atlas.G2.Natural.action F).comp f) :=
    natural_four_irreducible f hf
  let : FiniteDimensional (ZMod 2) V :=
    Module.Finite.equiv (Atlas.G2.Natural.BinarySemilinear.coordinatesEquiv F).symm
  apply Representation.irreducible_of_scalar_irreducible_of_no_small_faithful
    ((Atlas.G2.Natural.action F).comp f)
    ((Atlas.G2.Natural.BinarySemilinear.innerRepresentation F).comp f)
    (fun j v => Atlas.G2.Natural.BinarySemilinear.representation_inner F (f j) v)
    ((Atlas.G2.Natural.action_injective F).comp hf)
  intro S hd
  have hd' : 2 * Module.finrank (ZMod 2) S.toSubmodule ≤ 12 :=
    hd.trans_eq Atlas.G2.Natural.BinarySemilinear.finrank_four
  exact not_injective_binary_of_finrank_le_six S.toRepresentation (by omega)

end Embedding

namespace MarkedEmbedding
/-- Literal consumer for every marking; no separate irreducibility premise remains. -/
theorem innerRepresentation_irreducible [IsSimpleGroup Carrier] (d : MarkedEmbedding) :
    Representation.IsIrreducible d.innerRepresentation :=
  Embedding.natural_binary_irreducible d.inner d.inner_injective
end MarkedEmbedding
end Sporadic.LeechRelated.J2.G2FourModule
