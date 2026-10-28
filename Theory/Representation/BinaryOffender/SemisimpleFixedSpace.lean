module
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Theory.Representation.SubrepresentationLattice

/-!
# Fixed vectors in semisimple representations

An isotypic semisimple module is a direct sum of copies of its simple type.
The coordinate maps preserve every scalar action, so vanishing of fixed
vectors in the type implies vanishing in the whole isotypic module.
The same coordinate argument lifts fixed-space inclusions from all actual
simple subrepresentations. These are the linear fixed-space steps used in
Aschbacher–Smith F.9.18(3–4).
-/

public noncomputable section
namespace Representation.BinaryOffender
open scoped MonoidAlgebra

/-- Simultaneous scalar-fixed vectors vanish in a semisimple isotypic module
when they vanish in its type. -/
theorem eq_zero_of_isIsotypicOfType
    {R M N α : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsSemisimpleModule R M]
    (h : IsIsotypicOfType R M N) (r : α → R)
    (hN : ∀ n : N, (∀ a, r a • n = n) → n = 0)
    (m : M) (hm : ∀ a, r a • m = m) : m = 0 := by
  obtain ⟨ι, ⟨e⟩⟩ := h.linearEquiv_finsupp
  apply e.injective
  rw [map_zero]
  ext i
  apply hN
  intro a
  have he := congrArg (fun x => e x i) (hm a)
  simpa only [map_smul, Finsupp.smul_apply] using he

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A subgroup has no fixed vectors on a semisimple representation when it
has no fixed vectors on its common simple type. -/
theorem fixedSpace_eq_bot_of_isIsotypicOfType
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    [IsSemisimpleRepresentation ρ]
    (h : IsIsotypicOfType (ZMod 2)[G] ρ.asModule σ.asModule)
    (B : Subgroup G) (hB : fixedSpace σ B = ⊥) : fixedSpace ρ B = ⊥ := by
  let : IsSemisimpleModule (ZMod 2)[G] ρ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp inferInstance
  apply le_bot_iff.mp
  intro v hv
  change v = 0
  apply ρ.asModuleEquiv.symm.injective
  rw [map_zero]
  apply eq_zero_of_isIsotypicOfType h (fun b : B => MonoidAlgebra.of (ZMod 2) G b)
  · intro w hw
    apply σ.asModuleEquiv.injective
    rw [map_zero]
    apply hB.le
    intro b
    apply σ.asModuleEquiv.symm.injective
    change σ.asModuleEquiv.symm (σ b (σ.asModuleEquiv w)) =
      σ.asModuleEquiv.symm (σ.asModuleEquiv w)
    rw [asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
    exact hw b
  · intro b
    rw [← asModuleEquiv_symm_map_rho]
    exact congrArg ρ.asModuleEquiv.symm (hv b)

private theorem fixed_of_semisimple_simples
    {R M α β : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] (r : α → R) (s : β → R)
    (h : ∀ S : Submodule R M, IsSimpleModule R S →
      ∀ n : S, (∀ a, r a • n = n) → ∀ b, s b • n = n)
    (m : M) (hm : ∀ a, r a • m = m) (b : β) : s b • m = m := by
  obtain ⟨t, e, _, ht⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R M
  apply e.injective
  apply DFinsupp.ext
  intro i
  have hi := h i.val (ht i) (e m i) (fun a => ?_) b
  · simpa only [map_smul, DFinsupp.smul_apply] using hi
  · simpa only [map_smul, DFinsupp.smul_apply] using
      congrArg (fun x => e x i) (hm a)

/-- Fixed-space inclusions on all actual simple subrepresentations extend
to a semisimple representation by its invariant direct-sum decomposition. -/
theorem fixedSpace_le_of_semisimple_simples
    (ρ : Representation (ZMod 2) G V) [IsSemisimpleRepresentation ρ]
    (B H : Subgroup G)
    (h : ∀ S : Subrepresentation ρ, IsIrreducible S.toRepresentation →
      fixedSpace S.toRepresentation B ≤ fixedSpace S.toRepresentation H) :
    fixedSpace ρ B ≤ fixedSpace ρ H := by
  let : IsSemisimpleModule (ZMod 2)[G] ρ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp inferInstance
  intro v hv g
  apply ρ.asModuleEquiv.symm.injective
  change ρ.asModuleEquiv.symm (ρ g v) = ρ.asModuleEquiv.symm v
  rw [asModuleEquiv_symm_map_rho]
  apply fixed_of_semisimple_simples
    (fun b : B => MonoidAlgebra.of (ZMod 2) G b)
    (fun k : H => MonoidAlgebra.of (ZMod 2) G k)
  · intro S hS n hn k
    let T : Subrepresentation ρ := Subrepresentation.ofSubmodule' S
    have hi : IsIrreducible T.toRepresentation := by
      apply (Subrepresentation.irreducible_iff_isAtom T).mpr
      exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff T).mp
        (isSimpleModule_iff_isAtom.mp hS)
    have hfix : (⟨ρ.asModuleEquiv n.val, n.property⟩ : T.toSubmodule) ∈
        fixedSpace T.toRepresentation B := by
      intro b
      apply Subtype.ext
      change ρ b (ρ.asModuleEquiv n.val) = ρ.asModuleEquiv n.val
      have he := congrArg (fun x : S => ρ.asModuleEquiv x.val) (hn b)
      simpa only [SetLike.val_smul, asModuleEquiv_map_smul,
        asAlgebraHom_of] using he
    have he := congrArg Subtype.val (h T hi hfix k)
    change ρ k (ρ.asModuleEquiv n.val) = ρ.asModuleEquiv n.val at he
    apply Subtype.ext
    apply ρ.asModuleEquiv.injective
    simpa only [SetLike.val_smul, asModuleEquiv_map_smul, asAlgebraHom_of] using he
  · intro b
    rw [← asModuleEquiv_symm_map_rho]
    exact congrArg ρ.asModuleEquiv.symm (hv b)

/-- If every actual simple constituent is trivial or has no Borel-fixed
vectors, Borel-fixed vectors on the semisimple module are group-fixed. -/
theorem fixedSpace_le_top_of_semisimple_alternatives
    (ρ : Representation (ZMod 2) G V) [IsSemisimpleRepresentation ρ]
    (B : Subgroup G)
    (h : ∀ S : Subrepresentation ρ, IsIrreducible S.toRepresentation →
      S.toSubmodule ≤ fixedSpace ρ ⊤ ∨ fixedSpace S.toRepresentation B = ⊥) :
    fixedSpace ρ B ≤ fixedSpace ρ ⊤ := by
  apply fixedSpace_le_of_semisimple_simples ρ B ⊤
  intro S hs
  rcases h S hs with ht | hz
  · intro v _ g
    exact Subtype.ext (ht v.property g)
  · rw [hz]
    exact bot_le

end Representation.BinaryOffender
