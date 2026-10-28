module
public import Theory.Representation.ConjugateRep
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.Order.Interval.Set.OrderIso
/-!
# Semisimplicity of a normal subgroup's ambient span

If semisimple submodules for a normal subgroup generate a representation under
its full actor group, then restriction to the normal subgroup is semisimple.
Conjugation gives order isomorphisms on invariant-subspace lattices, so preserves
semisimplicity of each submodule; their sum is the whole representation.

The argument is the semisimple-span step of Clifford theory, requiring neither
finite dimension nor an irreducible ambient representation. It applies to the
Borel-fixed generating seeds in Aschbacher--Smith, 13.6, printed p.918.
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra

namespace Subrepresentation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
/-- Semisimplicity of a subrepresentation as its group-algebra submodule. -/
abbrev IsSemisimple {ρ : Representation k G V} (S : Subrepresentation ρ) : Prop :=
  IsSemisimpleModule k[G] S.asSubmodule
/-- Pull back an invariant subspace along a homomorphism of actor groups. -/
def compActors {ρ : Representation k G V} (S : Subrepresentation ρ)
    {D : Type*} [Group D] (f : D →* G) : Subrepresentation (ρ.comp f) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule d _ hv := S.apply_mem_toSubmodule (f d) hv
end Subrepresentation

namespace Representation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

private theorem semisimple_orderIso {R M T N : Type*}
    [Ring R] [AddCommGroup M] [Module R M]
    [Ring T] [AddCommGroup N] [Module T N]
    (e : Submodule R M ≃o Submodule T N) (P : Submodule R M)
    (hP : IsSemisimpleModule R P) : IsSemisimpleModule T (e P) := by
  rw [isSemisimpleModule_iff] at hP ⊢
  exact (e P).mapIic.complementedLattice_iff.mpr
    ((OrderIso.Iic e P).complementedLattice_iff.mp (P.mapIic.complementedLattice_iff.mp hP))

/-- Conjugating a normal-subgroup submodule preserves semisimplicity. -/
theorem conjugate_semisimple (ρ : Representation k G V) (D : Subgroup G) [D.Normal]
    (S : Subrepresentation (ρ.comp D.subtype)) (g : G)
    (hS : IsSemisimpleModule k[D] S.asSubmodule) :
    IsSemisimpleModule k[D]
      (conjugateSubrepresentationOrderIso ρ D g S).asSubmodule := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp D.subtype)
  exact semisimple_orderIso (e.symm.trans ((conjugateSubrepresentationOrderIso ρ D g).trans e))
    S.asSubmodule hS

/-- Semisimple normal-subgroup submodules whose ambient orbit spans the whole
representation make its restriction semisimple. -/
theorem normal_restriction_semisimple_of_generating_family
    (ρ : Representation k G V) (D : Subgroup G) [D.Normal]
    {ι : Type*} (S : ι → Subrepresentation (ρ.comp D.subtype))
    (hS : ∀ i, IsSemisimpleModule k[D] (S i).asSubmodule)
    (hgen : ∀ U : Subrepresentation ρ,
      (∀ i, (S i).toSubmodule ≤ U.toSubmodule) → U = ⊤) :
    IsSemisimpleModule k[D] (Representation.asModule (ρ.comp D.subtype)) := by
  let c := conjugateSubrepresentationOrderIso ρ D
  let Q : Subrepresentation (ρ.comp D.subtype) := ⨆ i, ⨆ g : G, c g (S i)
  have hstable (x : G) : c x Q ≤ Q := by
    simp only [Q, OrderIso.map_iSup]
    refine iSup_le fun i => iSup_le fun g => ?_
    rw [← conjugateSubrepresentationOrderIso_mul]
    exact le_iSup_of_le i (le_iSup_of_le (x*g) le_rfl)
  let U : Subrepresentation ρ := {
    toSubmodule := Q.toSubmodule
    apply_mem_toSubmodule x v hv := by
      have hm : ρ x v ∈ Q.toSubmodule.map (ρ x) := ⟨v,hv,rfl⟩
      rw [← conjugateSubrepresentationOrderIso_toSubmodule] at hm
      exact hstable x hm }
  have htop : Q = ⊤ := by
    have hu := hgen U (fun i => ?_)
    · apply Subrepresentation.toSubmodule_injective
      change U.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule
      exact congrArg Subrepresentation.toSubmodule hu
    intro v hv
    apply (show c 1 (S i) ≤ Q from le_iSup_of_le i (le_iSup_of_le 1 le_rfl))
    change v ∈ (conjugateSubrepresentationOrderIso ρ D 1 (S i)).toSubmodule
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    simpa only [map_one, Module.End.one_eq_id, Submodule.map_id] using hv
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp D.subtype)
  apply isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun ig : ι × G => e (c ig.2 (S ig.1)))
  · rintro ⟨i,g⟩
    exact conjugate_semisimple ρ D (S i) g (hS i)
  · have hh := congrArg e htop
    dsimp only [Q] at hh
    rw [e.map_iSup,e.map_top] at hh
    simp_rw [e.map_iSup] at hh
    rw [← hh]
    exact le_antisymm (iSup_le fun ig => le_iSup_of_le ig.1 (le_iSup_of_le ig.2 le_rfl))
      (iSup_le fun i => iSup_le fun g => le_iSup_of_le (i,g) le_rfl)

/-- Surjective actor changes preserve semisimplicity in both directions. -/
theorem semisimple_comp_iff_of_surjective (ρ : Representation k G V)
    {D : Type*} [Group D] (f : D →* G) (hf : Function.Surjective f) :
    IsSemisimpleModule k[D] (Representation.asModule (ρ.comp f)) ↔
      IsSemisimpleModule k[G] ρ.asModule := by
  let e : Subrepresentation ρ ≃o Subrepresentation (ρ.comp f) := {
    toFun S := ⟨S.toSubmodule, fun x _ hv => S.apply_mem_toSubmodule (f x) hv⟩
    invFun S := ⟨S.toSubmodule, fun x _ hv => by
      obtain ⟨y,rfl⟩ := hf x
      exact S.apply_mem_toSubmodule y hv⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_rel_iff' := Iff.rfl }
  rw [← isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    ← isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  exact e.complementedLattice_iff.symm

/-- Pulling a subrepresentation back through a surjective change of actors
preserves semisimplicity of its actual submodule. -/
theorem compActors_semisimple (ρ : Representation k G V)
    {D : Type*} [Group D] (f : D →* G) (hf : Function.Surjective f)
    (S : Subrepresentation ρ) (hS : S.IsSemisimple) :
    (S.compActors f).IsSemisimple := by
  let e : Subrepresentation ρ ≃o Subrepresentation (ρ.comp f) := {
    toFun U := U.compActors f
    invFun U := ⟨U.toSubmodule, fun x _ hv => by
      obtain ⟨y,rfl⟩ := hf x
      exact U.apply_mem_toSubmodule y hv⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_rel_iff' := Iff.rfl }
  let a := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let b := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp f)
  exact semisimple_orderIso (a.symm.trans (e.trans b)) S.asSubmodule hS

variable {W : Type*} [AddCommGroup W] [Module k W]

set_option backward.isDefEq.respectTransparency false in
/-- The image of a semisimple representation is a semisimple subrepresentation. -/
theorem intertwining_range_semisimple (ρ : Representation k G V) (σ : Representation k G W)
    (f : ρ.IntertwiningMap σ) [IsSemisimpleModule k[G] ρ.asModule] :
    IsSemisimpleModule k[G] f.range.asSubmodule := by
  let l := IntertwiningMap.equivLinearMapAsModule ρ σ f
  have hr : l.range = f.range.asSubmodule := by
    ext x
    rfl
  rw [← hr]
  exact IsSemisimpleModule.range l

end Representation
