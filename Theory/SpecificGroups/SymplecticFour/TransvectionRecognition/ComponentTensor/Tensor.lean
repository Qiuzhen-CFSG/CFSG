module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ComponentTensor.Schur

/-!
# The actual degree-two tensor factors

Restrict an irreducible four-dimensional product action to its first perfect
factor. A simple constituent fills the restriction isotypically. Neither
its degree nor its multiplicity can be one: perfectness excludes the former,
and the finite Schur commutant excludes the latter. Both are therefore two.
Absolute irreducibility of the constituent supplies the actual second-factor
multiplicity action and an equivariant tensor isomorphism over the original
finite field.

This proves the tensor realization used for the two-component branch of
Aschbacher--Smith G.4.9, printed pp.341--342. The action need not be irreducible
over the prime field, and no tensor equivalence is assumed.
-/

public section
noncomputable section
open scoped TensorProduct
namespace Representation.ComponentTensor
open QuadraticFourGroup.TensorClassification
variable {F G H V : Type*} [Field F] [Finite F] [Group G] [Group H]
  [Group.IsPerfect G] [Group.IsPerfect H]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A degree-four irreducible product action, nontrivial on both perfect
factors, is an actual tensor of two degree-two actions over the given field. -/
theorem exists_two_tensor (ρ : Representation F (G×H) V) [ρ.IsIrreducible]
    (hl : ρ.comp (MonoidHom.inl G H)≠1)
    (hr : ρ.comp (MonoidHom.inr G H)≠1)
    (hdim : Module.finrank F V=4) :
    ∃τ₁ : Representation F G (Fin 2→F),∃τ₂ : Representation F H (Fin 2→F),
      Nonempty (ρ.Equiv (externalTensor τ₁ τ₂)) := by
  let l : Representation F G V := ρ.comp (MonoidHom.inl G H)
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨W,hW⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional l
  let σ := W.toRepresentation
  let : σ.IsIrreducible := hW
  let : Nontrivial W.toSubmodule := Subrepresentation.irreducible_module_nontrivial σ
  let f : σ.IntertwiningMap l := .mk W.toSubmodule.subtype (by intro g; ext v; rfl)
  have hf : f≠0 := by
    obtain ⟨v,hv⟩ := exists_ne (0:W.toSubmodule)
    intro he
    apply hv
    exact Subtype.ext (congrArg (fun z : σ.IntertwiningMap l=>z v) he)
  obtain ⟨n,e,he⟩ := ProductIsotypic.exists_copy_coordinates ρ σ f hf
  have hnd : n*Module.finrank F W.toSubmodule=4 := by
    simpa [Module.finrank_pi_fintype,hdim] using e.finrank_eq.symm
  have hσ : σ≠1 := by
    intro hh
    apply hl
    ext g v
    apply e.injective
    change e (ρ (g,1) v)=e v
    rw [he]
    funext i
    change σ g (e v i)=e v i
    rw [hh]
    rfl
  have hd : 2≤Module.finrank F W.toSubmodule := by
    by_contra! hh
    exact hσ (eq_one_of_finrank_le_one σ (by omega))
  have hn : n≠1 := by
    intro hn
    have hdW : Module.finrank F W.toSubmodule=Module.finrank F V := by
      rw [hdim]
      simpa [hn] using hnd
    have hfinj : Function.Injective f := Subtype.val_injective
    have hfsurj : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdW).mp hfinj
    let ef := f.ofBijective ⟨hfinj,hfsurj⟩
    let : l.IsIrreducible := (RepEquiv.ofRepresentationEquiv ef.symm).irreducible_of_euqiv hW
    apply hr
    apply commuting_eq_one_of_irreducible l (ρ.comp (MonoidHom.inr G H))
    intro g h
    change ρ (g,1)*ρ (1,h)=ρ (1,h)*ρ (g,1)
    rw [←map_mul,←map_mul]
    simp
  have hn2 : 2≤n := by
    have hn0 : n≠0 := by intro hn0; simp [hn0] at hnd
    omega
  have hd2 : Module.finrank F W.toSubmodule=2 := by nlinarith
  let : σ.IsAbsolutelyIrreducible := absolute_of_perfect_degree_two σ hσ hd2
  obtain ⟨m,μ,⟨eT⟩⟩ := ProductIsotypic.exists_externalTensor ρ σ f hf
  have hm : m=2 := by
    have hh := eT.toLinearEquiv.finrank_eq
    rw [hdim,Module.finrank_tensorProduct,hd2] at hh
    simp only [Module.finrank_pi,Fintype.card_fin] at hh
    omega
  subst m
  let b : Module.Basis (Fin 2) F W.toSubmodule := (Module.finBasis F W.toSubmodule).reindex (finCongr hd2)
  let τ := (b.equivFun.conjAlgEquiv F).toAlgHom.toMonoidHom.comp σ
  let eσ : σ.Equiv τ := Representation.Equiv.mk b.equivFun (by
    intro g
    apply LinearMap.ext
    intro v
    change b.equivFun (σ g v)=b.equivFun (σ g (b.equivFun.symm (b.equivFun v)))
    rw [b.equivFun.symm_apply_apply])
  exact ⟨τ,μ,⟨eT.trans (externalTensorEquiv eσ (Representation.Equiv.refl μ))⟩⟩
end Representation.ComponentTensor
