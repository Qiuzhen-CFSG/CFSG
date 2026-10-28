module

public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Quotients after discarding a summand with a prescribed simple head

Suppose two equivariant maps into a finite-dimensional representation have
ranges summing to the whole target. If every irreducible quotient of the
first source is a fixed representation S, and the target has no quotient S,
then the second map is surjective. A maximal subrepresentation containing
its range would otherwise give precisely the forbidden simple quotient.

The simple-head bridge uses the actual intersection of maximal invariant
subspaces, or equivalently an explicit unique maximal kernel. These are
conditions on the first source and its head map, not on the desired range.

This is the correct quotient-surjectivity replacement for the general
technical claim printed as Aschbacher–Smith H.6.4, p.388 of the combined
manuscript of 1 March 2004. The stronger printed conclusion that the first
summand lies in the original kernel is false. The replacement retains the
quotient reduction needed in H.6.5; it needs no restriction on the second
summand's simple quotients or composition factors.
-/

public section

open scoped MonoidAlgebra

namespace Representation.SimpleHeadQuotient

universe u
variable {k G A B S : Type*} {M : Type u}
  [Field k] [Group G] [AddCommGroup A] [Module k A]
  [AddCommGroup B] [Module k B] [AddCommGroup M] [Module k M]
  [AddCommGroup S] [Module k S]

/-- Finite-dimensional representations have maximal invariant subspaces above every proper invariant subspace. -/
theorem subrepresentation_coatomic (ρ : Representation k G M)
    [FiniteDimensional k M] : IsCoatomic (Subrepresentation ρ) := by
  let : Module.Finite k[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] ρ.asModule
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isCoatomic_iff).mpr
    inferInstance

/-- The literal quotient by a maximal invariant subspace is irreducible. -/
theorem irreducible_quotient_of_isCoatom {ρ : Representation k G M}
    (N : Subrepresentation ρ) (hN : IsCoatom N) : IsIrreducible N.quotientRepresentation := by
  have hn : N.toSubmodule ≠ ⊤ := fun he => hN.1 (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial (M ⧸ N.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hn
  refine ⟨?_⟩
  intro Q
  let T : Subrepresentation ρ := {
    toSubmodule := Q.toSubmodule.comap N.toSubmodule.mkQ
    apply_mem_toSubmodule g v hv := Q.apply_mem_toSubmodule g hv }
  have hNT : N ≤ T := by
    intro v hv
    change N.toSubmodule.mkQ v ∈ Q
    have hz : N.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact Q.toSubmodule.zero_mem
  rcases eq_or_lt_of_le hNT with he | hlt
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro w hw
    obtain ⟨v, rfl⟩ := N.toSubmodule.mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).mpr (show v ∈ N from he.symm ▸ hw)
  · right
    have ht : T = ⊤ := hN.2 T hlt
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    obtain ⟨v, rfl⟩ := N.toSubmodule.mkQ_surjective w
    exact (show v ∈ T from ht.symm ▸ (show v ∈ (⊤ : Subrepresentation ρ) from by trivial))

/-- A surjection onto an irreducible representation has maximal kernel. -/
theorem isCoatom_ker_of_surjective
    {α : Representation k G A} {σ : Representation k G S} [IsIrreducible σ]
    (p : α.IntertwiningMap σ) (hp : Function.Surjective p) : IsCoatom p.ker := by
  apply (Subrepresentation.subrepresentationSubmoduleOrderIso.isCoatom_iff p.ker).mp
  exact LinearMap.isCoatom_ker_of_surjective
    (f := IntertwiningMap.equivLinearMapAsModule α σ p) hp

set_option backward.isDefEq.respectTransparency false in
private theorem equiv_of_surjective_of_ker_eq
    {α : Representation k G A} {ρ : Representation k G M} {σ : Representation k G S}
    (f : α.IntertwiningMap ρ) (hf : Function.Surjective f)
    (p : α.IntertwiningMap σ) (hp : Function.Surjective p)
    (hker : f.ker = p.ker) : Nonempty (ρ.Equiv σ) := by
  let ef := f.toLinearMap.quotKerEquivOfSurjective hf
  let ep := p.toLinearMap.quotKerEquivOfSurjective hp
  let e := ef.symm.trans ((Submodule.quotEquivOfEq _ _
    (congrArg Subrepresentation.toSubmodule hker)).trans ep)
  have he (x : A) : e (f x) = p x := by
    change ep (Submodule.quotEquivOfEq _ _ _ (ef.symm (f x))) = p x
    have hex : ef.symm (f x) = Submodule.Quotient.mk x := by
      simpa only [ef, IntertwiningMap.toLinearMap_apply] using
        LinearMap.quotKerEquivOfSurjective_symm_apply (f := f.toLinearMap) hf x
    rw [hex, Submodule.quotEquivOfEq_mk]
    rfl
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro g
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  change e (ρ g (f x)) = σ g (e (f x))
  rw [← IntertwiningMap.isIntertwining α ρ f, he,
    IntertwiningMap.isIntertwining α σ p, he]

/-- A surjective head map with a unique maximal kernel identifies every irreducible quotient with its target. -/
theorem unique_irreducible_quotient_of_unique_maximal_kernel
    {α : Representation k G A} {ρ : Representation k G M} {σ : Representation k G S}
    [IsIrreducible ρ]
    (p : α.IntertwiningMap σ) (hp : Function.Surjective p)
    (hmax : ∀ N : Subrepresentation α, IsCoatom N → N = p.ker)
    (f : α.IntertwiningMap ρ) (hf : Function.Surjective f) : Nonempty (ρ.Equiv σ) :=
  equiv_of_surjective_of_ker_eq f hf p hp
    (hmax f.ker (isCoatom_ker_of_surjective f hf))

/-- A simple head map whose kernel is the intersection of maximal invariant subspaces identifies every irreducible quotient. -/
theorem unique_irreducible_quotient_of_simple_head
    {α : Representation k G A} {ρ : Representation k G M} {σ : Representation k G S}
    [IsIrreducible ρ] [IsIrreducible σ]
    (p : α.IntertwiningMap σ) (hp : Function.Surjective p)
    (hrad : p.ker = sInf {N : Subrepresentation α | IsCoatom N})
    (f : α.IntertwiningMap ρ) (hf : Function.Surjective f) : Nonempty (ρ.Equiv σ) := by
  apply unique_irreducible_quotient_of_unique_maximal_kernel p hp ?_ f hf
  intro N hN
  have hle : p.ker ≤ N := by rw [hrad]; exact sInf_le hN
  rcases eq_or_lt_of_le hle with he | hlt
  · exact he.symm
  · exact False.elim (hN.1 ((isCoatom_ker_of_surjective p hp).2 N hlt))

/-- If two equivariant images span the target, the target excludes the unique irreducible quotient of the first source, and the target is finite-dimensional, then the second map is surjective. -/
theorem surjective_right_of_unique_irreducible_quotient
    [FiniteDimensional k M]
    {α : Representation k G A} {β : Representation k G B}
    {ρ : Representation k G M} {σ : Representation k G S}
    (a : α.IntertwiningMap ρ) (b : β.IntertwiningMap ρ)
    (hspan : LinearMap.range a.toLinearMap ⊔ LinearMap.range b.toLinearMap = ⊤)
    (hhead : ∀ (T : Type u) [AddCommGroup T] [Module k T]
      (τ : Representation k G T), IsIrreducible τ →
      ∀ f : α.IntertwiningMap τ, Function.Surjective f → Nonempty (τ.Equiv σ))
    (hno : ∀ f : ρ.IntertwiningMap σ, ¬ Function.Surjective f) :
    Function.Surjective b := by
  let : IsCoatomic (Subrepresentation ρ) := subrepresentation_coatomic ρ
  rcases eq_top_or_exists_le_coatom b.range with hb | ⟨N, hN, hbN⟩
  · exact LinearMap.range_eq_top.mp (congrArg Subrepresentation.toSubmodule hb)
  let q : ρ.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  have hq : Function.Surjective q := N.toSubmodule.mkQ_surjective
  have hqa : Function.Surjective (q.comp a) := by
    intro w
    obtain ⟨m, rfl⟩ := hq w
    have hm : m ∈ LinearMap.range a.toLinearMap ⊔ LinearMap.range b.toLinearMap := by
      rw [hspan]
      trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hm
    obtain ⟨v, rfl⟩ := hx
    have hyq : q y = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (hbN hy)
    refine ⟨v, ?_⟩
    change q (a v) = q m
    rw [← hxy, map_add, hyq, add_zero]
    rfl
  obtain ⟨e⟩ := hhead _ N.quotientRepresentation
    (irreducible_quotient_of_isCoatom N hN) (q.comp a) hqa
  exact False.elim (hno (e.toIntertwiningMap.comp q) (e.toLinearEquiv.surjective.comp hq))

/-- A quotient of a product is already a quotient of its second factor when the target excludes the unique irreducible quotient of the first factor. -/
theorem surjective_inr_of_unique_irreducible_quotient
    [FiniteDimensional k M]
    {α : Representation k G A} {β : Representation k G B}
    {ρ : Representation k G M} {σ : Representation k G S}
    (q : (α.prod β).IntertwiningMap ρ) (hq : Function.Surjective q)
    (hhead : ∀ (T : Type u) [AddCommGroup T] [Module k T]
      (τ : Representation k G T), IsIrreducible τ →
      ∀ f : α.IntertwiningMap τ, Function.Surjective f → Nonempty (τ.Equiv σ))
    (hno : ∀ f : ρ.IntertwiningMap σ, ¬ Function.Surjective f) :
    Function.Surjective (q.comp (IntertwiningMap.inr k α β)) := by
  apply surjective_right_of_unique_irreducible_quotient
    (q.comp (IntertwiningMap.inl k α β)) (q.comp (IntertwiningMap.inr k α β)) ?_ hhead hno
  apply Submodule.eq_top_iff'.mpr
  intro m
  obtain ⟨⟨x, y⟩, rfl⟩ := hq m
  refine Submodule.mem_sup.mpr ⟨q (x, 0), ⟨x, rfl⟩, q (0, y), ⟨y, rfl⟩, ?_⟩
  rw [← map_add]
  simp

end Representation.SimpleHeadQuotient
