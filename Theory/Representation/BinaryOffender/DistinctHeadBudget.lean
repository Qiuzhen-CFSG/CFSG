module
public import Theory.Representation.SimpleHeadQuotient.Independent
public import Theory.Representation.BinaryOffender.Embedding
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Additive displacement of distinct simple subquotients

Two inequivalent simple quotients of invariant subspaces both contribute to
the fixed codimension of the ambient module. If the second head survives on
the intersection, independence of simple heads puts its full cost into the
first head's kernel. Otherwise it descends through the first subspace. The
submodule--quotient inequality adds the two costs in either case, without
splitting the ambient module or assuming disjoint subspaces.

Source application: Aschbacher--Smith 13.4.7(1iv), printed p.901: the two
graph-conjugate natural A₆ factors in the original omega module.
-/

public noncomputable section
open Representation
namespace Representation.BinaryOffender
variable {G V W E F : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

private theorem injective_budget
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
    [FiniteDimensional (ZMod 2) W]
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i) (A : Subgroup G) :
    fixedCodim ρ A ≤ fixedCodim σ A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_le_of_embedding σ ρ
    (MonoidHom.id G) i.toLinearMap hi (fun g v => (IntertwiningMap.isIntertwining _ _ i g v).symm) A

private theorem surjective_budget
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
    [FiniteDimensional (ZMod 2) V]
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) (A : Subgroup G) :
    fixedCodim σ A ≤ fixedCodim ρ A :=
  fixedCodim_le_of_equivariant_surjection ρ σ p.toLinearMap hp (IntertwiningMap.isIntertwining _ _ p) A

/-- Distinct heads of the whole module and an embedded submodule have additive cost. -/
private theorem head_subhead_budget
    (ρ : Representation (ZMod 2) G V) (α : Representation (ZMod 2) G W)
    (σ : Representation (ZMod 2) G E) (τ : Representation (ZMod 2) G F)
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    [IsIrreducible σ] [IsIrreducible τ]
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p)
    (i : α.IntertwiningMap ρ) (hi : Function.Injective i)
    (q : α.IntertwiningMap τ) (hq : Function.Surjective q)
    (hne : ¬ Nonempty (σ.Equiv τ)) (A : Subgroup G) :
    fixedCodim σ A + fixedCodim τ A ≤ fixedCodim ρ A := by
  let f := p.comp i
  let qK : f.ker.toRepresentation.IntertwiningMap τ := {
    toLinearMap := q.toLinearMap.comp f.ker.toSubmodule.subtype
    isIntertwining' g := LinearMap.ext (fun v => IntertwiningMap.isIntertwining _ _ q g v.val) }
  have hqK : Function.Surjective qK := by
    rcases IsIrreducible.surjective_or_eq_zero f with hf | hf
    · have hpair := SimpleHeadQuotient.surjective_prod_of_inequivalent_simple_quotients
        f q hf hq hne
      intro y
      obtain ⟨x,hx⟩ := hpair (0,y)
      exact ⟨⟨x,congrArg Prod.fst hx⟩,congrArg Prod.snd hx⟩
    · intro y
      obtain ⟨x,hx⟩ := hq y
      exact ⟨⟨x,by change f x = 0; rw [hf]; rfl⟩,hx⟩
  let j : f.ker.toRepresentation.IntertwiningMap p.ker.toRepresentation := {
    toLinearMap := (i.toLinearMap.comp f.ker.toSubmodule.subtype).codRestrict
      p.ker.toSubmodule (fun v => v.property)
    isIntertwining' g := LinearMap.ext (fun v => Subtype.ext (IntertwiningMap.isIntertwining _ _ i g v.val)) }
  have hj : Function.Injective j := fun x y h => Subtype.ext (hi (congrArg Subtype.val h))
  let r : p.ker.quotientRepresentation.IntertwiningMap σ := {
    toLinearMap := p.ker.toSubmodule.liftQ p.toLinearMap le_rfl
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | _ v => exact IntertwiningMap.isIntertwining _ _ p g v }
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,rfl⟩ := hp y
    exact ⟨p.ker.toSubmodule.mkQ x,rfl⟩
  have h1 := surjective_budget r hr A
  have h2 := (surjective_budget qK hqK A).trans (injective_budget j hj A)
  have h3 := fixedCodim_quotient_add_subrepresentation_le ρ p.ker A
  omega

/-- A head vanishing on the intersection is a section of the ambient quotient. -/
private theorem head_le_quotient_budget
    (ρ : Representation (ZMod 2) G V) (τ : Representation (ZMod 2) G F)
    [FiniteDimensional (ZMod 2) V]
    (P Q : Subrepresentation ρ)
    (q : Q.toRepresentation.IntertwiningMap τ) (hq : Function.Surjective q)
    (hz : ∀ x : Q.toSubmodule, x.val ∈ P → q x = 0) (A : Subgroup G) :
    fixedCodim τ A ≤ fixedCodim P.quotientRepresentation A := by
  let f : Q.toRepresentation.IntertwiningMap P.quotientRepresentation := {
    toLinearMap := P.toSubmodule.mkQ.comp Q.toSubmodule.subtype
    isIntertwining' g := rfl }
  have hk : f.toLinearMap.ker ≤ q.toLinearMap.ker := by
    intro x hx
    exact hz x ((Submodule.Quotient.mk_eq_zero P.toSubmodule).mp hx)
  let e := f.toLinearMap.quotKerEquivRange
  let r := (f.toLinearMap.ker.liftQ q.toLinearMap hk).comp e.symm.toLinearMap
  have hr (x : Q.toSubmodule) : r ⟨f x,LinearMap.mem_range_self _ x⟩ = q x := by
    change (f.toLinearMap.ker.liftQ q.toLinearMap hk) (e.symm (e (f.toLinearMap.ker.mkQ x))) = _
    rw [e.symm_apply_apply]
    rfl
  let t : f.range.toRepresentation.IntertwiningMap τ := {
    toLinearMap := r
    isIntertwining' g := by
      apply LinearMap.ext
      rintro ⟨v,x,rfl⟩
      change r ⟨f (Q.toRepresentation g x),_⟩ = τ g (r ⟨f x,_⟩)
      rw [hr,hr]
      exact IntertwiningMap.isIntertwining _ _ q g x }
  have ht : Function.Surjective t := by
    intro y
    obtain ⟨x,rfl⟩ := hq y
    exact ⟨⟨f x,LinearMap.mem_range_self _ x⟩,hr x⟩
  exact (surjective_budget t ht A).trans
    (fixedCodim_subrepresentation_le P.quotientRepresentation f.range A)

/-- Inequivalent simple quotients of two invariant subspaces contribute
additively to the fixed codimension of the whole module, without splitting. -/
theorem fixedCodim_add_le_of_distinct_submodule_heads
    (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G E) (τ : Representation (ZMod 2) G F)
    [FiniteDimensional (ZMod 2) V] [IsIrreducible σ] [IsIrreducible τ]
    (P Q : Subrepresentation ρ)
    (p : P.toRepresentation.IntertwiningMap σ) (hp : Function.Surjective p)
    (q : Q.toRepresentation.IntertwiningMap τ) (hq : Function.Surjective q)
    (hne : ¬ Nonempty (σ.Equiv τ)) (A : Subgroup G) :
    fixedCodim σ A + fixedCodim τ A ≤ fixedCodim ρ A := by
  let I := P ⊓ Q
  let j : I.toRepresentation.IntertwiningMap Q.toRepresentation := {
    toLinearMap := Submodule.inclusion (show I.toSubmodule ≤ Q.toSubmodule from inf_le_right)
    isIntertwining' g := rfl }
  let i : I.toRepresentation.IntertwiningMap P.toRepresentation := {
    toLinearMap := Submodule.inclusion (show I.toSubmodule ≤ P.toSubmodule from inf_le_left)
    isIntertwining' g := rfl }
  rcases IsIrreducible.surjective_or_eq_zero (q.comp j) with hs | hz
  · exact (head_subhead_budget P.toRepresentation I.toRepresentation σ τ p hp
      i (fun x y h => Subtype.ext (congrArg (fun z : P.toSubmodule => z.val) h)) (q.comp j) hs hne A).trans
        (fixedCodim_subrepresentation_le ρ P A)
  · have hkill (x : Q.toSubmodule) (hx : x.val ∈ P) : q x = 0 := by
      exact congrArg (fun f : I.toRepresentation.IntertwiningMap τ => f ⟨x.val,hx,x.property⟩) hz
    have h1 := surjective_budget p hp A
    have h2 := head_le_quotient_budget ρ τ P Q q hq hkill A
    have h3 := fixedCodim_quotient_add_subrepresentation_le ρ P A
    omega
/-- The same inequality for actual injective intertwining maps, avoiding a
choice of submodule coordinates in the consumer. -/
theorem fixedCodim_add_le_of_distinct_embedded_heads
    (ρ : Representation (ZMod 2) G V) (α : Representation (ZMod 2) G W)
    (β : Representation (ZMod 2) G E)
    {S₁ S₂ : Type*} [AddCommGroup S₁] [Module (ZMod 2) S₁]
    [AddCommGroup S₂] [Module (ZMod 2) S₂]
    (σ : Representation (ZMod 2) G S₁) (τ : Representation (ZMod 2) G S₂)
    [FiniteDimensional (ZMod 2) V] [IsIrreducible σ] [IsIrreducible τ]
    (i : α.IntertwiningMap ρ) (hi : Function.Injective i)
    (j : β.IntertwiningMap ρ) (hj : Function.Injective j)
    (p : α.IntertwiningMap σ) (hp : Function.Surjective p)
    (q : β.IntertwiningMap τ) (hq : Function.Surjective q)
    (hne : ¬ Nonempty (σ.Equiv τ)) (A : Subgroup G) :
    fixedCodim σ A + fixedCodim τ A ≤ fixedCodim ρ A := by
  let ei : α.Equiv i.range.toRepresentation := .mk
    (LinearEquiv.ofInjective i.toLinearMap hi)
    (fun g => LinearMap.ext (fun v => Subtype.ext
      (IntertwiningMap.isIntertwining _ _ i g v)))
  let ej : β.Equiv j.range.toRepresentation := .mk
    (LinearEquiv.ofInjective j.toLinearMap hj)
    (fun g => LinearMap.ext (fun v => Subtype.ext
      (IntertwiningMap.isIntertwining _ _ j g v)))
  exact fixedCodim_add_le_of_distinct_submodule_heads ρ σ τ i.range j.range
    (p.comp ei.symm.toIntertwiningMap) (hp.comp ei.symm.toLinearEquiv.surjective)
    (q.comp ej.symm.toIntertwiningMap) (hq.comp ej.symm.toLinearEquiv.surjective) hne A
end Representation.BinaryOffender
