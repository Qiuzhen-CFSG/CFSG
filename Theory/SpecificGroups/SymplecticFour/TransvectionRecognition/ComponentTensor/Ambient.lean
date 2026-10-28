module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ComponentTensor.Quadratic
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.QuadraticExclusion
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical
public import Theory.Representation.Quotient
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The quadratic form of an embedded component product

Two commuting nontrivial perfect subgroups generating an irreducible
symplectic four-space give the literal determinant refinement of its
standard alternating form. Uniqueness of the invariant refinement makes
the full symplectic normalizer preserve that same quadratic form. The
moving opposition-pair geometry therefore excludes this component product.
Source: Aschbacher--Smith G.4.9, printed pp.341--342.
-/

public section
noncomputable section
open Subgroup Module Matrix
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ComponentTensor
variable {F:Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem subgroup_action_faithful (H:Subgroup (Sp F)) :
    Function.Injective ((Representation.symplecticNatural 2).comp H.subtype) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun f:Module.End F (Vector F)=>f (Pi.single j 1) i) he
  change ((g:Sp F).val *ᵥ Pi.single j 1) i=((h:Sp F).val *ᵥ Pi.single j 1) i at hh
  simpa using hh

omit [CharP F 2] in
/-- The actual irreducible product of two commuting nontrivial perfect
symplectic subgroups has a quadratic refinement of the original form. -/
theorem exists_quadratic_of_commuting_perfect_factors
    (H:Subgroup (Sp F))
    (hi:Representation.IsIrreducible ((Representation.symplecticNatural 2).comp H.subtype))
    (K₁ K₂:Subgroup H) [Group.IsPerfect K₁] [Group.IsPerfect K₂]
    [Nontrivial K₁] [Nontrivial K₂]
    (hc:∀x:K₁,∀y:K₂,Commute (x:H) (y:H)) (hgen:K₁⊔K₂=⊤) :
    ∃Q:QuadraticForm F (Vector F),Q.polarBilin=form F ∧ ∀h:H,∀v,Q ((h:Sp F)•v)=Q v := by
  let ρ : Representation F H (Vector F) := (Representation.symplecticNatural 2).comp H.subtype
  let : ρ.IsIrreducible := hi
  let f := MonoidHom.noncommCoprod K₁.subtype K₂.subtype hc
  have hsur : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    exact (MonoidHom.noncommCoprod_range K₁.subtype K₂.subtype hc).trans
      ((congrArg₂ (·⊔·) K₁.range_subtype K₂.range_subtype).trans hgen)
  let σ : Representation F (K₁×K₂) (Vector F) := ρ.comp f
  let : σ.IsIrreducible := (Representation.irreducible_comp_surjective_iff f hsur ρ).mpr hi
  have hf : Function.Injective ρ := subgroup_action_faithful H
  have hl : σ.comp (MonoidHom.inl K₁ K₂)≠1 := by
    obtain ⟨k,hk⟩ := exists_ne (1:K₁)
    intro he
    apply hk
    apply Subtype.ext
    apply hf
    have hh := congrArg (fun τ:Representation F K₁ (Vector F)=>τ k) he
    change ρ (f (k,1))=1 at hh
    have hfk : f (k,1)=(k:H) := by
      change (k:H)*(1:H)=(k:H)
      exact mul_one _
    rw [hfk] at hh
    exact hh.trans ρ.map_one.symm
  have hr : σ.comp (MonoidHom.inr K₁ K₂)≠1 := by
    obtain ⟨k,hk⟩ := exists_ne (1:K₂)
    intro he
    apply hk
    apply Subtype.ext
    apply hf
    have hh := congrArg (fun τ:Representation F K₂ (Vector F)=>τ k) he
    change ρ (f (1,k))=1 at hh
    have hfk : f (1,k)=(k:H) := by
      change (1:H)*(k:H)=(k:H)
      exact one_mul _
    rw [hfk] at hh
    exact hh.trans ρ.map_one.symm
  obtain ⟨Q,hQ,hQI⟩ := Representation.ComponentTensor.exists_compatible_quadratic σ hl hr
    (by simp [Vector]) (form F) TwoLocalCover.form_nondegenerate
    (fun g v w=>preserves_form (F:=F) ((f g:H):Sp F) v w)
  refine ⟨Q,hQ,?_⟩
  intro h v
  obtain ⟨g,rfl⟩ := hsur h
  exact hQI g v

omit [CharP F 2] in
/-- Every actual symplectic normalizer of the component product preserves
the same compatible quadratic form. -/
theorem exists_normalizer_quadratic_of_commuting_perfect_factors
    (H:Subgroup (Sp F))
    (hi:Representation.IsIrreducible ((Representation.symplecticNatural 2).comp H.subtype))
    (K₁ K₂:Subgroup H) [Group.IsPerfect K₁] [Group.IsPerfect K₂]
    [Nontrivial K₁] [Nontrivial K₂]
    (hc:∀x:K₁,∀y:K₂,Commute (x:H) (y:H)) (hgen:K₁⊔K₂=⊤) :
    ∃Q:QuadraticForm F (Vector F),Q.polarBilin=form F ∧
      ∀g∈normalizer (H:Set (Sp F)),∀v,Q (g•v)=Q v := by
  obtain ⟨Q,hQ,hQI⟩ := exists_quadratic_of_commuting_perfect_factors H hi K₁ K₂ hc hgen
  let ρ : Representation F H (Vector F) := (Representation.symplecticNatural 2).comp H.subtype
  let : ρ.IsIrreducible := hi
  have hnon : ∃g v,ρ g v≠v := by
    obtain ⟨k,hk⟩ := exists_ne (1:K₁)
    by_contra! hh
    apply hk
    apply Subtype.ext
    apply subgroup_action_faithful H
    apply LinearMap.ext
    intro v
    have he : ρ (1:H) v=v := congrArg (fun z:Module.End F (Vector F)=>z v) ρ.map_one
    exact (hh (k:H) v).trans he.symm
  refine ⟨Q,hQ,?_⟩
  intro g hg
  apply Representation.QuadraticRefinement.normalizer_preserves ρ hnon Q hQI
    (H.normalizerMonoidHom ⟨g,hg⟩) (toLinear g)
  · intro h v
    change g•((h:Sp F)•v)=(g*(h:Sp F)*g⁻¹)•(g•v)
    simp only [mul_smul,inv_smul_smul]
  · intro v w
    rw [hQ]
    exact preserves_form g v w

open TwoConjugate DiagramAutomorphisms EvenBorelTorus
/-- In the actual moving opposition pair, no normal irreducible subgroup
can be a product of two commuting nontrivial perfect factors. -/
theorem moving_pair_excludes_two_perfect_factors (hq:2<Nat.card F)
    (a:ActorReduction.stabilizer (F:=F)) (ha:¬PreservesDiagram a.val)
    (V:Subgroup (Sp F)) (hV:V.map a.val.toMonoidHom=V)
    (hcent:V≤(CentralRootGeometry.parameter (F:=F)).range) (hr:2<Nat.card V)
    (H:Subgroup (Sp F))
    (hi:Representation.IsIrreducible ((Representation.symplecticNatural 2).comp H.subtype))
    (hN:oppositePair V≤normalizer (H:Set (Sp F)))
    (K₁ K₂:Subgroup H) [Group.IsPerfect K₁] [Group.IsPerfect K₂]
    [Nontrivial K₁] [Nontrivial K₂]
    (hc:∀x:K₁,∀y:K₂,Commute (x:H) (y:H)) (hgen:K₁⊔K₂=⊤) : False := by
  obtain ⟨Q,hQ,hQI⟩ := exists_normalizer_quadratic_of_commuting_perfect_factors H hi K₁ K₂ hc hgen
  exact oppositePair_not_preserves_quadratic_of_moving_actor hq a ha V hV hcent hr Q hQ
    (fun g hg=>hQI g (hN hg))
end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ComponentTensor
