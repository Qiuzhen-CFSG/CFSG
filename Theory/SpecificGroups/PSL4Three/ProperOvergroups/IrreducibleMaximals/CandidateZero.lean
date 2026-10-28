module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.IrreducibleMaximals.CandidateZero.Representation
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Normal layers for the first concrete PSL₄(3) candidate

The generated matrix subgroup acts on four explicit alternating forms. Its
permutation kernel embeds in Sp₄(3), and the quotient of the generated group
by that kernel embeds in the solvable group S₄. Projecting the kernel gives a
normal subgroup `N` of the candidate with solvable outer quotient.

The symplectic representation descends to a homomorphism `N → PSp₄(3)`:
scalar matrices killed in PSL₄(3) are killed in PSp₄(3) as well. Its kernel
`R` is a solvable normal subgroup of `N`. The first isomorphism theorem gives
the required faithful map from the actual quotient `N/R`. Composing the
projective map with conjugation gives these layers for every conjugate.

This construction uses the permitted PSp₄(3) target, without requiring an
abstract identification of the candidate or its nonsolvable factor.

Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals

private theorem descend_solvable_layers
    {A G H C : Type*} [Group A] [Group G] [Group H] [Group C]
    [Group.IsSolvable C]
    (p : A →* G) (hp : Function.Surjective p) (μ : A →* C)
    (f : μ.ker →* H) [Group.IsSolvable f.ker]
    (hpf : ∀ x : μ.ker, p x = 1 → f x = 1) :
    Theory.GroupTheory.SolvableLayersEmbedding G H := by
  let N := μ.ker.map p
  let : N.Normal := Subgroup.Normal.map inferInstance p hp
  let q : A →* G ⧸ N := (QuotientGroup.mk' N).comp p
  have hμq : μ.ker ≤ q.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff (p x)).mpr ⟨x, hx, rfl⟩
  let q' := QuotientGroup.lift μ.ker q hμq
  have hq' : Function.Surjective q' :=
    QuotientGroup.lift_surjective_of_surjective μ.ker q
      ((QuotientGroup.mk'_surjective N).comp hp) hμq
  let : Group.IsSolvable (A ⧸ μ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective μ)
  have houter : Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_surjective hq'
  let pN : μ.ker →* N :=
    (p.comp μ.ker.subtype).codRestrict N (fun x => ⟨x, x.property, rfl⟩)
  have hpN : Function.Surjective pN := by
    rintro ⟨x, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : pN.ker ≤ f.ker := by
    intro x hx
    exact hpf x (congrArg (fun z : N => (z : G)) hx)
  let j : N →* H := pN.liftOfSurjective hpN ⟨f, hker⟩
  have hj (x : μ.ker) : j (pN x) = f x := by
    exact pN.liftOfRightInverse_comp_apply _ _ _ x
  let k : f.ker →* j.ker :=
    (pN.comp f.ker.subtype).codRestrict j.ker (fun x => by
      change j (pN x.val) = 1
      rw [hj]
      exact x.property)
  have hk : Function.Surjective k := by
    intro x
    obtain ⟨y, hy⟩ := hpN x.val
    have hfy : f y = 1 := by rw [← hj, hy]; exact x.property
    exact ⟨⟨y, hfy⟩, Subtype.ext hy⟩
  let : Group.IsSolvable j.ker := Group.isSolvable_of_surjective hk
  exact ⟨N, inferInstance, houter, j.ker, inferInstance, inferInstance,
    QuotientGroup.kerLift j, QuotientGroup.kerLift_injective j⟩

open CandidateZero

/-- The first concrete candidate and every conjugate have the required actual
normal layers, represented in the projective symplectic target. -/
public theorem candidate_zero_conjugate_hasSmallLayers (g : PSL) :
    HasSmallLayers ((candidate 0).map (MulAut.conj g).toMonoidHom) := by
  let U := (candidate 0).map (MulAut.conj g).toMonoidHom
  let p : lift →* U :=
    (((MulAut.conj g).toMonoidHom.comp project).comp lift.subtype).codRestrict U
      (fun x => ⟨project x.val, ⟨x.val, x.property, rfl⟩, rfl⟩)
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨y, hy, hyx⟩ := x.property
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨⟨z, hz⟩, Subtype.ext hyx⟩
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable projectiveSymplectic.ker := projectiveSymplectic_ker_solvable
  refine Or.inr (Or.inr (descend_solvable_layers p hp action projectiveSymplectic ?_))
  intro x hx
  apply projectiveSymplectic_eq_one
  apply (MulAut.conj g).injective
  have hx' := congrArg (fun z : U => (z : PSL)) hx
  change (MulAut.conj g) (project x.val.val) = 1 at hx'
  simpa only [map_one] using hx'

end Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals
