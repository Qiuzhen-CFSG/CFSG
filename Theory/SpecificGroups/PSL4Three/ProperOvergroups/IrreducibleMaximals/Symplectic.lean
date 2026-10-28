module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.IrreducibleMaximals.Data
public import Theory.GroupTheory.SolvableLayersEmbeddingConstructions
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Mathlib.Algebra.Field.ZMod

/-!
# Solvable layers for projective symplectic similitudes

Suppose all matrix lifts of a subgroup of PSL₄(3) preserve a nondegenerate
alternating form up to a scalar. The multiplier homomorphism has abelian image.
An isometry with the standard alternating form embeds its kernel in the actual
symplectic matrix group. Passing to the central quotient kills every scalar
lift, and the remaining kernel is solvable because it embeds in the center.

The normal subgroup is the projective image of the multiplier kernel; its
quotient is solvable. The inner solvable normal subgroup is the kernel of the
induced map to PSp₄(3). The first isomorphism theorem supplies the faithful map
from the actual quotient. No simplicity, order, or subgroup classification is
used. This proves the geometric alternative, not its exhaustiveness.

Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`. Alternating-frame transport uses
the existing attributed ATLAS port in `PSp4Three.MatrixModel`.
-/

namespace Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals

private theorem descend_layers
    {A G H C : Type*} [Group A] [Group G] [Group H] [CommGroup C]
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


open Matrix.PSp4Three

noncomputable section

private def slLinear : SL →* (Vec ≃ₗ[ZMod 3] Vec) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) Vec).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL)

private theorem slLinear_injective : Function.Injective slLinear :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) Vec).injective.comp
    (Matrix.GeneralLinearGroup.toLin.injective.comp Matrix.SpecialLinearGroup.toGL_injective)

/-- Small layers for any subgroup whose matrix lifts are symplectic similitudes. -/
public theorem hasSmallLayers_of_symplecticSimilitudes (U : Subgroup PSL)
    (hU : SymplecticSimilitudes U) : HasSmallLayers U := by
  obtain ⟨B, hAlt, hND, hsim⟩ := hU
  obtain ⟨e⟩ := Matrix.PSp4Three.exists_isometry (F := ZMod 3) (V := Vec)
    2 B hAlt hND (by simp [Vec])
  have eleft (v : Vec) : e.symm (e v) = v := e.toLinearEquiv.symm_apply_apply v
  have eright (v : Vector 2 (ZMod 3)) : e (e.symm v) = v :=
    e.toLinearEquiv.apply_symm_apply v
  have hv : firstVector ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [firstVector] at this
  obtain ⟨w, hw⟩ := Matrix.PSp4Three.Frame.exists_partner B hND hv
  let A := U.comap project
  let c : A → (ZMod 3)ˣ := fun g => Classical.choose (hsim g)
  have hc (g : A) (x y : Vec) :
      B ((g : SL) • x) ((g : SL) • y) = (c g : ZMod 3) * B x y :=
    Classical.choose_spec (hsim g) x y
  let μ : A →* (ZMod 3)ˣ := {
    toFun := c
    map_one' := by
      apply Units.ext
      have h := hc 1 firstVector w
      simpa [hw] using h.symm
    map_mul' := by
      intro g h
      apply Units.ext
      have hh := hc (g * h) firstVector w
      change B (((g : SL) * (h : SL)) • firstVector)
        (((g : SL) * (h : SL)) • w) = _ at hh
      rw [mul_smul, mul_smul, hc g, hc h, hw] at hh
      simpa using hh.symm }
  let ρ : A →* (Vec ≃ₗ[ZMod 3] Vec) := slLinear.comp A.subtype
  have hρinj : Function.Injective ρ := slLinear_injective.comp A.subtype_injective
  let L (g : μ.ker) : Vector 2 (ZMod 3) ≃ₗ[ZMod 3] Vector 2 (ZMod 3) :=
    e.toLinearEquiv.symm.trans ((ρ g.val).trans e.toLinearEquiv)
  have hL (g : μ.ker) (x y : Vector 2 (ZMod 3)) :
      form (L g x) (L g y) = form x y := by
    change form (e ((g.val : SL) • e.symm x)) (e ((g.val : SL) • e.symm y)) = _
    rw [e.map_app]
    rw [hc]
    have hg : c g.val = 1 := g.property
    rw [hg, Units.val_one, one_mul]
    exact e.symm.map_app y x
  let s : μ.ker →* Sp 2 (ZMod 3) := {
    toFun := fun g => ofLinear (L g) (hL g)
    map_one' := by
      apply ext_action
      intro x
      simp [ofLinear_apply, L]
    map_mul' := by
      intro g h
      apply ext_action
      intro x
      simp [ofLinear_apply, L, mul_smul]
      exact (e.toLinearEquiv.symm_apply_apply _).symm }
  have hs (g : μ.ker) (x : Vector 2 (ZMod 3)) :
      s g • x = e (ρ g.val (e.symm x)) := ofLinear_apply (L g) (hL g) x
  have hsinj : Function.Injective s := by
    intro g h heq
    apply Subtype.ext
    apply hρinj
    apply DFunLike.ext
    intro v
    have he := congrArg (fun t : Sp 2 (ZMod 3) => t • e v) heq
    rw [hs, hs] at he
    simpa only [eleft] using e.injective he
  let f : μ.ker →* Matrix.PSL4Three.PSp := projection.comp s
  let k : f.ker →* Subgroup.center (Sp 2 (ZMod 3)) :=
    (s.comp f.ker.subtype).codRestrict _ (fun x =>
      (QuotientGroup.eq_one_iff (s x.val)).mp x.property)
  let : Group.IsSolvable (Subgroup.center (Sp 2 (ZMod 3))) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp a.property b.val).symm)
  let : Group.IsSolvable f.ker :=
    Group.isSolvable_of_isSolvable_injective (f := k) (by
      intro x y h
      apply Subtype.ext
      apply hsinj
      exact congrArg (fun z : Subgroup.center (Sp 2 (ZMod 3)) => z.val) h)
  let p : A →* U := (project.comp A.subtype).codRestrict U (fun x => x.property)
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) x.val
    exact ⟨⟨g, by change project g ∈ U; simpa only [project, hg] using x.property⟩,
      Subtype.ext hg⟩
  refine Or.inr (Or.inr (descend_layers p hp μ f ?_))
  intro x hx
  have hz : (x.val : SL) ∈ Subgroup.center SL := by
    apply (QuotientGroup.eq_one_iff (x.val : SL)).mp
    exact congrArg (fun z : U => z.val) hx
  obtain ⟨a, _, ha⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  apply (QuotientGroup.eq_one_iff (s x)).mpr
  apply scalar_is_central (s x) a
  intro v
  rw [hs]
  have hscalar (z : Vec) : ρ x.val z = a • z := by
    change (x.val : SL) • z = a • z
    change ((x.val : SL) : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ z = a • z
    rw [← ha]
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [hscalar, map_smul, eright]

end
end Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals
