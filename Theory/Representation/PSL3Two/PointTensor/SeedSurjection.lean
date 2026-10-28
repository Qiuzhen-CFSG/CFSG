module

public import Theory.Representation.PSL3Two.PointTensor
public import Theory.Representation.SimpleHeadQuotient.BinaryCoreObstruction

/-!
# The marked point-tensor cover

An actual binary plane fixed by the marked point parabolic gives a quotient of
the literal seven-point permutation module tensored with the natural binary
`S₃`-module.  The construction keeps the marked point and the given plane;
it does not choose a natural/dual orientation or a chief section.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 13.8.21(1),
printed p.957.
-/

@[expose] public section

open Representation Representation.BinaryOffender InvertedCubicTensor
open BinaryLinearThree BinaryLinearThree.FanoDecomposition
open scoped TensorProduct

namespace BinaryLinearThree.PointTensor

abbrev F := ZMod 2
abbrev Core := BinaryPermutation.core (Fin 3)

/- The elementary orbit-map construction, with the cyclic-generation premise
  deliberately omitted.  Its range is handled after tensoring, using the
  generating-seed hypothesis. -/
private theorem orbit_map
    {G Ω M : Type*} [_root_.Group G] [Fintype Ω] [DecidableEq Ω]
    [AddCommGroup M] [Module F M]
    (τ : G →* Equiv.Perm Ω) (o : Ω) (H : Subgroup G)
    (hstab : ∀ g : G, g ∈ H ↔ τ g o = o)
    (htrans : ∀ x : Ω, ∃ g : G, τ g o = x)
    (σ : Representation F G M) (m : M)
    (hfixed : ∀ g ∈ H, σ g m = m) :
    ∃ f : Representation.IntertwiningMap
      ((BinaryPermutation.representation Ω).comp τ) σ,
      f (Pi.single o 1) = m ∧
        (∀ g x, f (Pi.single (τ g x) 1) = σ g (f (Pi.single x 1))) ∧
        ∀ x, ∃ g, τ g o = x ∧ f (Pi.single x 1) = σ g m := by
  classical
  let lift (x : Ω) : G := Classical.choose (htrans x)
  have hlift (x : Ω) : τ (lift x) o = x := Classical.choose_spec (htrans x)
  let value (x : Ω) : M := σ (lift x) m
  have hvalue (g : G) (x : Ω) (hg : τ g o = x) : value x = σ g m := by
    have hh : (lift x)⁻¹ * g ∈ H := by
      rw [hstab, map_mul, map_inv]
      change (τ (lift x)).symm (τ g o) = o
      rw [hg]
      apply (τ (lift x)).injective
      simpa only [Equiv.apply_symm_apply] using (hlift x).symm
    have he := congrArg (σ (lift x)) (hfixed _ hh)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
    exact he.symm
  have hvalue_o : value o = m := by simpa using hvalue 1 o (by simp)
  have hvalue_act (g : G) (x : Ω) : value (τ g x) = σ g (value x) := by
    have hx : τ (g * lift x) o = τ g x := by
      rw [map_mul]
      change τ g (τ (lift x) o) = τ g x
      rw [hlift]
    rw [hvalue (g * lift x) _ hx, map_mul]
    rfl
  let f : Representation.IntertwiningMap
      ((BinaryPermutation.representation Ω).comp τ) σ := {
    toLinearMap := {
      toFun := fun a => ∑ x : Ω, a x • value x
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ x : Ω, a ((τ g).symm x) • value x) =
        σ g (∑ x : Ω, a x • value x)
      rw [map_sum]
      simp only [map_smul, ← hvalue_act]
      exact (Equiv.sum_comp (τ g)
        (fun x => a ((τ g).symm x) • value x)).symm.trans (by simp)
    }
  have hf (x : Ω) : f (Pi.single x 1) = value x := by
    change (∑ y : Ω, (Pi.single x (1 : F) : Ω → F) y • value y) = value x
    simp
  refine ⟨f, (hf o).trans hvalue_o, ?_, ?_⟩
  · intro g x
    rw [hf, hf, hvalue_act]
  · intro x
    exact ⟨lift x, hlift x, (hf x).trans rfl⟩

private theorem point_stabilizer_iff (g : Group) :
    g ∈ Matrix.PSL3Two.pointParabolicSL ↔
      pointPerm g Matrix.PSL3Two.flagPoint = Matrix.PSL3Two.flagPoint := by
  revert g
  decide +kernel

variable {U : Type*} [AddCommGroup U] [Module F U]

theorem exists_surjective
    (ρ : Representation F Actor U) (D : Submodule F U)
    (hseed : IsGeneratingSeed ρ D) :
    ∃ q : pointTensor.IntertwiningMap ρ, Function.Surjective q := by
  let σ : Representation F S₃ D := {
    toFun s := (ρ (1, s)).domRestrict D |>.codRestrict D
      (fun v => hseed.symmetric_stable s v.val v.property)
    map_one' := by
      ext v
      change ρ (1 : Actor) v.val = v.val
      have h := LinearMap.congr_fun ρ.map_one v.val
      simpa only [Module.End.one_apply] using h
    map_mul' s t := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change ρ (1, s * t) v.val = ρ (1, s) (ρ (1, t) v.val)
      rw [← Module.End.mul_apply, ← map_mul]
      simp only [Prod.mk_mul_mk, mul_one] }
  have hfree : ∀ v : D, σ cubic v = v → v = 0 := by
    intro v hv
    apply Subtype.ext
    apply hseed.cubic_fixed_free v.val v.property
    change ρ (1, cubic) v.val = v.val
    exact congrArg Subtype.val hv
  let : FiniteDimensional F D := Module.finite_of_finrank_pos (by
    rw [hseed.dimension_two]
    decide)
  have hpair := (pairEquiv σ hfree).finrank_eq
  rw [Module.finrank_prod, hseed.dimension_two] at hpair
  change Module.finrank F (multiplicitySpace σ) +
      Module.finrank F (multiplicitySpace σ) = 2 at hpair
  have hmult : Module.finrank F (multiplicitySpace σ) = 1 := by omega
  have hmultpos : 0 < Module.finrank F (multiplicitySpace σ) := by
    rw [hmult]
    decide
  let : Nontrivial (multiplicitySpace σ) := Module.nontrivial_of_finrank_pos hmultpos
  obtain ⟨i, hi⟩ := exists_ne (0 : multiplicitySpace σ)
  let e : Core →ₗ[F] D := {
    toFun n := tensorEquiv σ hfree (i ⊗ₜ[F] n)
    map_add' := by
      intro x y
      change tensorEquiv σ hfree (i ⊗ₜ[F] (x + y)) =
        tensorEquiv σ hfree (i ⊗ₜ[F] x) + tensorEquiv σ hfree (i ⊗ₜ[F] y)
      rw [TensorProduct.tmul_add, map_add]
    map_smul' := by
      intro c x
      change tensorEquiv σ hfree (i ⊗ₜ[F] (c • x)) =
        c • tensorEquiv σ hfree (i ⊗ₜ[F] x)
      rw [TensorProduct.tmul_smul, map_smul] }
  have he_surj : Function.Surjective e := by
    have hsurj : ∀ z : multiplicitySpace σ ⊗[F] Core,
        ∃ n : Core, e n = tensorEquiv σ hfree z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp [e]⟩
      | tmul a n =>
          obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hmult hi a
          refine ⟨c • n, ?_⟩
          calc
            e (c • n) = tensorEquiv σ hfree (i ⊗ₜ[F] (c • n)) := rfl
            _ = tensorEquiv σ hfree ((c • i) ⊗ₜ[F] n) := by
              rw [TensorProduct.smul_tmul]
            _ = tensorEquiv σ hfree (a ⊗ₜ[F] n) := by rw [hc]
      | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          refine ⟨x' + y', ?_⟩
          calc
            e (x' + y') = tensorEquiv σ hfree (i ⊗ₜ[F] (x' + y')) := rfl
            _ = tensorEquiv σ hfree (i ⊗ₜ[F] x' + i ⊗ₜ[F] y') := by
              rw [TensorProduct.tmul_add]
            _ = e x' + e y' := by
              change tensorEquiv σ hfree (i ⊗ₜ[F] x' + i ⊗ₜ[F] y') =
                tensorEquiv σ hfree (i ⊗ₜ[F] x') + tensorEquiv σ hfree (i ⊗ₜ[F] y')
              rw [map_add]
            _ = tensorEquiv σ hfree x + tensorEquiv σ hfree y := by rw [hx', hy']
            _ = tensorEquiv σ hfree (x + y) := by rw [map_add]
    intro d
    obtain ⟨n, hn⟩ := hsurj ((tensorEquiv σ hfree).symm d)
    exact ⟨n, hn.trans ((tensorEquiv σ hfree).apply_symm_apply d)⟩
  have he_symmetric (s : S₃) (n : Core) :
      e (BinaryPermutation.coreRepresentation (Fin 3) s n) = σ s (e n) := by
    exact tensorEquiv_symmetric σ hfree s i n
  let m : Core →ₗ[F] U := D.subtype.comp e
  have hm_symmetric (s : S₃) (n : Core) :
      m (BinaryPermutation.coreRepresentation (Fin 3) s n) =
        ρ (1, s) (m n) := by
    change (e (BinaryPermutation.coreRepresentation (Fin 3) s n)).val =
      ρ (1, s) (e n).val
    have hh := congrArg Subtype.val (he_symmetric s n)
    change (e (BinaryPermutation.coreRepresentation (Fin 3) s n)).val =
      ρ (1, s) (e n).val at hh
    exact hh
  let τ : Representation F Group (Core →ₗ[F] U) := {
    toFun g := {
      toFun f := (ρ (g, 1)).comp f
      map_add' := by intros; ext n; simp
      map_smul' := by intros; ext n; simp }
    map_one' := by
      ext f n
      change ρ (1 : Actor) (f n) = f n
      have h := LinearMap.congr_fun ρ.map_one (f n)
      simpa only [Module.End.one_apply] using h
    map_mul' g h := by
      ext f n
      change ρ ((g, 1) * (h, 1)) (f n) =
        (ρ (g, 1) * ρ (h, 1)) (f n)
      exact LinearMap.congr_fun (ρ.map_mul (g, 1) (h, 1)) (f n) }
  have hm_fixed (g : Group) (hg : g ∈ Matrix.PSL3Two.pointParabolicSL) :
      τ g m = m := by
    ext n
    change ρ (g, 1) (e n).val = (e n).val
    exact hseed.point_fixed g hg (e n).val (e n).property
  obtain ⟨f, hf0, hf_act, hf_basis⟩ := orbit_map pointPerm Matrix.PSL3Two.flagPoint
    Matrix.PSL3Two.pointParabolicSL point_stabilizer_iff
    SimpleHeadQuotientObstruction.point_reachable τ m hm_fixed
  have hf_symmetric (a : BinaryPermutation.Full Point) (s : S₃) (n : Core) :
      f a (BinaryPermutation.coreRepresentation (Fin 3) s n) =
        ρ (1, s) (f a n) := by
    have ha : ∑ p : Point, a p • (Pi.single p (1 : F) : BinaryPermutation.Full Point) = a := by
      ext p
      simp [Pi.single_apply]
    rw [← ha]
    rw [show f (∑ p : Point, a p • (Pi.single p (1 : F) : BinaryPermutation.Full Point)) =
      ∑ p : Point, a p • f (Pi.single p (1 : F)) by
        simp only [map_sum, map_smul]]
    change (∑ p : Point, a p • f (Pi.single p (1 : F)))
      (BinaryPermutation.coreRepresentation (Fin 3) s n) = _
    simp only [LinearMap.coe_sum, Finset.sum_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨g, hg, hgp⟩ := hf_basis p
    rw [hgp]
    change a p • ρ (g, 1) (m (BinaryPermutation.coreRepresentation (Fin 3) s n)) =
      ρ (1, s) (a p • ρ (g, 1) (m n))
    rw [map_smul]
    rw [hm_symmetric]
    apply congrArg (fun z : U => a p • z)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    all_goals simp
  let b : BinaryPermutation.Full Point →ₗ[F] (Core →ₗ[F] U) := {
    toFun := f
    map_add' := by intros; exact f.map_add _ _
    map_smul' := by intros; exact f.map_smul _ _ }
  let q₀ : (BinaryPermutation.Full Point) ⊗[F] Core →ₗ[F] U :=
    TensorProduct.lift b
  let q : pointTensor.IntertwiningMap ρ := {
    toLinearMap := q₀
    isIntertwining' := by
      intro g
      rcases g with ⟨g, s⟩
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp [q₀]
      | tmul a n =>
          change f (BinaryPermutation.representation Point (pointPerm g) a)
              (BinaryPermutation.coreRepresentation (Fin 3) s n) =
            ρ (g, s) (f a n)
          have hfg := Representation.IntertwiningMap.isIntertwining
            ((BinaryPermutation.representation Point).comp pointPerm) τ f g a
          rw [show f (BinaryPermutation.representation Point (pointPerm g) a) =
              τ g (f a) by simpa using hfg]
          change ρ (g, 1) (f a (BinaryPermutation.coreRepresentation (Fin 3) s n)) = _
          rw [hf_symmetric]
          rw [← Module.End.mul_apply, ← map_mul]
          simp only [Prod.mk_mul_mk, one_mul, mul_one]
      | add x y hx hy => simp only [map_add, hx, hy]
  }
  let R := q.range
  have hD : D ≤ R.toSubmodule := by
    intro v hv
    obtain ⟨n, hn⟩ := he_surj ⟨v, hv⟩
    refine ⟨(Pi.single Matrix.PSL3Two.flagPoint (1 : F)) ⊗ₜ[F] n, ?_⟩
    change q₀ ((Pi.single Matrix.PSL3Two.flagPoint (1 : F)) ⊗ₜ[F] n) = v
    change f (Pi.single Matrix.PSL3Two.flagPoint (1 : F)) n = v
    rw [hf0]
    change (e n).val = v
    exact congrArg Subtype.val hn
  have hR : R = ⊤ := hseed.generates R hD
  refine ⟨q, ?_⟩
  apply LinearMap.range_eq_top.mp
  exact congrArg Subrepresentation.toSubmodule hR

end BinaryLinearThree.PointTensor
