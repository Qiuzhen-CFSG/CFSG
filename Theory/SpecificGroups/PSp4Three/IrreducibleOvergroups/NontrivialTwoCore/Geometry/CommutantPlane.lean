module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Geometry.Eigenspaces
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NoncommRing

/-!
# A plane representation of an anticommuting pair's commutant

An invertible map exchanging the two sign spaces of a linear involution
makes them equidimensional. A group commuting with both operators acts
faithfully on either sign space, since the exchanging map recovers the
other action.

Over F₃, two anticommuting invertible operators with squares in {1, -1}
always provide such an involution and exchanging map. If one squares to
one, use it directly. If both square to minus one, their sum squares to
one and their product exchanges its sign spaces. In dimension four this
constructs an actual embedding of the commutant into GL₂(3).

Source application: the extraspecial lift-core case in Aschbacher–Smith,
Theorem 0.1.2(4), condition K, printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSp4Three.NontrivialTwoCore.Geometry
open LinearInvolution

private noncomputable def exchangingEquiv {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (t : V →ₗ[F] V) (s : V ≃ₗ[F] V) (hs : ∀ x, t (s x) = -s (t x)) :
    plus t ≃ₗ[F] minus t where
  toFun x := ⟨s x.val, by rw [mem_minus, hs, (mem_plus t x.val).mp x.prop]⟩
  invFun x := ⟨s.symm x.val, by
    rw [mem_plus]
    apply s.injective
    have h := hs (s.symm x.val)
    rw [s.apply_symm_apply, (mem_minus t x.val).mp x.prop] at h
    exact (neg_injective h).symm.trans (s.apply_symm_apply x.val).symm⟩
  left_inv x := by apply Subtype.ext; exact s.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact s.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact s.map_add x.val y.val
  map_smul' a x := by apply Subtype.ext; exact s.map_smul a x.val

/-- A commuting group acts faithfully on a half-dimensional sign space when
an invertible intertwiner exchanges the two sign spaces. -/
public theorem exists_gl_two_embedding_of_exchange
    {F V C : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Group C] (rho : C →* (V ≃ₗ[F] V)) (hrho : Function.Injective rho)
    (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (s : V ≃ₗ[F] V) (hs : ∀ x, t (s x) = -s (t x))
    (hc : ∀ g x, t (rho g x) = rho g (t x))
    (hcs : ∀ g x, s (rho g x) = rho g (s x))
    (h2 : (2 : F) ≠ 0) (hd : Module.finrank F V = 4) :
    ∃ f : C →* Matrix.GeneralLinearGroup (Fin 2) F, Function.Injective f := by
  classical
  let W := plus t
  have hW (g : C) : ∀ x ∈ W, rho g x ∈ W := by
    intro x hx
    rw [mem_plus] at hx ⊢
    rw [hc, hx]
  let r : C →* (W ≃ₗ[F] W) := {
    toFun := fun g => {
      toFun := fun x => ⟨rho g x.val, hW g x.val x.prop⟩
      invFun := fun x => ⟨rho g⁻¹ x.val, hW g⁻¹ x.val x.prop⟩
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun x => by apply Subtype.ext; simp
      map_add' := fun x y => by apply Subtype.ext; exact (rho g).map_add x.val y.val
      map_smul' := fun a x => by apply Subtype.ext; exact (rho g).map_smul a x.val }
    map_one' := by ext x; change rho 1 x.val = x.val; simp
    map_mul' := fun g h => by ext x; change rho (g * h) x.val = rho g (rho h x.val); simp }
  have hr : Function.Injective r := by
    intro g h hgh
    apply hrho
    ext x
    obtain ⟨⟨p,m⟩,rfl⟩ := (decomposition t ht h2).surjective x
    obtain ⟨q,hq⟩ := (exchangingEquiv t s hs).surjective m
    have hp : rho g p.val = rho h p.val :=
      congrArg (fun f : W ≃ₗ[F] W => (f p).val) hgh
    have hq' : rho g q.val = rho h q.val :=
      congrArg (fun f : W ≃ₗ[F] W => (f q).val) hgh
    have hm : rho g m.val = rho h m.val := by
      have he : m.val = s q.val := (congrArg Subtype.val hq).symm
      rw [he, ← hcs, ← hcs, hq']
    change rho g (p.val + m.val) = rho h (p.val + m.val)
    rw [map_add, map_add, hp, hm]
  have hdim : Module.finrank F W = 2 := by
    have he := (exchangingEquiv t s hs).finrank_eq
    have ha := finrank_plus_add_minus t ht h2
    change Module.finrank F (plus t) = 2
    omega
  let b := Module.finBasisOfFinrankEq F W hdim
  let e : (W ≃ₗ[F] W) ≃* Matrix.GeneralLinearGroup (Fin 2) F :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F W).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  exact ⟨e.toMonoidHom.comp r, e.injective.comp hr⟩

/-- Two anticommuting operators with scalar squares give a faithful
half-dimensional action of their commutant over the ternary field. -/
public theorem exists_gl_two_embedding_of_anticommuting_pair
    {V C : Type*} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    [Group C] (rho : C →* (V ≃ₗ[ZMod 3] V)) (hrho : Function.Injective rho)
    (a b : V ≃ₗ[ZMod 3] V)
    (ha : a.toLinearMap * a.toLinearMap = 1 ∨ a.toLinearMap * a.toLinearMap = -1)
    (hb : b.toLinearMap * b.toLinearMap = 1 ∨ b.toLinearMap * b.toLinearMap = -1)
    (hab : a.toLinearMap * b.toLinearMap = -(b.toLinearMap * a.toLinearMap))
    (hca : ∀ g x, a (rho g x) = rho g (a x))
    (hcb : ∀ g x, b (rho g x) = rho g (b x))
    (hd : Module.finrank (ZMod 3) V = 4) :
    ∃ f : C →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3), Function.Injective f := by
  have hba : b.toLinearMap * a.toLinearMap = -(a.toLinearMap * b.toLinearMap) := by
    rw [hab, neg_neg]
  rcases ha with ha | ha
  · exact exists_gl_two_embedding_of_exchange rho hrho a.toLinearMap
      (fun x => LinearMap.congr_fun ha x) b (fun x => LinearMap.congr_fun hab x)
      hca hcb (by decide) hd
  rcases hb with hb | hb
  · exact exists_gl_two_embedding_of_exchange rho hrho b.toLinearMap
      (fun x => LinearMap.congr_fun hb x) a (fun x => LinearMap.congr_fun hba x)
      hcb hca (by decide) hd
  let A := a.toLinearMap
  let B := b.toLinearMap
  have hAB : A * B + B * A = 0 := by rw [hab, neg_add_cancel]
  have hsum : (A + B) * (A + B) = 1 := by
    calc
      _ = A * A + (A * B + B * A) + B * B := by noncomm_ring
      _ = (-1 : Module.End (ZMod 3) V) + -1 := by rw [ha, hb, hAB, add_zero]
      _ = 1 := by
        ext x
        change -x + -x = x
        have he : (-1 + -1 : ZMod 3) = 1 := by decide
        simpa only [add_smul, neg_one_smul, one_smul] using
          congrArg (fun c : ZMod 3 => c • x) he
  have hleft : (A + B) * (A * B) = -B + A := by
    calc
      _ = (A * A) * B + (B * A) * B := by noncomm_ring
      _ = -B + A := by
        rw [ha, hba, neg_one_mul, neg_mul, mul_assoc, hb, mul_neg, mul_one, neg_neg]
  have hright : (A * B) * (A + B) = B + -A := by
    calc
      _ = A * (B * A) + A * (B * B) := by noncomm_ring
      _ = B + -A := by
        rw [hba, mul_neg, ← mul_assoc, ha, hb, neg_one_mul, mul_neg, mul_one, neg_neg]
  have hexchange : (A + B) * (A * B) = -((A * B) * (A + B)) := by
    rw [hleft, hright, neg_add, neg_neg]
  apply exists_gl_two_embedding_of_exchange rho hrho (A + B)
    (fun x => LinearMap.congr_fun hsum x) (a * b)
    (fun x => LinearMap.congr_fun hexchange x)
  · intro g x
    change a (rho g x) + b (rho g x) = rho g (a x + b x)
    rw [hca, hcb, map_add]
  · intro g x
    change a (b (rho g x)) = rho g (a (b x))
    rw [hcb, hca]
  · decide
  · exact hd

end Matrix.PSp4Three.NontrivialTwoCore.Geometry
