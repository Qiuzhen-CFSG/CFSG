module
public import Theory.Representation.PSL3Two.SingerRestriction.FiveSpace.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transport of interchange involutions in an automorphism representation

An inner conjugation transports the actor pair and a moving subspace.
The subgroup maps, ordinary group action and extended automorphism action
all use this same conjugation. This abstract proof is specialized to the
actual Steinberg action in CubicInterchange, avoiding large kernel reductions
of the concrete matrix representation.

Source application: Aschbacher–Smith J.2.3(7), printed p.434 (PDF p.445).
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace BinaryLinearThree.SingerRestriction.CubicInterchange
private lemma pullback {X V : Type*} [_root_.Group X]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (K H : Subgroup X) (t : X)
    (he : K.map (MulAut.conj t).toMonoidHom = H)
    (M : Submodule (ZMod 2) V)
    (hM : ∀ h ∈ H, ∀ v ∈ M, ρ h v ∈ M)
    (hd : fixedSpace ρ H ⊓ M = ⊥)
    (ht : ∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ H, ρ h v = w) :
    let N := M.comap (ρ t)
    (∀ h ∈ K, ∀ u ∈ N, ρ h u ∈ N) ∧
    fixedSpace ρ K ⊓ N = ⊥ ∧
    (∀ u ∈ N, u ≠ 0 → ∀ w ∈ N, w ≠ 0 → ∃ h ∈ K, ρ h u = w) := by
  have hconj (h : X) (u : V) :
      ρ ((MulAut.conj t) h) (ρ t u) = ρ t (ρ h u) := by
    change ρ (t*h*t⁻¹) (ρ t u) = _
    simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
  let N := M.comap (ρ t)
  have hN : ∀ h ∈ K, ∀ u ∈ N, ρ h u ∈ N := by
    intro h hh u hu
    change ρ t (ρ h u) ∈ M
    rw [← hconj h u]
    exact hM _ (he ▸ mem_map.mpr ⟨h,hh,rfl⟩) _ hu
  refine ⟨hN, ?_, ?_⟩
  · apply _root_.eq_bot_iff.mpr
    intro u hu
    have hf : ρ t u ∈ fixedSpace ρ H := by
      rw [← he]
      intro k
      obtain ⟨a,ha,heq⟩ := k.property
      change ρ (k : X) (ρ t u) = ρ t u
      rw [← heq]
      exact (hconj a u).trans (congrArg (ρ t) (hu.1 ⟨a,ha⟩))
    have hz : ρ t u ∈ (⊥ : Submodule (ZMod 2) V) :=
      hd ▸ (show ρ t u ∈ fixedSpace ρ H ⊓ M from ⟨hf,hu.2⟩)
    change ρ t u = 0 at hz
    exact (ρ.apply_bijective t).injective (hz.trans (map_zero _).symm)
  · intro u hu hu0 w hw hw0
    have htu : ρ t u ≠ 0 := fun hz => hu0 ((ρ.apply_bijective t).injective
      (hz.trans (map_zero _).symm))
    have htw : ρ t w ≠ 0 := fun hz => hw0 ((ρ.apply_bijective t).injective
      (hz.trans (map_zero _).symm))
    obtain ⟨h,hh,hhuw⟩ := ht _ hu htu _ hw htw
    rw [← he] at hh
    obtain ⟨k,hk,rfl⟩ := hh
    refine ⟨k,hk,(ρ.apply_bijective t).injective ?_⟩
    rw [← hconj k u]
    exact hhuw

private lemma conjugate_action {X V : Type*} [_root_.Group X]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (t a : X) (u : V) :
    ρ (t*a*t⁻¹) (ρ t u) = ρ t (ρ a u) := by
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]

/-- Transport an actual pair of interchange involutions through one inner
conjugation. All computations are performed for abstract representations,
so specializing to the matrix model does not expand its implementation. -/
theorem transport_interchange {X V : Type*} [_root_.Group X]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (τ : Representation (ZMod 2) (MulAut X) V)
    (hτ : τ.comp (MulAut.conj : X →* MulAut X) = ρ)
    (K C H D : Subgroup X) (t : X)
    (heH : K.map (MulAut.conj t).toMonoidHom = H)
    (heD : C.map (MulAut.conj t).toMonoidHom = D)
    (j0 : MulAut X) (g0 : X)
    (hj0sq : j0 ^ 2 = 1) (hj0out : j0 ∉ MulAut.innerSubgroup X)
    (hj0K : K.map j0.toMonoidHom = K) (hj0C : ∀ d ∈ C, j0 d = d)
    (hg0sq : g0 ^ 2 = 1) (hg01 : g0 ≠ 1) (hg0C : g0 ∈ normalizer C)
    (hj0g : j0 g0 = g0)
    (hcanonical : ∀ N : Submodule (ZMod 2) V,
      (∀ h ∈ K, ∀ u ∈ N, ρ h u ∈ N) → fixedSpace ρ K ⊓ N = ⊥ →
      (∀ u ∈ N, u ≠ 0 → ∀ w ∈ N, w ≠ 0 → ∃ h ∈ K, ρ h u = w) →
      ∀ u ∈ N, u ≠ 0 → u ∈ fixedSpace ρ C → ρ g0 u = τ j0 u ∧ ρ g0 u ≠ u)
    (M : Submodule (ZMod 2) V)
    (hM : ∀ h ∈ H, ∀ v ∈ M, ρ h v ∈ M)
    (hd : fixedSpace ρ H ⊓ M = ⊥)
    (ht : ∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ H, ρ h v = w) :
    ∃ (j : MulAut X) (g : X),
      j ^ 2 = 1 ∧ j ∉ MulAut.innerSubgroup X ∧ H.map j.toMonoidHom = H ∧
      (∀ d ∈ D, j d = d) ∧ g ^ 2 = 1 ∧ g ≠ 1 ∧ g ∈ normalizer D ∧ j g = g ∧
      (∀ v ∈ M, v ≠ 0 → v ∈ fixedSpace ρ D → ρ g v = τ j v ∧ ρ g v ≠ v) := by
  let e := MulAut.conj t
  let j := e * j0 * e⁻¹
  let g := e g0
  have hj (x : X) : j (e x) = e (j0 x) := by simp [j]
  have hj2 : j ^ 2 = 1 := by
    calc
      j ^ 2 = e * j0 ^ 2 * e⁻¹ := by simp only [j,pow_two,mul_assoc,inv_mul_cancel_left]
      _ = 1 := by rw [hj0sq,mul_one,mul_inv_cancel]
  have hej : e ∈ MulAut.innerSubgroup X := ⟨t,rfl⟩
  have hjout : j ∉ MulAut.innerSubgroup X := by
    intro hi
    have ho := (MulAut.innerSubgroup X).mul_mem
      ((MulAut.innerSubgroup X).mul_mem ((MulAut.innerSubgroup X).inv_mem hej) hi) hej
    have heo : e⁻¹*j*e = j0 := by simp only [j,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
    rw [heo] at ho
    exact hj0out ho
  have hjH : H.map j.toMonoidHom = H := by
    calc
      H.map j.toMonoidHom = (K.map j0.toMonoidHom).map e.toMonoidHom := by
        rw [← heH,Subgroup.map_map,Subgroup.map_map]
        apply congrArg (fun f : X →* X => K.map f)
        exact MonoidHom.ext (fun x => hj x)
      _ = H := by rw [hj0K]; exact heH
  have hjD : ∀ d ∈ D, j d = d := by
    intro d hdD
    rw [← heD] at hdD
    obtain ⟨a,ha,rfl⟩ := hdD
    exact (hj a).trans (congrArg e (hj0C a ha))
  have hg2 : g ^ 2 = 1 :=
    (map_pow e g0 2).symm.trans ((congrArg e hg0sq).trans (map_one e))
  have hg1 : g ≠ 1 := fun h => hg01 (e.injective (h.trans (map_one e).symm))
  have hgD : g ∈ normalizer D := by
    rw [← heD, ← map_equiv_normalizer_eq]
    exact mem_map.mpr ⟨g0,hg0C,rfl⟩
  have hjg : j g = g := (hj g0).trans (congrArg e hj0g)
  refine ⟨j,g,hj2,hjout,hjH,hjD,hg2,hg1,hgD,hjg,?_⟩
  let N := M.comap (ρ t)
  obtain ⟨hN,hdN,htN⟩ := pullback ρ K H t heH M hM hd ht
  intro v hv hv0 hvD
  let u := ρ t⁻¹ v
  have htu : ρ t u = v := Representation.self_inv_apply ρ t v
  have hu : u ∈ N := by change ρ t u ∈ M; rwa [htu]
  have hu0 : u ≠ 0 := fun hz => hv0 (htu.symm.trans ((congrArg (ρ t) hz).trans (map_zero _)))
  have huD : u ∈ fixedSpace ρ C := by
    intro a
    change ρ (a : X) u = u
    apply (ρ.apply_bijective t).injective
    rw [← conjugate_action ρ t a u,htu]
    exact hvD ⟨e a,heD ▸ mem_map.mpr ⟨a,a.property,rfl⟩⟩
  have hc := hcanonical N hN hdN htN u hu hu0 huD
  have hgi : ρ g v = ρ t (ρ g0 u) := by
    rw [← htu]
    exact conjugate_action ρ t g0 u
  have ha : τ j v =
      ρ t (τ j0 u) := by
    have he : τ e = ρ t :=
      congrArg (fun ρ : Representation (ZMod 2) X V => ρ t)
        hτ
    have h := conjugate_action τ e j0 u
    change τ j (τ e u) =
      τ e (τ j0 u) at h
    have hu' : τ e u = v :=
      (LinearMap.congr_fun he u).trans htu
    exact ((congrArg (τ j) hu').symm.trans h).trans
      (LinearMap.congr_fun he _)
  constructor
  · exact hgi.trans ((congrArg (ρ t) hc.1).trans ha.symm)
  · intro h
    exact hc.2 ((ρ.apply_bijective t).injective (hgi.symm.trans (h.trans htu.symm)))


end BinaryLinearThree.SingerRestriction.CubicInterchange
