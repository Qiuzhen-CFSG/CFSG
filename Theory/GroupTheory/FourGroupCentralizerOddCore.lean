module

public import Theory.PPrimeCore
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Trivial normal subgroups from a fused four-group

Suppose z is an involution and z,t,zt are conjugate. If a normal subgroup
has trivial fixed subgroup under z, it is trivial: both z and t act by
inversion, whereas zt then acts trivially and without nonidentity fixed points.
In particular, if C_G(z) is a two-group, the odd core is trivial.

This gives the coprime fixed-point step used in Held, Illinois J. Math. 13
(1969), 224--240, p.234 (DOI 10.1215/ijm/1256053756). The general normal
subgroup argument is extracted from the existing private proof in
`ExtraspecialCentralizerSimplicity.lean`; it needs no extraspecial hypothesis.
-/

open Subgroup
namespace Subgroup

public theorem normal_eq_bot_of_fused_triple {G : Type*} [Group G] [Finite G] (z t : G) (hz : orderOf z = 2)
    (ht : IsConj z t) (hzt : IsConj z (z * t))
    (N : Subgroup G) [N.Normal]
    (hfix : ∀ x ∈ N, x ∈ centralizer ({z} : Set G) → x = 1) : N = ⊥ := by
  have hfp (u : G) (hu : IsConj z u) : MonoidHom.FixedPointFree (MulAut.conjNormal u : MulAut N) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hu
    intro x hx
    have hx' : u * (x : G) * u⁻¹ = x := congrArg Subtype.val hx
    have hc : (g⁻¹ * (x : G) * g) ∈ centralizer ({z} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have he := mul_inv_eq_iff_eq_mul.mp hx'
      rw [← hg] at he
      have he' := congrArg (fun a => g⁻¹ * a * g) he
      group at he' ⊢
      exact he'.symm
    have hn : g⁻¹ * (x : G) * g ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem x x.property g⁻¹
    have he := hfix _ hn hc
    apply Subtype.ext
    change (x : G) = 1
    have := congrArg (fun a => g * a * g⁻¹) he
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_one,
      mul_inv_cancel] using this
  have hinv (u : G) (hu : IsConj z u) :
      ∀ x : N, (MulAut.conjNormal u : MulAut N) x = x⁻¹ := by
    apply congrFun
    apply (hfp u hu).coe_eq_inv_of_involutive
    have hu2 : u ^ 2 = 1 := by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hu
      change (MulAut.conj g z) ^ 2 = 1
      rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
    intro x
    apply Subtype.ext
    change u * (u * (x : G) * u⁻¹) * u⁻¹ = x
    calc
      _ = (u * u) * (x : G) * (u * u)⁻¹ := by group
      _ = x := by rw [← pow_two, hu2]; simp
  apply (eq_bot_iff_forall N).mpr
  intro x hx
  let a : N := ⟨x, hx⟩
  have ha : (MulAut.conjNormal (z * t) : MulAut N) a = a := by
    rw [map_mul, MulAut.mul_apply, hinv t ht, map_inv, hinv z (IsConj.refl z), inv_inv]
  exact congrArg Subtype.val (hfp (z * t) hzt a ha)


/-- Three fused involutions with a two-group centralizer kill the odd core. -/
public theorem pPrimeCore_eq_bot_of_fused_involutions
    {G : Type*} [Group G] [Finite G] (z t : G) (hz : orderOf z = 2)
    (ht : IsConj z t) (hzt : IsConj z (z * t))
    (hC : IsPGroup 2 (centralizer ({z} : Set G))) : pPrimeCore 2 G = ⊥ := by
  apply normal_eq_bot_of_fused_triple z t hz ht hzt
  obtain ⟨n, hn⟩ := hC.exists_card_eq
  have hd : Disjoint (pPrimeCore 2 G) (centralizer ({z} : Set G)) :=
    disjoint_of_coprime_natCard (by
      rw [hn]
      exact (pPrimeCore_coprime_card (p := 2) (G := G)).symm.pow_right n)
  intro x hx hxc
  exact hd.le_bot ⟨hx, hxc⟩

end Subgroup
