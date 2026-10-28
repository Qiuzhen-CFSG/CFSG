module

public import Theory.Representation.BinaryOffender.MovedDimension
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A five-product obstruction to binary moved lines

Two conjugate actors with one-dimensional moved spaces have all their
displacements in a space of dimension at most two. Every orbit of their
order-five product lies in a translate of that space, hence has at most
four points. Faithfulness forbids this: a nontrivial orbit has five points.
The affine-orbit argument controls the whole module, including its fixed
directions, without assuming that restriction to the moved sum is faithful.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] (ρ : Representation (ZMod 2) G V)

private theorem five_le_card_of_displacements
    (hf : Function.Injective ρ) (a : G) (ha : orderOf a = 5)
    (W : Submodule (ZMod 2) V)
    (hW : ∀ g ∈ zpowers a, ∀ v : V, ρ g v - v ∈ W) :
    5 ≤ Nat.card W := by
  classical
  let A := zpowers a
  let : MulAction A V := MulAction.compHom V (ρ.comp A.subtype)
  have hA : Nat.card A = 5 := by simp [A, Nat.card_zpowers, ha]
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; decide)
  have ha1 : a ≠ 1 := by intro h; simp [h] at ha
  obtain ⟨v,hv⟩ : ∃ v : V, ρ a v ≠ v := by
    by_contra! h
    apply ha1
    apply hf
    ext w
    simpa using h w
  let f : MulAction.orbit A v → W := fun w => ⟨w.val-v, by
    obtain ⟨g,hg⟩ := w.property
    rw [←hg]
    exact hW g g.property v⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact sub_left_injective (congrArg Subtype.val h)
  have hbound := Nat.card_le_card_of_injective f hi
  have hdvd : Nat.card (MulAction.orbit A v) ∣ 5 := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer A v), ← hA]
    exact (MulAction.stabilizer A v).index_dvd_card
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdvd with hone | hfive
  · let := Fintype.ofFinite (MulAction.orbit A v)
    have hfix : v ∈ MulAction.fixedPoints A V :=
      MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr
        (by simpa only [Nat.card_eq_fintype_card] using hone)
    exact (hv (hfix ⟨a,mem_zpowers a⟩)).elim
  · exact hfive ▸ hbound

/-- If an actor and one of its conjugates have product of order five, its
binary moved space cannot be a line. The acting subgroup is retained. -/
theorem four_le_card_subspaceCommutator_of_conjugate_five
    (hf : Function.Injective ρ) (E : Subgroup G)
    (t : G) (ht : t ∈ E) (g : G)
    (hfive : orderOf (t * (g * t * g⁻¹)) = 5) :
    4 ≤ Nat.card (subspaceCommutator ρ ⊤ E) := by
  classical
  by_contra hn
  let U := subspaceCommutator ρ ⊤ E
  let E' := E.map (MulAut.conj g).toMonoidHom
  let U' := subspaceCommutator ρ ⊤ E'
  let W := U ⊔ U'
  have hdim : Module.finrank (ZMod 2) U ≤ 1 := by
    have hc : 2 ^ Module.finrank (ZMod 2) U < 4 := by
      have hcU : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
        simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U))
      rw [←hcU]
      exact Nat.lt_of_not_ge hn
    by_contra h
    have hb := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) U by omega)
    norm_num at hb
    omega
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  have he : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) U' := by
    apply moved_finrank_equivariant ρ ρ (MulAut.conj g).toMonoidHom e ?_ E
    intro x v
    change ρ g (ρ x v) = ρ (g*x*g⁻¹) (ρ g v)
    simp only [←Module.End.mul_apply, ←map_mul]
    congr 2
    group
  have hWdim : Module.finrank (ZMod 2) W ≤ 2 := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq U U'
    dsimp only [W]
    omega
  have hWcard : Nat.card W ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hWdim).trans_eq (by norm_num)
  let K : Subgroup G := {
    carrier := {a | ∀ v : V, ρ a v-v ∈ W}
    one_mem' := by
      intro v
      rw [map_one, Module.End.one_apply, sub_self]
      exact W.zero_mem
    mul_mem' := by
      intro a b ha hb v
      have hh := W.add_mem (ha (ρ b v)) (hb v)
      simpa only [map_mul,Module.End.mul_apply,sub_add_sub_cancel] using hh
    inv_mem' := by
      intro a ha v
      have hh := W.neg_mem (ha (ρ a⁻¹ v))
      simpa only [ρ.self_inv_apply,neg_sub] using hh }
  have hE : E ≤ K := by
    intro a ha v
    exact (le_sup_left : U ≤ W) (Submodule.subset_span
      ⟨a,ha,v,Submodule.mem_top,rfl⟩)
  have hE' : E' ≤ K := by
    intro a ha v
    exact (le_sup_right : U' ≤ W) (Submodule.subset_span
      ⟨a,ha,v,Submodule.mem_top,rfl⟩)
  have hconj : g*t*g⁻¹ ∈ E' := mem_map_of_mem (MulAut.conj g).toMonoidHom ht
  have ha : t*(g*t*g⁻¹) ∈ K := K.mul_mem (hE ht) (hE' hconj)
  have hlarge := five_le_card_of_displacements ρ hf _ hfive W
    (fun a ha => (zpowers_le.mpr ‹t*(g*t*g⁻¹) ∈ K›) ha)
  omega

end Representation.BinaryOffender
