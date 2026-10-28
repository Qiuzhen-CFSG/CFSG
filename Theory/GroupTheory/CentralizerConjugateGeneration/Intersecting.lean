module

public import Theory.GroupTheory.CentralizerConjugateGeneration

/-!
# Commuting intersecting conjugates from a transitive seed

If the normalizer is transitive on the nonidentity elements of V, an
abelian span of its C_G(z)-conjugates makes every pair of intersecting
conjugates commute. Move an intersection point to z, apply the centralizer
transporter, and conjugate the resulting commutator back.

Source: Aschbacher--Smith, A.1.7(1) and the paragraph after 5.1.23,
printed p.646 of `refs/quasithin.pdf`.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

theorem intersecting_conjugates_commute_of_transitive_centralizer_span
    (V : Subgroup G) {z : G} (hzV : z ∈ V) (hz : z ≠ 1)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ n ∈ normalizer (V : Set G),
      (MulAut.conj n) z = x)
    [IsMulCommutative (centralizerConjugateClosure V z)]
    (g : G) (hi : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨x, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hi
  obtain ⟨n, hn, he⟩ := htrans x x.property.1 (fun hh => hne (Subtype.ext hh))
  have hng : z ∈ V.map (MulAut.conj (n⁻¹ * g)).toMonoidHom := by
    obtain ⟨v, hv, hvx⟩ := x.property.2
    refine ⟨v, hv, ?_⟩
    apply (MulAut.conj n).injective
    rw [he]
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, mul_inv_rev, mul_assoc, mul_inv_cancel_left,
      inv_mul_cancel_left, inv_inv, mul_inv_cancel, mul_one] using hvx
  have hcomm := commutator_eq_bot_of_abelian_centralizerConjugateClosure V hz htrans
    (g := 1) (by simpa using hzV) hng
  have hmap : V.map (MulAut.conj n).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have hidentity : V.map (MulAut.conj (1 : G)).toMonoidHom = V := by
    ext x
    simp [Subgroup.mem_map]
  rw [hidentity] at hcomm
  have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj n).toMonoidHom) hcomm
  rw [map_commutator, hmap, map_map, map_bot] at hh
  have hcomp : (MulAut.conj n).toMonoidHom.comp
      (MulAut.conj (n⁻¹ * g)).toMonoidHom = (MulAut.conj g).toMonoidHom := by
    ext v
    simp [MulAut.conj_apply, mul_assoc]
  rwa [hcomp] at hh

end Subgroup
