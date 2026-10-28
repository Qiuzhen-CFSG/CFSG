module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local
public import Theory.SpecificGroups.PSL3Three.ProperSubgroups
public import Theory.SpecificGroups.PSL3Three.SylowInvolutions
public import Theory.GroupTheory.SolvableSylowInvolutions

/-!
# The PSL₃(3) component intersection

For the genuine local setup and an actual equivalence L ≃ PSL₃(3), an inner
action of z has an involution projection t in L, and L ∩ M = C_L(t).

The supplied Sylow subgroup meets L in a Sylow two-subgroup R containing t
centrally. The proper intersection K = L ∩ M is solvable by the concrete
PSL₃(3) subgroup classification. Relative subnormality in H ∩ M and its
characteristic-two condition make every odd prime core of K trivial.
The unique-involution property of the matrix-model Sylow subgroup then
forces t to be central in K, using the center of O₂(K). Conversely, C_L(t)
is contained in M because t induces the same action on L as z and C_G(z) ≤ M.
Thus the larger parabolic overgroups are excluded by the local conditions;
no ordinary maximality of the involution centralizer is asserted or assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
2.3.9(7)(d), printed pp.525–526, using the inner-action alternative of
1.1.5(3)(e). This module proves precisely the PSL₃(3) branch.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup

variable {G : Type*} [Group G]

private theorem center_eq_bot_of_linearThree {L : Subgroup G}
    (e : L ≃* Matrix.PSL3Three.PSL) : center L = ⊥ := by
  let f := e.trans Matrix.PSL3Three.equiv.symm
  apply le_bot_iff.mp
  intro x hx
  have he : f x ∈ center Matrix.PSL3Three.SL := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := f.surjective y
    simpa using congrArg f (mem_center_iff.mp hx a)
  rw [Matrix.PSL3Three.center_eq_bot, mem_bot] at he
  exact f.injective (he.trans (map_one f).symm)

private def intersectionEquiv (L M : Subgroup G) : M.subgroupOf L ≃* ↥(L ⊓ M) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- In the PSL₃(3) case, the component meets M in the centralizer of the
involution projecting the genuine inner action of z. -/
theorem linearThree_intersection
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* Matrix.PSL3Three.PSL)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃ t : L, orderOf t = 2 ∧ IsConjugationProjection L z t ∧
      L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G) := by
  let := h.finite
  obtain ⟨t, ht, _⟩ := h.exists_unique_projection (center_eq_bot_of_linearThree e) α hα hinner
  obtain ⟨R, hR⟩ := h.component_sylow
  have htc := h.projection_centralizes_sylow ht.1 R hR
  have htR := h.projection_mem_sylow ht.1 ht.2 R hR
  let K := M.subgroupOf L
  have hRK : (R : Subgroup L) ≤ K := by
    intro x hx
    apply h.sylow_le
    change x ∈ ((S : Subgroup H).map H.subtype).subgroupOf L
    rwa [← hR]
  have hproper : K ≠ ⊤ := fun he => h.outside (subgroupOf_eq_top.mp he)
  have hproperImage : K.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hproper
    apply e.mapSubgroup.injective
    simpa using he
  let : Group.IsSolvable (K.map e.toMonoidHom) :=
    Matrix.PSL3Three.isSolvable_of_ne_top _ hproperImage
  let f : K ≃* (K.map e.toMonoidHom) := MulEquiv.subgroupMap e K
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := f.toMonoidHom) f.injective
  let P := R.subtype hRK
  let q : P ≃* R := Subgroup.subgroupOfEquivOfLe hRK
  have hunique : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      (∀ s : P, Commute x (s * x * s⁻¹)) →
      (∀ s : P, Commute y (s * y * s⁻¹)) → x = y := by
    intro x y hx hy hxc hyc
    apply q.injective
    apply Matrix.PSL3Three.sylow_involution_eq_of_commuting_conjugates e R
    · simpa using hx
    · simpa using hy
    · intro s
      simpa using (hxc (q.symm s)).map q.toMonoidHom
    · intro s
      simpa using (hyc (q.symm s)).map q.toMonoidHom
  have hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → pCore p K = ⊥ := by
    intro p hp hp2
    let : Fact p.Prime := ⟨hp⟩
    have he := pCore_map_iso p (intersectionEquiv L M)
    rw [h.intersection_odd_core_eq_bot p hp2] at he
    exact (Subgroup.map_eq_bot_iff_of_injective _ (intersectionEquiv L M).injective).mp he
  let tk : K := ⟨t, hRK htR⟩
  let tp : P := ⟨tk, htR⟩
  have htp : orderOf tp = 2 :=
    (Subgroup.orderOf_coe tp).symm.trans ((Subgroup.orderOf_coe tk).symm.trans ht.2)
  have htpc : tp ∈ center P := by
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_iff.mp htc _ s.property
  have hcentral := Theory.GroupTheory.central_of_sylow_involution_uniqueness
    P hunique hodd tp htp htpc
  refine ⟨t, ht.2, ht.1, le_antisymm ?_
    (projection_centralizer_le_intersection ht.1 h.centralizer_le)⟩
  rintro x ⟨hxL, hxM⟩
  refine ⟨hxL, mem_centralizer_singleton_iff.mpr ?_⟩
  exact congrArg (fun y : K => ((y : L) : G))
    (mem_center_iff.mp hcentral (⟨⟨x, hxL⟩, hxM⟩ : K))

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
