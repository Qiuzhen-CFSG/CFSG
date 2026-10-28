module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SelfCentralizingCoreSubnormal
public import CFSG.Quasithin.Chapter1.Section01

/-!
# Sylow subgroups and the projected involution in a component

In Aschbacher–Smith 2.3.9(7), S meets L in a Sylow two-subgroup because
L is subnormal in H. The actual conjugation identity then shows that z_L
centralizes this Sylow subgroup. When z_L is an involution it belongs to
that subgroup: a two-element normalizing a Sylow two-subgroup lies in it.
Thus the projected action is genuinely two-central, with the original S
retained. The intersection L ∩ M is subnormal in H ∩ M, so the latter's
characteristic-two condition also rules out all odd prime cores of L ∩ M.
No ambient normality of L is assumed.

Source: combined manuscript of 1 March 2004, 1.1.5(3)(e,f) and
2.3.9(7)(d–f), printed pp.502 and 525–526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup
variable {G : Type*} [Group G]

/-- The supplied Sylow subgroup meets the component in a Sylow subgroup. -/
theorem LocalSetup.component_sylow {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) :
    ∃ R : Sylow 2 L, (R : Subgroup L) =
      ((S : Subgroup H).map H.subtype).subgroupOf L := by
  let := h.finite
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) h.component.1
  let e := Subgroup.subgroupOfEquivOfLe h.component_le
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (T : Subgroup (L.subgroupOf H)).map e.toMonoidHom = _
  rw [hT]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : H), hy, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    refine ⟨⟨y, ?_⟩, hy, ?_⟩
    · change (y : G) ∈ L
      change (y : G) = (x : G) at hxy
      exact hxy.symm ▸ x.property
    · exact Subtype.ext hxy

/-- The actual automorphism induced by z fixes the component Sylow subgroup
pointwise. This formulation also applies before a central cover is eliminated. -/
theorem LocalSetup.action_fixes_component_sylow
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (R : Sylow 2 L)
    (hR : (R : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L) :
    ∀ x ∈ (R : Subgroup L), α x = x := by
  intro x hx
  have hxs : (x : G) ∈ (S : Subgroup H).map H.subtype := by
    change x ∈ ((S : Subgroup H).map H.subtype).subgroupOf L
    rwa [← hR]
  apply Subtype.ext
  rw [hα, ← h.central x hxs, mul_inv_cancel_right]

/-- The literal projection centralizes the supplied component Sylow subgroup. -/
theorem LocalSetup.projection_centralizes_sylow
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) {t : L} (ht : IsConjugationProjection L z t)
    (R : Sylow 2 L)
    (hR : (R : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L) :
    t ∈ centralizer (R : Set L) := by
  apply mem_centralizer_iff.mpr
  intro x hx
  have hxs : (x : G) ∈ (S : Subgroup H).map H.subtype := by
    change x ∈ ((S : Subgroup H).map H.subtype).subgroupOf L
    rwa [← hR]
  apply Subtype.ext
  have he := ht x
  change z * (x : G) * z⁻¹ = (t : G) * (x : G) * (t : G)⁻¹ at he
  rw [← h.central x hxs, mul_inv_cancel_right] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

/-- An involution projection belongs to that Sylow subgroup, so it is two-central. -/
theorem LocalSetup.projection_mem_sylow
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) {t : L} (ht : IsConjugationProjection L z t)
    (ht2 : orderOf t = 2) (R : Sylow 2 L)
    (hR : (R : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L) :
    t ∈ (R : Subgroup L) := by
  let := h.finite
  have hp : IsPGroup 2 (zpowers t) := by
    apply (IsPGroup.iff_card).mpr
    exact ⟨1, by simpa using ht2⟩
  have hc := h.projection_centralizes_sylow ht R hR
  have hm : t ∈ zpowers t ⊓ normalizer (R : Set L) :=
    ⟨mem_zpowers t, centralizer_le_normalizer _ hc⟩
  rw [hp.inf_normalizer_sylow R] at hm
  exact hm.2

/-- The component intersection is subnormal in the local intersection H ∩ M. -/
theorem LocalSetup.intersection_subnormal
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) :
    ((L ⊓ M).subgroupOf (H ⊓ M)).IsSubnormal := by
  let f : ↥(H ⊓ M) →* H := Subgroup.inclusion inf_le_left
  have hs := h.component.1.comap f
  have he : (L.subgroupOf H).comap f = (L ⊓ M).subgroupOf (H ⊓ M) := by
    ext x
    change (x : G) ∈ L ↔ (x : G) ∈ L ∧ (x : G) ∈ M
    exact (and_iff_left x.property.2).symm
  rwa [he] at hs

/-- No odd prime core survives in L ∩ M. This uses relative subnormality
and the supplied characteristic-two condition on H ∩ M. -/
theorem LocalSetup.intersection_odd_core_eq_bot
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    pCore p ↥(L ⊓ M) = ⊥ := by
  let := h.finite
  have hc := Chapter1.mem_He_iff.mp h.local_even
  have hz := subnormal_pCore_eq_bot_of_other_selfCentralizingCore 2 p hp hc
    ((L ⊓ M).subgroupOf (H ⊓ M)) h.intersection_subnormal
  let e := Subgroup.subgroupOfEquivOfLe
    (inf_le_inf_right M h.component_le : L ⊓ M ≤ H ⊓ M)
  have he := pCore_map_iso p e
  rw [hz, Subgroup.map_bot] at he
  exact he.symm

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
