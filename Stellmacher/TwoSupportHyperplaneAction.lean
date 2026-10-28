module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.Defs
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic

/-!
# Fourth powers in a two-support hyperplane stabilizer

Two disjoint order-four supports span a group of order sixteen. A subgroup
of order eight containing neither support meets each in a subgroup of order
two. Squaring an actor that permutes the supports makes it preserve both
supports, their intersections with the hyperplane, and the complements of
those intersections. Each of these parts has two elements, so its injective
action has square equal to the identity. The fourth power therefore fixes
both supports and hence the whole group; faithfulness makes it trivial.

This is the intrinsic finite-action calculation for the final R₀,C₀ paragraph
of Stellmacher (9.3), journal p.50/PDF p.40. It uses neither a coordinate
classification nor Sylow or canonical one-seven hypotheses.
-/

open scoped IsMulCommutative

namespace Stellmacher
universe u

private theorem injective_square_eq_of_card_two
    {α : Type*} (hcard : Nat.card α = 2) (f : α → α)
    (hinj : Function.Injective f) (point : α) : f (f point) = point := by
  obtain ⟨other, hother, hunique⟩ := (Nat.card_eq_two_iff' point).mp hcard
  by_cases hfix : f point = point
  · rw [hfix, hfix]
  by_contra hne
  exact hfix (hinj ((hunique _ hne).trans (hunique _ hfix).symm))

private theorem injective_square_eq_of_two_parts
    {α : Type*} [Finite α] (hcard : Nat.card α = 4)
    (predicate : α → Prop) (hpart : Nat.card {point // predicate point} = 2)
    (f : α → α) (hinj : Function.Injective f)
    (hpres : ∀ point, predicate point ↔ predicate (f point))
    (point : α) : f (f point) = point := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite {point // predicate point}
  let := Fintype.ofFinite {point // ¬ predicate point}
  have hcompl : Nat.card {point // ¬ predicate point} = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [← Nat.card_eq_fintype_card, hcard, hpart]
  by_cases hpoint : predicate point
  · let restricted : {point // predicate point} → {point // predicate point} :=
      fun point => ⟨f point, (hpres point).mp point.property⟩
    have hrestricted : Function.Injective restricted := by
      intro left right heq
      exact Subtype.ext (hinj (congrArg Subtype.val heq))
    exact congrArg Subtype.val
      (injective_square_eq_of_card_two hpart restricted hrestricted ⟨point, hpoint⟩)
  · let restricted : {point // ¬ predicate point} → {point // ¬ predicate point} :=
      fun point => ⟨f point, fun hmem => point.property ((hpres point).mpr hmem)⟩
    have hrestricted : Function.Injective restricted := by
      intro left right heq
      exact Subtype.ext (hinj (congrArg Subtype.val heq))
    exact congrArg Subtype.val
      (injective_square_eq_of_card_two hcompl restricted hrestricted ⟨point, hpoint⟩)

private theorem support_hyperplane_inf_card
    {V : Type u} [Group V] [Finite V] [IsMulCommutative V]
    (H U : Subgroup V) (hV : Nat.card V = 16)
    (hH : Nat.card H = 8) (hU : Nat.card U = 4)
    (hnot : ¬ U ≤ H) : Nat.card (U ⊓ H : Subgroup V) = 2 := by
  have hbound : Nat.card (H ⊔ U : Subgroup V) ≤ 16 := by
    simpa [hV] using (Nat.card_le_card_of_injective _ (H ⊔ U).subtype_injective)
  have hlarge : 8 < Nat.card (H ⊔ U : Subgroup V) := by
    by_contra hn
    have heq : H = H ⊔ U := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    exact hnot (heq ▸ le_sup_right)
  obtain ⟨multiple, heq⟩ := Subgroup.card_dvd_of_le (show H ≤ H ⊔ U from le_sup_left)
  rw [hH] at heq
  have hsup : Nat.card (H ⊔ U : Subgroup V) = 16 := by omega
  have hnorm : U ≤ Subgroup.normalizer (H : Set V) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes H U hnorm
  rw [hH, hU, hsup, inf_comm H U] at hprod
  omega

private theorem support_preserving_square_fixes
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V]
    (U H : Subgroup V) (hU : Nat.card U = 4)
    (hline : Nat.card (U ⊓ H : Subgroup V) = 2)
    (actor : G) (hUstable : ∀ v ∈ U, actor • v ∈ U)
    (hHstable : ∀ v : V, v ∈ H ↔ actor • v ∈ H)
    (v : V) (hv : v ∈ U) : actor ^ 2 • v = v := by
  let lineEquiv : {point : U // (point : V) ∈ H} ≃ (U ⊓ H : Subgroup V) :=
    { toFun := fun point => ⟨point.val.val, point.val.property, point.property⟩
      invFun := fun point => ⟨⟨point.val, point.property.1⟩, point.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hpart : Nat.card {point : U // (point : V) ∈ H} = 2 :=
    (Nat.card_congr lineEquiv).trans hline
  let restricted : U → U := fun point => ⟨actor • (point : V), hUstable point point.property⟩
  have hinj : Function.Injective restricted := by
    intro left right heq
    exact Subtype.ext ((MulAction.injective actor) (congrArg Subtype.val heq))
  have hfix := injective_square_eq_of_two_parts hU (fun point : U => (point : V) ∈ H)
    hpart restricted hinj (fun point => hHstable point) ⟨v, hv⟩
  simpa only [pow_two, mul_smul] using congrArg Subtype.val hfix

public theorem two_support_hyperplane_setwise_pow_four_eq_one
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (U W H : Subgroup V) (hsup : U ⊔ W = ⊤) (hdis : Disjoint U W)
    (hU : Nat.card U = 4) (hW : Nat.card W = 4) (hH : Nat.card H = 8)
    (hnotU : ¬ U ≤ H) (hnotW : ¬ W ≤ H) (actor : G)
    (hsetwise : ∀ v : V, v ∈ H ↔ actor • v ∈ H)
    (hperm : ((∀ v ∈ U, actor • v ∈ U) ∧ (∀ v ∈ W, actor • v ∈ W)) ∨
      ((∀ v ∈ U, actor • v ∈ W) ∧ (∀ v ∈ W, actor • v ∈ U))) :
    actor ^ 4 = 1 := by
  have hV : Nat.card V = 16 := by
    have hnorm : W ≤ Subgroup.normalizer (U : Set V) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hprod := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint U W hnorm hdis
    simpa [hsup, hU, hW] using hprod
  have hlineU := support_hyperplane_inf_card H U hV hH hU hnotU
  have hlineW := support_hyperplane_inf_card H W hV hH hW hnotW
  have hsqU : ∀ v ∈ U, actor ^ 2 • v ∈ U := by
    intro v hv
    rw [pow_two, mul_smul]
    rcases hperm with hp | hp
    · exact hp.1 _ (hp.1 v hv)
    · exact hp.2 _ (hp.1 v hv)
  have hsqW : ∀ v ∈ W, actor ^ 2 • v ∈ W := by
    intro v hv
    rw [pow_two, mul_smul]
    rcases hperm with hp | hp
    · exact hp.2 _ (hp.2 v hv)
    · exact hp.1 _ (hp.2 v hv)
  have hsqH : ∀ v : V, v ∈ H ↔ actor ^ 2 • v ∈ H := by
    intro v
    simpa only [pow_two, mul_smul] using (hsetwise v).trans (hsetwise (actor • v))
  have hfixU : ∀ v ∈ U, actor ^ 4 • v = v := by
    intro v hv
    simpa only [← pow_mul] using
      support_preserving_square_fixes U H hU hlineU (actor ^ 2) hsqU hsqH v hv
  have hfixW : ∀ v ∈ W, actor ^ 4 • v = v := by
    intro v hv
    simpa only [← pow_mul] using
      support_preserving_square_fixes W H hW hlineW (actor ^ 2) hsqW hsqH v hv
  change actor ^ 4 ∈ (⊥ : Subgroup G)
  rw [← hfaith]
  apply (mem_fixingSubgroup_iff (M := G)).mpr
  intro v _
  have hv : v ∈ U ⊔ W := by rw [hsup]; trivial
  obtain ⟨left, hleft, right, hright, rfl⟩ := Subgroup.mem_sup.mp hv
  rw [smul_mul', hfixU left hleft, hfixW right hright]


end Stellmacher
