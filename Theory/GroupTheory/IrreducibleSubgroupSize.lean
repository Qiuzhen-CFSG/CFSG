module
public import Theory.GroupAction.PrimitivePrimeTI
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.GroupTheory.SubgroupProductCard

/-!
# Large irreducible subgroups inside normalized prime groups

An irreducible subgroup E is TI under the normalizer of its actor B.
If E lies in U and |U| < |E|², the subgroup product formula rules out
trivial intersection with any U-conjugate. Thus U normalizes E. When U
is a prime group normalized by B, the normal prime-core lemma makes U
centralize E. The image transport retains the actual homomorphism.

Application: the small Mathieu pushing-up cases in Aschbacher–Smith
4.2.13 and 4.4.14, printed pp.611–612 and 624–625.
-/

public noncomputable section

open scoped Pointwise
namespace Subgroup

/-- An invariant-subgroup dichotomy descends through the actual image map. -/
theorem invariant_subgroup_dichotomy_map
    {G H : Type*} [Group G] [Group H] (f : G →* H) (E B : Subgroup G)
    (hBE : B ≤ normalizer (E : Set G))
    (hirr : ∀ X : Subgroup G, X ≤ E → B ≤ normalizer (X : Set G) → X = ⊥ ∨ X = E)
    (X : Subgroup H) (hXE : X ≤ E.map f) (hBX : B.map f ≤ normalizer (X : Set H)) :
    X = ⊥ ∨ X = E.map f := by
  let Y := E ⊓ X.comap f
  have hBY : B ≤ normalizer (Y : Set G) :=
    (le_inf hBE ((map_le_iff_le_comap.mp hBX).trans (X.le_normalizer_comap f))).trans
      inf_normalizer_le_normalizer_inf
  have he : Y.map f = X := by
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨y,hy,he⟩ := hXE hx
      exact ⟨y,⟨hy,show f y ∈ X from he.symm ▸ hx⟩,he⟩
  rcases hirr Y inf_le_left hBY with hy | hy
  · exact Or.inl (by rw [←he,hy,map_bot])
  · exact Or.inr (by rw [←he,hy])

/-- A large irreducible subgroup cannot have a disjoint conjugate inside U. -/
theorem le_normalizer_of_large_irreducible
    {G : Type*} [Group G] [Finite G] (E B U : Subgroup G)
    (hEU : E ≤ U) (hBE : B ≤ normalizer (E : Set G))
    (hUB : U ≤ normalizer (B : Set G))
    (hirr : ∀ X : Subgroup G, X ≤ E → B ≤ normalizer (X : Set G) → X = ⊥ ∨ X = E)
    (hlarge : Nat.card U < Nat.card E * Nat.card E) :
    U ≤ normalizer (E : Set G) := by
  intro u hu
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply (ti_under_actor_normalizer E B hBE hirr (hUB hu)).resolve_left
  intro hdis
  let Eg := E.map (MulAut.conj u).toMonoidHom
  have hEgU : Eg ≤ U := by
    have hm := map_mono (f := (MulAut.conj u).toMonoidHom) hEU
    exact hm.trans_eq (mem_normalizer_iff_map_conj_eq.mp (U.le_normalizer hu))
  have hprod : (E : Set G) * (Eg : Set G) ⊆ U := by
    rintro x ⟨a,ha,b,hb,rfl⟩
    exact U.mul_mem (hEU ha) (hEgU hb)
  have hcount := card_set_mul_mul_card_inf E Eg
  rw [hdis,card_bot,mul_one,card_map_of_injective (MulAut.conj u).injective] at hcount
  have hle : Nat.card ((E : Set G) * (Eg : Set G)) ≤ Nat.card U :=
    Nat.card_le_card_of_injective (Set.inclusion hprod) (Set.inclusion_injective hprod)
  exact (not_lt_of_ge (hcount ▸ hle)) hlarge

/-- The normalized p-group centralizes its large irreducible subgroup. -/
theorem le_centralizer_of_large_irreducible
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (E B U : Subgroup G) (hp : IsPGroup p U)
    (hEU : E ≤ U) (hBE : B ≤ normalizer (E : Set G))
    (hBU : B ≤ normalizer (U : Set G)) (hUB : U ≤ normalizer (B : Set G))
    (hirr : ∀ X : Subgroup G, X ≤ E → B ≤ normalizer (X : Set G) → X = ⊥ ∨ X = E)
    (hlarge : Nat.card U < Nat.card E * Nat.card E) :
    U ≤ centralizer (E : Set G) := by
  have hUE := le_normalizer_of_large_irreducible E B U hEU hBE hUB hirr hlarge
  have hcore := pCoreIn_le_centralizer_of_irreducible E B (B ⊔ U)
    (hp.of_injective (inclusion hEU) (inclusion_injective hEU)) (hEU.trans le_sup_right) (sup_le hBE hUE) le_sup_left hirr
  exact (le_pCoreIn_of_normalizes hp le_sup_right (sup_le hBU U.le_normalizer)).trans hcore
end Subgroup
