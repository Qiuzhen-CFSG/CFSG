module
public import Theory.SpecificGroups.PSL2.PrimePerfectCentralizer
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# Centralizer comparison inside a normalized prime-field component

A nontrivial perfect subgroup of a prime-field PSL₂ model determines its
centralizer among all elements normalizing the model. Applying this to two
nested relative components makes the larger component centralize the original
actor; component maximality then identifies the two components.
Source: Aschbacher--Smith A.3.12(8), used in 12.4.8, printed p.815.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2
variable {G : Type*} [Group G]

theorem centralizer_inf_normalizer_le_of_perfect
    (D K : Subgroup G) [Group.IsPerfect K] (hK : K ≠ ⊥) (hKD : K ≤ D)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {F : Type} [Field F] [Finite F] (hcard : Nat.card F = p)
    (eD : D ≃* PSL(2,F)) :
    centralizer (K : Set G) ⊓ normalizer (D : Set G) ≤ centralizer (D : Set G) := by
  let N := normalizer (D : Set G)
  let D' := D.subgroupOf N
  let K' := K.subgroupOf N
  have hKN : K ≤ N := hKD.trans D.le_normalizer
  let : Group.IsPerfect K' := Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKN).symm.toMonoidHom) (subgroupOfEquivOfLe hKN).symm.surjective
  have hK' : K' ≠ ⊥ := by
    intro he
    apply hK
    have hm := congrArg (Subgroup.map N.subtype) he
    simpa only [K',map_subgroupOf_eq_of_le hKN,Subgroup.map_bot] using hm
  have hc := centralizer_eq_of_perfect_in_prime_component D' K' hK'
    (by intro x hx; exact hKD hx) hp hcard
    ((subgroupOfEquivOfLe D.le_normalizer).trans eD)
  intro a ha d hd
  have ha' : (⟨a,ha.2⟩ : N) ∈ centralizer (K' : Set N) := by
    intro k hk
    exact Subtype.ext (ha.1 k hk)
  rw [hc] at ha'
  exact congrArg Subtype.val (ha' ⟨d,D.le_normalizer hd⟩ hd)

/-- Two nested components coincide when the larger prime-field component is
normalized by the actor centralized by the smaller one. -/
theorem component_eq_of_normalized_prime_model
    {A B K D : Subgroup G} (hBA : B ≤ A)
    (hK : IsComponentIn K (centralizer (A : Set G)))
    (hD : IsComponentIn D (centralizer (B : Set G)))
    (hKD : K ≤ D) (hAN : A ≤ normalizer (D : Set G))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {F : Type} [Field F] [Finite F] (hcard : Nat.card F = p)
    (eD : D ≃* PSL(2,F)) : K = D := by
  let := hK.quasisimple
  have hAD : A ≤ centralizer (D : Set G) := by
    apply le_trans _ (centralizer_inf_normalizer_le_of_perfect D K hK.ne_bot hKD hp hcard eD)
    exact le_inf (le_centralizer_iff.mp hK.1) hAN
  have hD' := hD.restrict (le_centralizer_iff.mp hAD) (centralizer_le hBA)
  have he := hK.2.eq_of_le hD'.2 (by intro x hx; exact hKD hx)
  have hm := congrArg (Subgroup.map (centralizer (A : Set G)).subtype) he
  simpa only [map_subgroupOf_eq_of_le hK.1,map_subgroupOf_eq_of_le hD'.1] using hm
end Theory.PSL2
