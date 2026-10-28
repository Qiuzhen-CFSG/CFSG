module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SylowPointwiseInner
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Marking Sylow-central actors in nonbinary symplectic components

If a faithful normal subgroup is Sp₄(2ⁿ), n > 1, every ambient element
centralizing a Sylow two-subgroup belongs to that normal subgroup. Restrict
the Sylow subgroup to the component, transport to the matrix group, and
combine the proved pointwise-Sylow calculation with the proved semilinear
classification. Thus no innerness or root-type hypothesis is required.

The central quotient comparison is induced by the actual quotient map:
the even symplectic center is trivial by its transvection calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21, printed p.924, and the Sylow-pointwise assertion in 16.1.6,
printed p.1172. The separate binary derived group is outside this statement.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace Theory.SpecificGroups.SymplecticFour.SylowCentralMarking

variable {F : Type*} [Field F] [CharP F 2]

/-- Pointwise Sylow centrality places the actor in the actual faithful normal component. -/
theorem centralizes_sylow_mem_component [Finite F]
    {A : Type*} [Group A] [Finite A]
    (N : Subgroup A) [N.Normal] (hc : centralizer (N : Set A) = ⊥)
    (e : N ≃* Sp F) {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 A) {v : A} (hv : v ∈ centralizer (S : Set A)) : v ∈ N := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal N
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let a := MulAut.congr e (MulAut.conjNormal (H := N) v)
  have hfix : ∀ x ∈ (Q : Subgroup (Sp F)), a x = x := by
    rintro _ ⟨x, hx, rfl⟩
    change e (MulAut.conjNormal v (e.symm (e x))) = e x
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    have hxS : (x : A) ∈ (S : Subgroup A) := by
      change x ∈ (S : Subgroup A).subgroupOf N
      rwa [← hP]
    have he := mem_centralizer_iff.mp hv x hxS
    change v * (x : A) * v⁻¹ = x
    rw [← he, mul_inv_cancel_right]
  obtain ⟨g, _, hg⟩ := aut_fixing_sylow_inner hF hn
    SemilinearClassification.inner_field_of_preservesDiagram Q a hfix
  obtain ⟨k, hk⟩ := (MulAut.congr_inner_iff e (MulAut.conjNormal v)).mp ⟨g, hg⟩
  have hm : v ∈ (MulAut.innerSubgroup N).comap MulAut.conjNormal := ⟨k, hk.symm⟩
  simpa only [MulAut.conjNormal_comap_innerSubgroup, hc, sup_bot_eq] using hm

/-- A group actually isomorphic to the even symplectic matrix group has trivial center. -/
theorem center_eq_bot_of_equiv {E : Type*} [Group E] (L : Subgroup E)
    (e : L ≃* Sp F) : center L = ⊥ := by
  apply bot_unique
  intro l hl
  have hm := ((centerCongr e) ⟨l, hl⟩).property
  change e l ∈ center (Sp F) at hm
  rw [EvenProjective.center_eq_bot, mem_bot] at hm
  exact e.injective (by simpa using hm)

/-- The equivalence is induced by the literal quotient map; its reduction is part of this API. -/
@[expose] noncomputable def centralQuotientEquiv {E : Type*} [Group E] (L : Subgroup E)
    (e : L ≃* Sp F) : (L ⧸ center L) ≃* Sp F :=
  ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_equiv L e)).trans
    QuotientGroup.quotientBot).trans e

@[simp] theorem centralQuotientEquiv_mk {E : Type*} [Group E] (L : Subgroup E)
    (e : L ≃* Sp F) (l : L) :
    centralQuotientEquiv L e (QuotientGroup.mk' (center L) l) = e l := rfl

end Theory.SpecificGroups.SymplecticFour.SylowCentralMarking
