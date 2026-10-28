module

public import Theory.GroupTheory.MarkedInnerStrongClosure.ReturningConjugates
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization

/-!
# Marked quotient obstructions for the actual Bender component

Restrict the original Sylow of H to its component L. The source O(H)=1
makes Z(L)=O₂(L), so an actual model of L/O₂(L) gives a central two-quotient
without any bound on its kernel. The original distinguished involution has
a nontrivial inner implementer modulo that kernel, since L is not contained
in M. A noncommuting pair of returning conjugates of its marked image is
incompatible with the abelian strong closure of U.

The model pair remains explicit in this adapter; each family consumer must
prove it internally. No involutory lift or multiplier calculation is used.

Source: Aschbacher--Smith 1.1.5(3), pp.501--503, and Proposition 2.2.2,
pp.519--520 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

private theorem false_of_marked_central_two_quotient_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    {Q : Type*} [Group Q] [Finite Q]
    (q : L →* Q) (hq : Function.Surjective q)
    (hker : q.ker = center L) (hker2 : IsPGroup 2 q.ker)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹)
    (hpair : ∀ (R : Sylow 2 Q) (v : Q), v ∈ R → orderOf v = 2 →
      (∀ x ∈ R, Commute v x) →
      ∃ a b : R, IsConj v (a : Q) ∧ IsConj v (b : Q) ∧ ¬Commute a b) : False := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let S' : Subgroup G := (S : Subgroup H).map H.subtype
  have hU : IsStronglyClosedSet (w.U : Set G) S' ⊤ :=
    ⟨hUS, fun x hx g hg hgs => w.strongly_closed.2 x hx g hg (hST hgs)⟩
  obtain ⟨P0, hP0⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) hL.2.1
  let e0 := subgroupOfEquivOfLe hL.1
  let P := P0.mapSurjective (f := e0.toMonoidHom) e0.surjective
  have hPS : (P : Subgroup L).map L.subtype ≤ S' := by
    rintro _ ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    have hxS : (x : H) ∈ (S : Subgroup H) := by
      change x ∈ (S : Subgroup H).subgroupOf (L.subgroupOf H)
      rw [← hP0]
      exact hx
    exact mem_map_of_mem H.subtype hxS
  obtain ⟨t, ht⟩ := hinner
  have htn : q t ≠ 1 := by
    intro he
    have htc : t ∈ center L := hker ▸ (show t ∈ q.ker from he)
    apply hLM
    intro x hx
    apply w.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have htx : t * (⟨x, hx⟩ : L) * t⁻¹ = ⟨x, hx⟩ := by
      rw [← mem_center_iff.mp htc ⟨x, hx⟩]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    have hh := ht ⟨x, hx⟩
    rw [htx] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  exact MarkedInnerStrongClosure.false_of_central_two_quotient_returning_pair
    S' w.U hU L.subtype L.subtype_injective P hPS q hq hker hker2
    w.z w.z_mem (w.z_order ▸ pow_orderOf_eq_one w.z)
    (fun s hs => w.z_central s (hST hs)) t htn ht hpair

/-- An internally proved marked-class obstruction in the literal L/O₂(L)
model excludes the source component. The source odd-core hypothesis supplies
the central two-kernel, whose order is unrestricted. -/
theorem LocalControlWitness.false_of_marked_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    {Q : Type*} [Group Q] [Finite Q] (e : (L ⧸ pCore 2 L) ≃* Q)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹)
    (hpair : ∀ (R : Sylow 2 Q) (v : Q), v ∈ R → orderOf v = 2 →
      (∀ x ∈ R, Commute v x) →
      ∃ a b : R, IsConj v (a : Q) ∧ IsConj v (b : Q) ∧ ¬Commute a b) : False := by
  let : IsQuasisimple L := hL.quasisimple
  have hlocal : pPrimeCore 2 (L.subgroupOf H) = ⊥ :=
    hL.2.1.pPrimeCore_eq_bot hcore (L.subgroupOf H)
  have hcoreL : pPrimeCore 2 L = ⊥ := by
    have he := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hL.1)
    simpa only [hlocal, Subgroup.map_bot] using he.symm
  have hZ : center L = pCore 2 L := IsQuasisimple.center_eq_pCore hcoreL
  let q : L →* Q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hk : q.ker = pCore 2 L := by
    dsimp only [q]
    exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (pCore 2 L))
      e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  exact false_of_marked_central_two_quotient_model w H S hUS hST L hL hLM
    q (e.surjective.comp (QuotientGroup.mk'_surjective _)) (hk.trans hZ.symm)
    (hk.symm ▸ pCore_isPGroup) hinner hpair

end CFSG.Quasithin.Chapter2.BenderFusion
